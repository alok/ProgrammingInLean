import Lean
-- This module serves as the root of the `ProgrammingInLean` library.
-- Import modules here that should be built as part of the library.
import Std.Data.HashMap
/- Use Lean's new doc library-/
set_option doc.verso true


/-! # Anagram Finder

Given 2 words, uses a {name (full := Std.HashMap)}`HashMap` to find the anagrams of the first word in the second word.
-/
namespace Anagram

instance [BEq k] [Hashable k] [BEq v]: BEq (Std.HashMap k v) where
  beq map1 map2 := map1.size == map2.size && map1.keys.all (fun k => map2[k]? == map1[k]?)

/-- Very simple implementation of anagram detection.-/
def isAnagram (word1 : String) (word2 : String) : Bool := Id.run do
  let (word1,word2) := (word1.toList, word2.toList)
  let mut map1 := Std.HashMap.emptyWithCapacity word1.length
  let mut map2 := Std.HashMap.emptyWithCapacity word2.length
  for char in word1 do
    let count := map1[char]?
    if let some count := count then
      map1 := map1.insert char (count + 1)
    else
      map1 := map1.insert char 1
  for char in word2 do
    let count := map2[char]?
    if let some count := count then
      map2 := map2.insert char (count + 1)
    else
      map2 := map2.insert char 1
  return map1 == map2

-- def List.toHashSet  [Hashable h] (list : List h)

theorem isAnagram_correct (word1 : String) (word2 : String) : isAnagram word1 word2 = (word1.toList.toHashSet = word2.toList.toHashSet) := by
  example : ¬   isAnagram "a" "aa" := by
    rfl

#eval isAnagram "listen" "silent"


end Anagram


namespace TicTacToe

/--Coordinates in a 2D grid. {lean}`(0, 0)` is the upper left. -/
structure Coords where
  /-- Row number -/
  row : Fin 3
  /-- Column number -/
  col : Fin 3
deriving BEq,Hashable

/-! # Tictactoe Game -/

/-! ## syntax

a tictactoe game is a 3x3 grid of squares, with each square being either empty, or occupied by a player's X or O.
-/

/-- The player who is currently taking their turn -/
inductive Player where
  /-- {name (full := Player.X)}`X` goes first-/
  | X
  /-- {name (full := Player.O)}`O` goes second -/
  | O
deriving Repr,DecidableEq,BEq,Hashable


/-- One board cell. -/
inductive Cell where
  /-- Unoccupied tictactoe cell -/
| Empty
  /-- {name (full := Cell.X)}`X` tictactoe cell -/
  | X
  /-- {name (full := Cell.O)}`O` tictactoe cell -/
  | O
deriving Repr,DecidableEq,BEq,Hashable

instance : Repr Cell where
  reprPrec cell _ := Id.run do
    return match cell with
    | Cell.Empty => "░"
    | Cell.X => "X"
    | Cell.O => "O"


/-- The top markers -/
declare_syntax_cat topBorder
/-- A {lit}`─` marker for the horizontal borders instead of {lit}`-` because comments use {lit}`--` -/
declare_syntax_cat horizontalBorder
/-- One middle row. Where most of the action happens. -/
declare_syntax_cat middleRow
/-- The bottom markers -/
declare_syntax_cat bottomBorder
/-- {name (full := Cell.Empty)}`Empty`, {name (full := Cell.X)}`X`, or {name (full := Cell.O)}`O` -/
declare_syntax_cat cell

@[inherit_doc Lean.Parser.Category.horizontalBorder]
syntax "─" : horizontalBorder

-- there's 5 horizontal borders to make it line up
@[inherit_doc Lean.Parser.Category.topBorder]
syntax (priority := 1000) "\n┌" horizontalBorder horizontalBorder horizontalBorder horizontalBorder horizontalBorder "┐\n" : topBorder
@[inherit_doc Cell.X]
syntax "X" : cell
@[inherit_doc Cell.X]
syntax "O" : cell
@[inherit_doc Cell.Empty]
syntax "░" : cell
@[inherit_doc Lean.Parser.Category.bottomBorder]
syntax "\n└" horizontalBorder horizontalBorder horizontalBorder horizontalBorder horizontalBorder "┘\n" : bottomBorder

@[inherit_doc Lean.Parser.Category.middleRow]
syntax "│" cell "│" cell "│" cell "│\n" : middleRow
/-- The whole board -/
syntax:max topBorder middleRow middleRow middleRow bottomBorder : term

/-- The board is represented as a {lean}`Vector (Vector Cell 3) 3`. Some light dependent typing -/
abbrev TicTacToeBoard := Vector (Vector Cell 3) 3

/-- Hand written instance to show how to use {kw (of := Lean.Parser.Term.doFor)}`for` loops and {name}`Vector`s. -/
instance : Repr TicTacToeBoard where
  reprPrec board _n := Id.run do
    let mut out : String := ""
    /- Note that {name}`Id.run` can put you in mutable mode-/
    let printRow (row : Vector Cell 3) : String := Id.run do
      let mut out : String := ""
      for cell in row do
        out := out.append "│"
        out := out.append ((repr cell).pretty)
      out := out.append "│"
      out := out.append "\n"
      return out
    out := out.append "┌─────┐"
    out := out.append "\n"
    for row in board do
      out := out.append (printRow row)
      -- out := out.append "\n"
    out := out.append "└─────┘"
    out := out.append "\n"
    return out

/-- State needed to construct the game. -/
structure GameState where
  /-- {name (full := GameState.currentPlayer)}`currentPlayer` is the player who is currently taking their turn. -/
  currentPlayer : Player
  /-- {name (full := GameState.board)}`board` is the current state of the board. -/
  board : TicTacToeBoard


/-- Turn our custom {syntaxCat}`cell` syntax into {syntaxCat}`term` (a {name}`Cell`). -/
def termOfCell : Lean.TSyntax `cell → Lean.MacroM (Lean.TSyntax `term)
/- Notice the hover works on `░` and shows its docs. -/
| `(cell| ░) => `(Cell.Empty)
/- Notice the hover works on `X` and shows its docs. -/
| `(cell| X) => `(Cell.X)
/- Notice the hover works on `O` and shows its docs. -/
| `(cell| O) => `(Cell.O)
| _ => Lean.Macro.throwError "unknown cell"

/-- Outputs a {lean}`Vector Cell 3` from a {syntaxCat}`middleRow` syntax node. -/
def termOfMiddleRow : Lean.TSyntax `middleRow → Lean.MacroM (Lean.TSyntax `term)
/- Yes I know this may be a lot to read-/
| `(middleRow| /- ← narrows syntax category -/ │ /- ← The delimiters are {lit}`│` -/ $left:cell  /- ← The left cell -/ │ $middle:cell  /- ← The middle cell -/ │ $right:cell  /- ← The right cell -/ │) =>
      do
        let mut out : Array (Lean.TSyntax `term) := #[]
        out := out.push (← termOfCell left)
        out := out.push (← termOfCell middle)
        out := out.push (← termOfCell right)
        `(#v[$out,*])
| _ => Lean.Macro.throwError "unknown middle row"

/-- Macro rules may be better called {lit}`semantics` to contrast with `syntax`-/
macro_rules
| `($_:topBorder /- we can ignore the top border -/
    $top:middleRow
    $middle:middleRow
    $bottom:middleRow
    $_:bottomBorder /- we can ignore the bottom border -/
    ) =>
      /- Here I deliberately use 3 syntaxes for monadic binding `←` -/
      do
        let top ← termOfMiddleRow top
        let middle ← termOfMiddleRow middle
        -- let bottom ← termOfMiddleRow bottom
        -- We return a `Lean.Syntax` object, hence the antiquotes.
        `(#v[$top, $middle, $(← termOfMiddleRow bottom)])

/--This example board is for testing out new syntax and making sure it looks right. -/
def exampleBoard : TicTacToeBoard :=
  ┌─────┐
  │O│O│X│
  │X│X│O│
  │X│X│O│
  └─────┘

def exampleGame : GameState := {currentPlayer:= Player.X,board:= exampleBoard}
/-- todo this should check game logic more and ensure only valid moves can be added, even with {lean}`Prop`s to go all the way -/
def GameState.step  (oldState : GameState) (coords : Coords) (currPlayer : Player) : GameState :=
  /- Notice here we can drop names before the `.` since it knows what the expected type is from the context. -/
  let newValue := if currPlayer == .X then Cell.X else .O
  let newRow := oldState.board[coords.row].set coords.col newValue
  let newBoard := oldState.board.set coords.row newRow
  {oldState .. with
   board := newBoard}

#eval exampleBoard
#eval  (GameState.mk Player.X exampleBoard).step ⟨0, 0⟩ .X

/-! ## win checking -/

/-- {name}`true` iff some row, column, or diagonal has three equal non-empty cells. Lazy about checking that the board is well formed in the first place, but whatever. That should be in {name}`GameState.step`. -/
def GameState.isWin (state : GameState) : Bool :=
  let b := state.board
  let cell (r c : Fin 3) : Cell := b[r][c]
  let same3 (x y z : Cell) : Bool := x ≠ .Empty && x = y && y = z
  -- rows
  same3 b[0][0] b[0][1] b[0][2] ||
  same3 b[1][0] b[1][1] b[1][2] ||
  same3 b[2][0] b[2][1] b[2][2] ||
  -- columns
  same3 b[0][0] b[1][0] b[2][0] ||
  same3 b[0][1] b[1][1] b[2][1] ||
  same3 b[0][2] b[1][2] b[2][2] ||
  -- diagonals
  same3 b[0][0] b[1][1] b[2][2] ||
  same3 b[0][2] b[1][1] b[2][0]

#eval GameState.isWin exampleGame

/-! ## Game scripting DSL (State monad + macro)

Write small scripts to update a {name}`GameState` using a tiny command language.
-/

/-- Game script monad over {name}`GameState`. -/
abbrev GameM := StateM GameState

/-- Set a specific cell on the board to a {name}`Cell` value. -/
def setCellAt (row col : Fin 3) (value : Cell) : GameM Unit := do
  let s ← get
  let updatedRow := s.board[row].set col value
  let updatedBoard := s.board.set row updatedRow
  set { s with board := updatedBoard }

/-- Toggle the current player. -/
def switchPlayer : GameM Unit := do
  let s ← get
  let next := if s.currentPlayer == .X then Player.O else Player.X
  set { s with currentPlayer := next }

/-- Place the current player's mark at {lean}`(row, col)` and then toggle player. -/
def playAt (row col : Fin 3) : GameM Unit := do
  let s ← get
  let mark := if s.currentPlayer == .X then Cell.X else Cell.O
  let updatedRow := s.board[row].set col mark
  let updatedBoard := s.board.set row updatedRow
  let next := if s.currentPlayer == .X then Player.O else Player.X
  set { s with board := updatedBoard, currentPlayer := next }

/-! ### Syntax for game scripts -/
declare_syntax_cat ttt_cmd
syntax "X" "at" num "," num : ttt_cmd
syntax "O" "at" num "," num : ttt_cmd
syntax "play" num "," num : ttt_cmd
syntax "switch" : ttt_cmd

def termOfTttCmd : Lean.TSyntax `ttt_cmd → Lean.MacroM (Lean.TSyntax `term)
| `(ttt_cmd| X at $r:num , $c:num) =>
    `(TicTacToe.setCellAt ⟨$r, by decide⟩ ⟨$c, by decide⟩ Cell.X)
| `(ttt_cmd| O at $r:num , $c:num) =>
    `(TicTacToe.setCellAt ⟨$r, by decide⟩ ⟨$c, by decide⟩ Cell.O)
| `(ttt_cmd| play $r:num , $c:num) =>
    `(TicTacToe.playAt ⟨$r, by decide⟩ ⟨$c, by decide⟩)
| `(ttt_cmd| switch) => `(TicTacToe.switchPlayer)
| _ => Lean.Macro.throwError "unknown tictactoe command"

syntax "game!" term "doo" ttt_cmd* : term

macro_rules
| `(game! $s doo $cmds:ttt_cmd*) =>
    do
      let cmds' ← Array.mapM termOfTttCmd cmds
      `(let (_, s') := ((do $[$cmds'];* : TicTacToe.GameM Unit).run $s); s')

-- Example: start from `exampleGame`, play two moves and switch
#eval (game! exampleGame do
  play 0, 0
  switch
  X at 2, 2
)
end TicTacToe
