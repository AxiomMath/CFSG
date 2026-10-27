module

public import CFSG.LocalAnalysis.WeakClosure81.W183FinL34Loc

public section

namespace CFSG.LocalAnalysis.WeakClosure81.W183L34

open CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four

@[expose] def e8Idx : List (List ℕ) :=
  [[0, 1, 2, 3, 4, 9, 11, 17], [0, 1, 2, 3, 5, 6, 16, 18], [0, 1, 2, 3, 7, 8, 10, 19],
   [0, 1, 2, 3, 12, 20, 21, 26], [0, 1, 2, 3, 13, 14, 23, 24], [0, 1, 2, 3, 15, 22, 25, 27]]

@[expose] def e16Idx : List (List ℕ) :=
  [[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 16, 17, 18, 19],
   [0, 1, 2, 3, 12, 13, 14, 15, 20, 21, 22, 23, 24, 25, 26, 27]]

@[expose] def coverW : List (List ℕ) :=
  [[], [2], [1], [1, 2], [0, 1, 0, 0], [0, 2, 0, 0], [0, 1, 2, 0, 0], [1, 0, 1, 0, 1, 0, 0, 1],
   [1, 0, 1, 0, 1, 0, 0, 1, 0, 0]]

@[expose] def pickN (I : List ℕ) : List Nat := I.map fun i => c1N.getD i 0

@[expose] def e8N : List (List Nat) := e8Idx.map pickN

@[expose] def e16N : List (List Nat) := e16Idx.map pickN

@[expose] def q1N : List Nat := e16N.getD 0 []

@[expose] def q2N : List Nat := e16N.getD 1 []

@[expose] def coverN : List Nat := coverW.map wN

@[expose] def invI : List ℕ :=
  (List.range 64).filter fun i =>
    !eqN (c1N.getD i 0) idN && eqN (compN (c1N.getD i 0) (c1N.getD i 0)) idN

@[expose] def invN : List Nat := invI.map fun i => c1N.getD i 0

@[expose] def commM : List (List Bool) := invN.map fun a => invN.map fun b => commN a b

@[expose] def cm (i j : ℕ) : Bool := (commM.getD i []).getD j false

@[expose] def prodM : List (List Nat) := invN.map fun a => invN.map fun b => compN a b

@[expose] def imgs : List (List Nat) := coverN.map fun g => invN.map fun x => compN g x

@[expose] def nCos : List (List (List Nat)) :=
  coverN.map fun g => e8N.map fun N => N.map fun n => compN n g

@[expose] def tripleOK (a b c : ℕ) : Bool :=
  (List.range 9).any fun t => (List.range 6).any fun m =>
    let L := (nCos.getD t []).getD m []
    L.contains ((imgs.getD t []).getD a 0) && L.contains ((imgs.getD t []).getD b 0) &&
      L.contains ((imgs.getD t []).getD c 0)

@[expose] def normalIn (N : List Nat) : Bool :=
  c1N.all fun u => let rhs := N.map fun m => compN m u; N.all fun n => rhs.contains (compN u n)

@[expose] def closedMul (N : List Nat) : Bool :=
  N.all fun a => N.all fun b => N.contains (compN a b)

@[expose] def fixMask (x : Nat) : Nat :=
  (List.range 42).foldl (fun acc i => if getN x i == i then acc ||| (1 <<< i) else acc) 0

@[expose] def blockCount (m lo : Nat) : Nat :=
  ((List.range 21).filter fun i => m.testBit (lo + i)).length

@[expose] def fixOK (m : Nat) : Bool :=
  (blockCount m 0 == 5 && blockCount m 21 == 1) || (blockCount m 0 == 1 && blockCount m 21 == 5)

@[expose] def fixM : List Nat := invN.map fixMask

theorem invI_length : invI.length = 27 := by decide +kernel

theorem e8_normal : e8N.all normalIn = true := by decide +kernel

theorem e8_closed : e8N.all closedMul = true := by decide +kernel

theorem e16_normal : e16N.all normalIn = true := by decide +kernel

theorem q_noncomm :
    q1N.all (fun a => q2N.contains a || q2N.all fun b => q1N.contains b || !commN a b) = true := by
  decide +kernel

theorem core_normalConj : (List.range 27).all (fun i => (List.range 27).all fun j =>
    !(i != j && cm i j) || (List.range 27).all fun k =>
      !(k != i && k != j && cm i k && cm j k) || tripleOK i j k) = true := by
  decide +kernel

theorem fix_triples : (List.range 27).all (fun i => (List.range 27).all fun j =>
    !(i != j && cm i j) || (List.range 27).all fun k =>
      !(k != i && k != j && cm i k && cm j k && (prodM.getD i []).getD j 0 != invN.getD k 0) ||
        fixOK (fixM.getD i 0 &&& fixM.getD j 0 &&& fixM.getD k 0)) = true := by
  decide +kernel

theorem fix_e16 : e16N.all (fun Q => fixOK (Q.foldl (fun m x => m &&& fixMask x) (2 ^ 42 - 1))) =
    true := by
  decide +kernel

end CFSG.LocalAnalysis.WeakClosure81.W183L34

end
