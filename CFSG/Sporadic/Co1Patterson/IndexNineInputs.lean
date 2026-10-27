module

public import CFSG.Sporadic.Co1Patterson.GraphInputs
public import CFSG.Sporadic.Co1Patterson.TwistNativeInputs

public section

namespace CFSG.Sporadic.Co1Patterson.IndexNine

open CFSG.Sporadic.Co1Patterson.Native CFSG.Sporadic.Co1Patterson.TwistNative
open CFSG.Sporadic.Co1Block CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.SmallF2.Native

@[expose] def findCol (h : Rows) (k : Nat) : Nat :=
  let x := mul (mul h (yRow k)) (inv h)
  ((List.range 256).find? fun c => x == yprodRow c || x == mul (yprodRow c) iotaARows).getD 0

@[expose] def findCols (h : Rows) : List Nat := (List.range 8).map fun k => findCol h k

@[expose] def co1XWord : List (Nat × Nat) :=
  [(6, 1), (0, 1), (7, 1), (1, 5), (2, 8), (0, 13), (7, 11), (1, 4), (3, 1), (4, 1),
  (0, 14), (6, 14), (0, 14), (4, 11), (7, 11), (6, 14), (0, 1), (4, 11), (0, 14), (1, 1),
  (4, 1), (2, 8), (4, 1), (7, 2), (6, 14), (2, 8), (7, 1)]

@[expose] def co1YWord : List (Nat × Nat) :=
  [(4, 1), (2, 7), (4, 1), (1, 2), (7, 1), (0, 2), (2, 1), (6, 1), (4, 1), (0, 1), (2, 8),
  (0, 1), (4, 11), (0, 14), (1, 1), (4, 1), (6, 14), (4, 2), (6, 1), (7, 11), (1, 5),
  (0, 14), (2, 1), (6, 1), (0, 2)]

@[expose] def co1UWords : List (List (Nat × Nat)) :=
  [
    [
      (6, 1), (4, 11), (1, 5), (0, 1), (4, 1), (0, 14), (1, 4), (6, 14), (7, 11), (6, 14),
      (0, 14), (1, 4), (3, 1), (4, 1), (6, 14), (1, 1), (7, 1), (4, 1), (0, 14), (7, 11),
      (0, 14)
    ],
    [
      (7, 11), (2, 1), (6, 1), (7, 10), (4, 11), (2, 1), (6, 14), (2, 7), (4, 11), (7, 1),
      (1, 5), (2, 1), (1, 1), (2, 8), (1, 5), (4, 11), (0, 1), (7, 1), (1, 1), (3, 1),
      (4, 11), (0, 13), (1, 5), (0, 14), (6, 1), (0, 1), (1, 1), (2, 8), (0, 1), (1, 1),
      (3, 1), (7, 1), (0, 2), (2, 1)
    ],
    [
      (0, 1), (6, 14), (7, 10), (1, 1), (7, 1), (3, 14), (1, 1), (4, 1), (3, 14), (7, 11),
      (3, 14), (2, 1), (6, 1), (7, 11), (6, 14), (0, 14), (2, 1), (6, 1), (4, 1), (0, 1),
      (2, 8), (1, 1), (0, 1), (2, 1), (6, 13)
    ],
    [
      (0, 1), (6, 14), (7, 10), (1, 1), (7, 1), (3, 14), (1, 1), (4, 1), (3, 14), (7, 11),
      (3, 14), (2, 1), (6, 1), (7, 11), (6, 14), (0, 14), (2, 8), (6, 1), (3, 1), (0, 1),
      (1, 1), (0, 14), (4, 10), (7, 1), (4, 11), (3, 1), (0, 14), (3, 14), (4, 10), (2, 8),
      (0, 1), (1, 5), (6, 1), (2, 8), (4, 1), (3, 13)
    ]
  ]

@[expose] def co1BaseFlag : Nat × Nat := (8, 4)

@[expose] def co1MatsC (_ : Unit := ()) : List (List Nat) :=
  (List.range 8).map fun l => findCols (brayArr[l]!)

@[expose] def co1PowCols (m : List Nat) : Nat → List Nat
  | 0 => idCols
  | n + 1 => colsMul (co1PowCols m n) m

@[expose] def co1WordCGo (M : List (List Nat)) : List (Nat × Nat) → List Nat
  | [] => idCols
  | x :: xs => colsMul (co1WordCGo M xs) (co1PowCols (M.getD x.1 idCols) x.2)

@[expose] def co1WordC (M : List (List Nat)) (w : List (Nat × Nat)) : List Nat :=
  co1WordCGo M w.reverse

@[expose] def co1FlagStepC (m : List Nat) (f : Nat × Nat) : Nat × Nat :=
  let p := colsApply m f.1
  let q := colsApply m f.2
  let q' := if q < (q ^^^ p) then q else (q ^^^ p)
  (p, q')

@[expose] def co1RowsKeyC (m : List Nat) : Nat :=
  Nat.ofDigits 256 (m.take 8)

theorem co1RowsKeyC_injOn {m n : List Nat} (hm : m.length = 8) (hn : n.length = 8)
    (hm' : ∀ x ∈ m, x < 256) (hn' : ∀ x ∈ n, x < 256)
    (h : co1RowsKeyC m = co1RowsKeyC n) : m = n := by
  have hmt : m.take 8 = m := List.take_of_length_le (by omega)
  have hnt : n.take 8 = n := List.take_of_length_le (by omega)
  have h' : Nat.ofDigits 256 m = Nat.ofDigits 256 n := by
    simpa [co1RowsKeyC, hmt, hnt] using h
  exact Nat.injOn_ofDigits (b := 256) (by norm_num) 8 ⟨hm, hm'⟩ ⟨hn, hn'⟩ h'

@[expose] def co1XYCheckC (x y : List Nat) : Bool :=
  let x2 := colsMul x x
  colsMul x2 x == idCols && colsMul (colsMul y y) y == idCols &&
    colsMul x y == colsMul y x && x != idCols && y != idCols && y != x && y != x2 &&
    co1FlagStepC x co1BaseFlag == co1BaseFlag &&
    co1FlagStepC y co1BaseFlag == co1BaseFlag

@[expose] def co1EvalColsR (gens : List (List Nat)) : List Nat → List Nat
  | [] => idCols
  | i :: w => colsMul (gens.getD i idCols) (co1EvalColsR gens w)

theorem co1XYCheckC_spec {x y : List Nat} (h : co1XYCheckC x y = true) :
    colsMul x x |> fun x2 => colsMul x2 x = idCols ∧
      colsMul (colsMul y y) y = idCols ∧
      colsMul x y = colsMul y x ∧ x ≠ idCols ∧ y ≠ idCols ∧ y ≠ x ∧
      y ≠ colsMul x x ∧ co1FlagStepC x co1BaseFlag = co1BaseFlag ∧
      co1FlagStepC y co1BaseFlag = co1BaseFlag := by
  simpa [co1XYCheckC, Bool.and_eq_true, beq_iff_eq, and_assoc] using h

theorem co1UWords_length : co1UWords.length = 4 := rfl

end CFSG.Sporadic.Co1Patterson.IndexNine
