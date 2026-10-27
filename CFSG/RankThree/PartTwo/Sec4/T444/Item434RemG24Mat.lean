module

public import CFSG.Fischer.F4
public import Mathlib

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434RemG24

open CFSG.Fischer Matrix

scoped instance (priority := high) decEqF4 : DecidableEq F4 := fun a b =>
  decidable_of_iff (a.code = b.code) (by cases a; cases b; simp)

abbrev Mat3 : Type := Matrix (Fin 3) (Fin 3) F4

abbrev w : F4 := F4.ω

abbrev w2 : F4 := ⟨3⟩

@[expose] def sZeroList : List Mat3 :=
  [!![0, 0, 1; 1, 0, 0; 0, 1, 0],
  !![0, 0, 1; w, 0, 0; 0, w2, 0],
  !![0, 0, 1; w2, 0, 0; 0, w, 0],
  !![0, 0, w; 1, 0, 0; 0, w2, 0],
  !![0, 0, w; w, 0, 0; 0, w, 0],
  !![0, 0, w; w2, 0, 0; 0, 1, 0],
  !![0, 0, w2; 1, 0, 0; 0, w, 0],
  !![0, 0, w2; w, 0, 0; 0, 1, 0],
  !![0, 0, w2; w2, 0, 0; 0, w2, 0],
  !![0, 1, 0; 0, 0, 1; 1, 0, 0],
  !![0, 1, 0; 0, 0, w; w2, 0, 0],
  !![0, 1, 0; 0, 0, w2; w, 0, 0],
  !![0, w, 0; 0, 0, 1; w2, 0, 0],
  !![0, w, 0; 0, 0, w; w, 0, 0],
  !![0, w, 0; 0, 0, w2; 1, 0, 0],
  !![0, w2, 0; 0, 0, 1; w, 0, 0],
  !![0, w2, 0; 0, 0, w; 1, 0, 0],
  !![0, w2, 0; 0, 0, w2; w2, 0, 0],
  !![1, 0, 0; 0, 1, 0; 0, 0, 1],
  !![1, 0, 0; 0, w, 0; 0, 0, w2],
  !![1, 0, 0; 0, w2, 0; 0, 0, w],
  !![w, 0, 0; 0, 1, 0; 0, 0, w2],
  !![w, 0, 0; 0, w, 0; 0, 0, w],
  !![w, 0, 0; 0, w2, 0; 0, 0, 1],
  !![w2, 0, 0; 0, 1, 0; 0, 0, w],
  !![w2, 0, 0; 0, w, 0; 0, 0, 1],
  !![w2, 0, 0; 0, w2, 0; 0, 0, w2]]

@[expose] def zList : List Mat3 :=
  [!![1, 0, 0; 0, 1, 0; 0, 0, 1], !![w, 0, 0; 0, w, 0; 0, 0, w], !![w2, 0, 0; 0, w2, 0; 0, 0, w2]]

@[expose] def eList0 : List Mat3 :=
  [!![0, 0, 1; w2, 0, 0; 0, w, 0], !![0, 0, w; 1, 0, 0; 0, w2, 0], !![0, 0, w2; w, 0, 0; 0, 1, 0],
    !![0, 1, 0; 0, 0, w; w2, 0, 0], !![0, w, 0; 0, 0, w2; 1, 0, 0], !![0, w2, 0; 0, 0, 1; w, 0, 0],
    !![1, 0, 0; 0, 1, 0; 0, 0, 1], !![w, 0, 0; 0, w, 0; 0, 0, w],
    !![w2, 0, 0; 0, w2, 0; 0, 0, w2]]

@[expose] def eList1 : List Mat3 :=
  [!![0, 0, 1; 1, 0, 0; 0, 1, 0], !![0, 0, w; w, 0, 0; 0, w, 0], !![0, 0, w2; w2, 0, 0; 0, w2, 0],
    !![0, 1, 0; 0, 0, 1; 1, 0, 0], !![0, w, 0; 0, 0, w; w, 0, 0],
    !![0, w2, 0; 0, 0, w2; w2, 0, 0], !![1, 0, 0; 0, 1, 0; 0, 0, 1],
    !![w, 0, 0; 0, w, 0; 0, 0, w], !![w2, 0, 0; 0, w2, 0; 0, 0, w2]]

@[expose] def eList2 : List Mat3 :=
  [!![0, 0, 1; w, 0, 0; 0, w2, 0], !![0, 0, w; w2, 0, 0; 0, 1, 0], !![0, 0, w2; 1, 0, 0; 0, w, 0],
    !![0, 1, 0; 0, 0, w2; w, 0, 0], !![0, w, 0; 0, 0, 1; w2, 0, 0], !![0, w2, 0; 0, 0, w; 1, 0, 0],
    !![1, 0, 0; 0, 1, 0; 0, 0, 1], !![w, 0, 0; 0, w, 0; 0, 0, w],
    !![w2, 0, 0; 0, w2, 0; 0, 0, w2]]

@[expose] def eList3 : List Mat3 :=
  [!![1, 0, 0; 0, 1, 0; 0, 0, 1], !![1, 0, 0; 0, w, 0; 0, 0, w2], !![1, 0, 0; 0, w2, 0; 0, 0, w],
    !![w, 0, 0; 0, 1, 0; 0, 0, w2], !![w, 0, 0; 0, w, 0; 0, 0, w], !![w, 0, 0; 0, w2, 0; 0, 0, 1],
    !![w2, 0, 0; 0, 1, 0; 0, 0, w], !![w2, 0, 0; 0, w, 0; 0, 0, 1],
    !![w2, 0, 0; 0, w2, 0; 0, 0, w2]]

@[expose] def eList : Fin 4 → List Mat3 := ![eList0, eList1, eList2, eList3]

@[expose] def nMat : Fin 4 → Mat3 :=
  ![!![1, 1, w; w, w, w2; w, w, w2], !![1, 1, 1; w, w, w; w2, w2, w2],
    !![1, 1, w2; w, w, 1; 1, 1, w2], !![0, 0, 0; 0, 0, 0; 0, 1, 0]]

@[expose] def eIdx (x : Mat3) : Fin 4 :=
  if x ∈ eList0 then 0 else if x ∈ eList1 then 1 else if x ∈ eList2 then 2 else 3

set_option maxRecDepth 10000 in
theorem sZero_checks :
    (sZeroList.all fun a => sZeroList.all fun b => decide (a * b ∈ sZeroList)) = true ∧
      (1 : Mat3) ∈ sZeroList ∧
      (sZeroList.all fun a => decide (a * a * a = 1) && decide (a.det = 1)) = true := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 10000 in
theorem eList_checks : ∀ i : Fin 4,
    ((eList i).all fun a => decide (a ∈ sZeroList)) = true ∧
      (zList.all fun a => decide (a ∈ eList i)) = true ∧
      ((eList i).all fun a => (eList i).all fun b => decide (a * b ∈ eList i)) = true ∧
      ((eList i).all fun a => (eList i).all fun b => decide (a * b = b * a)) = true ∧
      (eList i).length = 9 ∧ (eList i).Nodup := by
  decide +kernel

set_option maxRecDepth 10000 in
theorem centralizer_check :
    (sZeroList.all fun x => decide (x ∈ zList) ||
      (decide (x ∈ eList (eIdx x)) &&
        sZeroList.all fun y => !decide (x * y = y * x) || decide (y ∈ eList (eIdx x)))) =
      true := by
  decide +kernel

set_option maxRecDepth 10000 in
theorem normalizes_check : ∀ i : Fin 4, nMat i * nMat i = 0 ∧ nMat i ≠ 0 ∧
    ((eList i).all fun e => ([1, w, w2] : List F4).any fun c =>
      decide (e * nMat i * (e * e) = c • nMat i)) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
theorem sZero_noncomm : (!![0, 0, 1; 1, 0, 0; 0, 1, 0] : Mat3) ∈ sZeroList ∧
    (!![0, 0, 1; w, 0, 0; 0, w2, 0] : Mat3) ∈ sZeroList ∧
    (!![0, 0, 1; 1, 0, 0; 0, 1, 0] : Mat3) * !![0, 0, 1; w, 0, 0; 0, w2, 0] ≠
      !![0, 0, 1; w, 0, 0; 0, w2, 0] * !![0, 0, 1; 1, 0, 0; 0, 1, 0] := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 10000 in
theorem sZero_card : sZeroList.length = 27 ∧ sZeroList.Nodup ∧ zList.length = 3 ∧
    zList.Nodup ∧ (zList.all fun a => decide (a ∈ sZeroList)) = true := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel⟩

end CFSG.RankThree.PartTwo.Sec4.Item434RemG24
