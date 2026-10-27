module

public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Tactic.NormNum.GCD
public import CFSG.RankThree.PartTwo.Sec14.Item148HJProofA6DataK

public section

namespace CFSG.RankThree.PartTwo.Sec14.Item148HJ

open Equiv

@[expose] def cA : Perm (Fin 6) := swap 0 1 * swap 1 2

@[expose] def cB : Perm (Fin 6) := swap 0 1 * swap 1 2 * (swap 3 4 * swap 4 5)

@[expose] def invA : List (Perm (Fin 6)) :=
  [swap 0 1 * swap 2 3, swap 0 1 * swap 2 4, swap 0 1 * swap 2 5, swap 0 2 * swap 1 3,
    swap 0 2 * swap 1 4, swap 0 2 * swap 1 5, swap 0 3 * swap 1 2, swap 0 4 * swap 1 2,
    swap 0 5 * swap 1 2]

@[expose] def invB : List (Perm (Fin 6)) :=
  [swap 1 3 * swap 2 4, swap 1 4 * swap 2 5, swap 1 5 * swap 2 3, swap 0 3 * swap 2 5,
    swap 0 3 * swap 1 4, swap 0 4 * swap 2 3, swap 0 4 * swap 1 5, swap 0 5 * swap 2 4,
    swap 0 5 * swap 1 3]

@[expose] def repA : Fin 3 → Perm (Fin 6) :=
  ![swap 0 1 * swap 2 3, swap 0 1 * swap 2 4, swap 0 1 * swap 2 5]

@[expose] def repB : Fin 3 → Perm (Fin 6) :=
  ![swap 1 3 * swap 2 4, swap 1 4 * swap 2 5, swap 1 5 * swap 2 3]

abbrev InS (c u v : Perm (Fin 6)) : Prop :=
  v = u ∨ v = c * u * c⁻¹ ∨ v = u * (c * u * c⁻¹)

abbrev W3 (c u : Perm (Fin 6)) : Prop :=
  (u * u * (c * u * c⁻¹) * (c * (c * u * c⁻¹) * c⁻¹) ≠ 1 ∧
      (u * u * (c * u * c⁻¹) * (c * (c * u * c⁻¹) * c⁻¹)) ^ 3 = 1) ∨
    (u * u * (c * (c * u * c⁻¹) * c⁻¹) * (c * u * c⁻¹) ≠ 1 ∧
      (u * u * (c * (c * u * c⁻¹) * c⁻¹) * (c * u * c⁻¹)) ^ 3 = 1) ∨
    (u * (c * u * c⁻¹) * u * (c * (c * u * c⁻¹) * c⁻¹) ≠ 1 ∧
      (u * (c * u * c⁻¹) * u * (c * (c * u * c⁻¹) * c⁻¹)) ^ 3 = 1)

structure RepData (c : Perm (Fin 6)) (l : List (Perm (Fin 6))) (r : Fin 3 → Perm (Fin 6)) :
    Prop where
  w3 : ∀ u : Perm (Fin 6), Perm.sign u = 1 → u ≠ 1 → u ∉ l → W3 c u
  inv : ∀ u ∈ l, u * u = 1 ∧ u ≠ 1 ∧ c * u * c⁻¹ ∈ l ∧
    u * (c * u * c⁻¹) = c * (c * u * c⁻¹) * c⁻¹ ∧ u * (c * u * c⁻¹) = c * u * c⁻¹ * u
  prod : ∀ u ∈ l, ∀ v ∈ l, InS c u v ∨ (u * v ≠ 1 ∧ u * v ∉ l)
  symm : ∀ u ∈ l, ∀ v ∈ l, InS c u v → InS c v u
  three : ∀ y : Perm (Fin 6), y ≠ 1 → y ^ 3 = 1 → ∀ u ∈ l, u * y ≠ y * u
  five : ∀ y : Perm (Fin 6), y ≠ 1 → y ^ 5 = 1 →
    c * y * c⁻¹ ≠ y ∧ c * y * c⁻¹ ≠ y ^ 2 ∧ c * y * c⁻¹ ≠ y ^ 3 ∧ c * y * c⁻¹ ≠ y ^ 4
  reps : ∀ u ∈ l, ∀ w ∈ l, InS c u w ∨ ∃ k k' : Fin 3, k ≠ k' ∧ InS c u (r k) ∧
    InS c u (c * r k * c⁻¹) ∧ InS c w (r k') ∧ InS c w (c * r k' * c⁻¹)

set_option maxHeartbeats 1000000 in
theorem w3_A : ∀ u : Perm (Fin 6), Perm.sign u = 1 → u ≠ 1 → u ∉ invA → W3 cA u :=
  Item148HJK.w3_of (c := cA) (l := invA) (C := 5517345) (Ci := 5517570) (E := 5517840)
    (L := [5513985, 5387265, 2372865, 5509170, 5320770, 1323090, 5505315, 5255460, 274725])
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

set_option maxHeartbeats 1000000 in
theorem inv_A : ∀ u ∈ invA, u * u = 1 ∧ u ≠ 1 ∧ cA * u * cA⁻¹ ∈ invA ∧
    u * (cA * u * cA⁻¹) = cA * (cA * u * cA⁻¹) * cA⁻¹ ∧
      u * (cA * u * cA⁻¹) = cA * u * cA⁻¹ * u :=
  (Item148HJK.list_of (c := cA) (l := invA) (C := 5517345) (Ci := 5517570) (E := 5517840)
    (L := [5513985, 5387265, 2372865, 5509170, 5320770, 1323090, 5505315, 5255460, 274725])
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)).1

set_option maxHeartbeats 1000000 in
theorem prod_A : ∀ u ∈ invA, ∀ v ∈ invA, InS cA u v ∨ (u * v ≠ 1 ∧ u * v ∉ invA) :=
  (Item148HJK.list_of (c := cA) (l := invA) (C := 5517345) (Ci := 5517570) (E := 5517840)
    (L := [5513985, 5387265, 2372865, 5509170, 5320770, 1323090, 5505315, 5255460, 274725])
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)).2.1

set_option maxHeartbeats 1000000 in
theorem symm_A : ∀ u ∈ invA, ∀ v ∈ invA, InS cA u v → InS cA v u :=
  (Item148HJK.list_of (c := cA) (l := invA) (C := 5517345) (Ci := 5517570) (E := 5517840)
    (L := [5513985, 5387265, 2372865, 5509170, 5320770, 1323090, 5505315, 5255460, 274725])
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)).2.2

set_option maxHeartbeats 1000000 in
theorem three_A : ∀ y : Perm (Fin 6), y ≠ 1 → y ^ 3 = 1 → ∀ u ∈ invA, u * y ≠ y * u :=
  Item148HJK.three_of (l := invA) (E := 5517840)
    (L := [5513985, 5387265, 2372865, 5509170, 5320770, 1323090, 5505315, 5255460, 274725])
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 1000000 in
theorem five_A : ∀ y : Perm (Fin 6), y ≠ 1 → y ^ 5 = 1 →
    cA * y * cA⁻¹ ≠ y ∧ cA * y * cA⁻¹ ≠ y ^ 2 ∧ cA * y * cA⁻¹ ≠ y ^ 3 ∧ cA * y * cA⁻¹ ≠ y ^ 4 :=
  Item148HJK.five_of (c := cA) (C := 5517345) (Ci := 5517570) (E := 5517840)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 1000000 in
theorem reps_A : ∀ u ∈ invA, ∀ w ∈ invA, InS cA u w ∨ ∃ k k' : Fin 3, k ≠ k' ∧ InS cA u (repA k) ∧
    InS cA u (cA * repA k * cA⁻¹) ∧ InS cA w (repA k') ∧ InS cA w (cA * repA k' * cA⁻¹) := by
  decide +kernel

theorem repData_A : RepData cA invA repA :=
  ⟨w3_A, inv_A, prod_A, symm_A, three_A, five_A, reps_A⟩

set_option maxHeartbeats 1000000 in
theorem w3_B : ∀ u : Perm (Fin 6), Perm.sign u = 1 → u ≠ 1 → u ∉ invB → W3 cB u :=
  Item148HJK.w3_of (c := cB) (l := invB) (C := 3489825) (Ci := 4411650) (E := 5517840)
    (L := [5379120, 2176320, 1319760, 2360595, 5308995, 5251860, 1061460, 144405, 266805])
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

set_option maxHeartbeats 1000000 in
theorem inv_B : ∀ u ∈ invB, u * u = 1 ∧ u ≠ 1 ∧ cB * u * cB⁻¹ ∈ invB ∧
    u * (cB * u * cB⁻¹) = cB * (cB * u * cB⁻¹) * cB⁻¹ ∧
      u * (cB * u * cB⁻¹) = cB * u * cB⁻¹ * u :=
  (Item148HJK.list_of (c := cB) (l := invB) (C := 3489825) (Ci := 4411650) (E := 5517840)
    (L := [5379120, 2176320, 1319760, 2360595, 5308995, 5251860, 1061460, 144405, 266805])
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)).1

set_option maxHeartbeats 1000000 in
theorem prod_B : ∀ u ∈ invB, ∀ v ∈ invB, InS cB u v ∨ (u * v ≠ 1 ∧ u * v ∉ invB) :=
  (Item148HJK.list_of (c := cB) (l := invB) (C := 3489825) (Ci := 4411650) (E := 5517840)
    (L := [5379120, 2176320, 1319760, 2360595, 5308995, 5251860, 1061460, 144405, 266805])
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)).2.1

set_option maxHeartbeats 1000000 in
theorem symm_B : ∀ u ∈ invB, ∀ v ∈ invB, InS cB u v → InS cB v u :=
  (Item148HJK.list_of (c := cB) (l := invB) (C := 3489825) (Ci := 4411650) (E := 5517840)
    (L := [5379120, 2176320, 1319760, 2360595, 5308995, 5251860, 1061460, 144405, 266805])
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)).2.2

set_option maxHeartbeats 1000000 in
theorem three_B : ∀ y : Perm (Fin 6), y ≠ 1 → y ^ 3 = 1 → ∀ u ∈ invB, u * y ≠ y * u :=
  Item148HJK.three_of (l := invB) (E := 5517840)
    (L := [5379120, 2176320, 1319760, 2360595, 5308995, 5251860, 1061460, 144405, 266805])
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 1000000 in
theorem five_B : ∀ y : Perm (Fin 6), y ≠ 1 → y ^ 5 = 1 →
    cB * y * cB⁻¹ ≠ y ∧ cB * y * cB⁻¹ ≠ y ^ 2 ∧ cB * y * cB⁻¹ ≠ y ^ 3 ∧ cB * y * cB⁻¹ ≠ y ^ 4 :=
  Item148HJK.five_of (c := cB) (C := 3489825) (Ci := 4411650) (E := 5517840)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 1000000 in
theorem reps_B : ∀ u ∈ invB, ∀ w ∈ invB, InS cB u w ∨ ∃ k k' : Fin 3, k ≠ k' ∧ InS cB u (repB k) ∧
    InS cB u (cB * repB k * cB⁻¹) ∧ InS cB w (repB k') ∧ InS cB w (cB * repB k' * cB⁻¹) := by
  decide +kernel

theorem repData_B : RepData cB invB repB :=
  ⟨w3_B, inv_B, prod_B, symm_B, three_B, five_B, reps_B⟩

end CFSG.RankThree.PartTwo.Sec14.Item148HJ
