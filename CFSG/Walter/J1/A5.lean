module

public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.Walter.J1

namespace A5

private instance instDecEqPermFin5 : DecidableEq (Equiv.Perm (Fin 5)) := fun a b =>
  decidable_of_iff (∀ i : Fin 5, a i = b i) ⟨Equiv.ext, fun h i => congrArg (fun e => e i) h⟩

private instance instDecMemA5 :
    DecidablePred (fun σ : Equiv.Perm (Fin 5) => σ ∈ alternatingGroup (Fin 5)) :=
  Equiv.Perm.sign.decidableMemKer

abbrev A := alternatingGroup (Fin 5)

set_option maxHeartbeats 0 in
theorem pow_eq_one : ∀ x : A, x ^ 2 = 1 ∨ x ^ 3 = 1 ∨ x ^ 5 = 1 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem centralizer_three : ∀ x y : A, (x ^ 3 = 1 ∧ x ≠ 1 ∧ x * y = y * x) →
    (y = 1 ∨ y = x ∨ y = x ^ 2) := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem centralizer_five : ∀ x y : A, (x ^ 5 = 1 ∧ x ≠ 1 ∧ x * y = y * x) →
    (y = 1 ∨ y = x ∨ y = x ^ 2 ∨ y = x ^ 3 ∨ y = x ^ 4) := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem centralizer_two : ∀ x y : A, (x ^ 2 = 1 ∧ x ≠ 1 ∧ x * y = y * x) → y ^ 2 = 1 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem exists_inv : ∀ x : A, (x ≠ 1 ∧ x ^ 15 = 1) →
    ∃ y : A, y ^ 2 = 1 ∧ y ≠ 1 ∧ y * x * y⁻¹ = x⁻¹ := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem three_five : ∀ x y : A, (x ^ 3 = 1 ∧ x ≠ 1 ∧ y ^ 5 = 1 ∧ y ≠ 1) →
    (x * y * x⁻¹ ≠ y ∧ x * y * x⁻¹ ≠ y ^ 2 ∧ x * y * x⁻¹ ≠ y ^ 3 ∧ x * y * x⁻¹ ≠ y ^ 4) := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem four_group : ∀ a b : A, (a ^ 2 = 1 ∧ b ^ 2 = 1 ∧ a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b ∧ a * b = b * a) →
    ∃ c : A, c ^ 3 = 1 ∧ c * a * c⁻¹ = b ∧ c * b * c⁻¹ = a * b := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem card_involutions : (Finset.univ.filter (fun x : A => x ^ 2 = 1 ∧ x ≠ 1)).card = 15 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem conj_inv : ∀ y v : A, (y ≠ 1 ∧ y ^ 15 = 1 ∧ v ^ 2 = 1 ∧ v ≠ 1 ∧
    (v * y * v⁻¹ = 1 ∨ v * y * v⁻¹ = y ∨ v * y * v⁻¹ = y ^ 2 ∨ v * y * v⁻¹ = y ^ 3 ∨
      v * y * v⁻¹ = y ^ 4)) → v * y * v⁻¹ = y⁻¹ := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem conj_three : ∀ x y : A, (x ^ 3 = 1 ∧ x ≠ 1 ∧ y ^ 3 = 1 ∧ y ≠ 1) →
    ∃ g : A, g * x * g⁻¹ = y := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem conj_five : ∀ x y : A, (x ^ 5 = 1 ∧ x ≠ 1 ∧ y ^ 5 = 1 ∧ y ≠ 1) →
    ∃ g : A, g * x * g⁻¹ = y ∨ g * x * g⁻¹ = y ^ 2 := by
  decide +kernel

set_option synthInstance.maxSize 2048 in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 0 in
theorem normalizer_three : ∀ c : A, (c ^ 3 = 1 ∧ c ≠ 1) → ∀ f : A,
    (f ^ 2 = 1 ∧ f ≠ 1 ∧ f * c * f⁻¹ = c⁻¹) → ∀ g : A, (g * c * g⁻¹ = c ∨ g * c * g⁻¹ = c ^ 2) →
    (g = 1 ∨ g = c ∨ g = c ^ 2 ∨ g = f ∨ g = c * f ∨ g = c ^ 2 * f) := by
  decide +kernel

end A5

end CFSG.Walter.J1
