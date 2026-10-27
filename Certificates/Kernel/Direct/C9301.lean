module

public import CFSG.RankThree.PartTwo.Sec15.Item153Push2ProofPerm
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.ClassicalInvolution.SmallCases.NobqCriteria

public section

namespace CertificateChecks.KernelDirect.C9301

open CFSG CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Nobq
open Equiv Equiv.Perm

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem exists_commuting_odd_check : ∀ (d : Perm (Fin 4)), (∀ i, (d * d) i ≠ i) →
    ∀ (ε : ℤˣ), ∃ u : Perm (Fin 4), sign u = ε ∧ u * (d * d) = (d * d) * u ∧
      (d * (u * d * u⁻¹)) * (d * (u * d * u⁻¹)) = 1 := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem exists_conj_involution_four : ∀ (r : Perm (Fin 4)), r * r = 1 → r ≠ 1 →
    ∃ v : Perm (Fin 4), (r * (v * r * v⁻¹)) * (r * (v * r * v⁻¹)) = 1 ∧ r * (v * r * v⁻¹) ≠ 1 := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem exists_conj_involution_five : ∀ (r : Perm (Fin 5)), r * r = 1 → r ≠ 1 →
    ∃ v : Perm (Fin 5), (r * (v * r * v⁻¹)) * (r * (v * r * v⁻¹)) = 1 ∧ r * (v * r * v⁻¹) ≠ 1 := by
  decide +kernel

open CFSG.RankThree.PartTwo.Sec15.Push153B (pcode cmul pcode_mul pcode_one pcode_injective
  pcode_mem_permutations')

def invCands (n : ℕ) : List (Perm (Fin n)) :=
  (List.finRange n).flatMap (fun i => (List.finRange n).filterMap fun j =>
    if i < j then some (swap i j) else none) ++
  (List.finRange n).flatMap fun i => (List.finRange n).flatMap fun j =>
    (List.finRange n).flatMap fun k => (List.finRange n).filterMap fun l =>
      if i < j ∧ k < l ∧ i < k ∧ j ≠ k ∧ j ≠ l then some (swap i j * swap k l) else none

def invNe (n : ℕ) (u : List ℕ) : Bool := cmul u u == List.range n && !(u == List.range n)

def conjOK (n : ℕ) (l c : List ℕ) : Bool := cmul c c == List.range n && invNe n (cmul l (cmul (cmul c l) c))

def conjCheck (n : ℕ) : Bool :=
  (List.range n).permutations'.all fun l =>
    !invNe n l || (invCands n).any fun v => conjOK n l (pcode v)

theorem conjCheck_sound {n : ℕ} (h : conjCheck n = true) (r : Perm (Fin n)) (h1 : r * r = 1)
    (h2 : r ≠ 1) :
    ∃ v : Perm (Fin n), (r * (v * r * v⁻¹)) * (r * (v * r * v⁻¹)) = 1 ∧ r * (v * r * v⁻¹) ≠ 1 := by
  have hall := List.all_eq_true.1 h (pcode r) (pcode_mem_permutations' r)
  have hr : invNe n (pcode r) = true := by
    have e1 : cmul (pcode r) (pcode r) = List.range n := by rw [← pcode_mul, h1, pcode_one]
    have e2 : pcode r ≠ List.range n := fun e => h2 (pcode_injective (e.trans pcode_one.symm))
    simp [invNe, e1, e2]
  rw [hr, Bool.not_true, Bool.false_or, List.any_eq_true] at hall
  obtain ⟨v, -, hv⟩ := hall
  simp only [conjOK, invNe, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', beq_eq_false_iff_ne]
    at hv
  obtain ⟨hvv, hu1, hu2⟩ := hv
  have hinv : v⁻¹ = v :=
    inv_eq_of_mul_eq_one_right (pcode_injective (by rw [pcode_mul, hvv, pcode_one]))
  have hu : pcode (r * (v * r * v⁻¹)) =
      cmul (pcode r) (cmul (cmul (pcode v) (pcode r)) (pcode v)) := by
    rw [hinv, pcode_mul, pcode_mul, pcode_mul]
  refine ⟨v, pcode_injective ?_, fun e => hu2 ?_⟩
  · rw [pcode_mul, hu, hu1, pcode_one]
  · rw [← hu, e, pcode_one]

set_option maxRecDepth 100000 in
theorem conjCheck_six : conjCheck 6 = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem conjCheck_seven : conjCheck 7 = true := by
  decide +kernel

theorem exists_conj_involution_six : ∀ (r : Perm (Fin 6)), r * r = 1 → r ≠ 1 →
    ∃ v : Perm (Fin 6), (r * (v * r * v⁻¹)) * (r * (v * r * v⁻¹)) = 1 ∧ r * (v * r * v⁻¹) ≠ 1 :=
  conjCheck_sound conjCheck_six

theorem exists_conj_involution_seven : ∀ (r : Perm (Fin 7)), r * r = 1 → r ≠ 1 →
    ∃ v : Perm (Fin 7), (r * (v * r * v⁻¹)) * (r * (v * r * v⁻¹)) = 1 ∧ r * (v * r * v⁻¹) ≠ 1 :=
  conjCheck_sound conjCheck_seven

end CertificateChecks.KernelDirect.C9301
