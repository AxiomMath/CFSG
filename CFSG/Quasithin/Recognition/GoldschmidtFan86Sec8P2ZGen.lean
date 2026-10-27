module

public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Data.Fintype.Card

public section

namespace CFSG.Quasithin.Fan86

@[expose] def powB {M : Type*} [Monoid M] (w : M) (e : Bool) : M := if e then w else 1

theorem powB_mul {M : Type*} [Monoid M] (w : M) (hw : w * w = 1) (e e' : Bool) :
    powB w e * powB w e' = powB w (xor e e') := by
  cases e <;> cases e' <;> simp [powB, hw]

variable {A : Type*} [CommGroup A]

theorem prod_symmDiff_of_sq (z : Fin 5 → A) (hsq : ∀ s, z s * z s = 1) (S T : Finset (Fin 5)) :
    (∏ s ∈ S, z s) * (∏ s ∈ T, z s) = ∏ s ∈ symmDiff S T, z s := by
  have key : ∀ U : Finset (Fin 5), ∏ s ∈ U, z s = ∏ s : Fin 5, (if s ∈ U then z s else 1) := by
    intro U
    rw [Finset.prod_ite_mem, Finset.univ_inter]
  rw [key S, key T, key (symmDiff S T), ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun s _ => ?_
  by_cases hS : s ∈ S <;> by_cases hT : s ∈ T <;> simp [hS, hT, Finset.mem_symmDiff, hsq s]

theorem prod_compl_of_prod_one (z : Fin 5 → A) (hsq : ∀ s, z s * z s = 1) (hprod : ∏ s, z s = 1)
    (S : Finset (Fin 5)) : ∏ s ∈ S, z s = ∏ s ∈ Sᶜ, z s := by
  have h1 : (∏ s ∈ S, z s) * ∏ s ∈ Sᶜ, z s = 1 := by
    rw [Finset.prod_mul_prod_compl, hprod]
  have h2 : (∏ s ∈ Sᶜ, z s) * ∏ s ∈ Sᶜ, z s = 1 := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun s _ => hsq s
  exact mul_right_cancel (h1.trans h2.symm)

theorem exists_small (z : Fin 5 → A) (hsq : ∀ s, z s * z s = 1) (hprod : ∏ s, z s = 1)
    (S : Finset (Fin 5)) : ∃ S' : Finset (Fin 5), S'.card ≤ 2 ∧ ∏ s ∈ S, z s = ∏ s ∈ S', z s := by
  by_cases h : S.card ≤ 2
  · exact ⟨S, h, rfl⟩
  · refine ⟨Sᶜ, ?_, prod_compl_of_prod_one z hsq hprod S⟩
    have := Finset.card_add_card_compl S
    simp only [Fintype.card_fin] at this
    omega

theorem exists_normal_form (z : Fin 5 → A) (w : A) (hsq : ∀ s, z s * z s = 1) (hw : w * w = 1)
    (hprod : ∏ s, z s = 1) :
    ∀ ζ ∈ Subgroup.closure (Set.range z ∪ {w}),
      ∃ (e : Bool) (S : Finset (Fin 5)), S.card ≤ 2 ∧ ζ = powB w e * ∏ s ∈ S, z s := by
  intro ζ hζ
  induction hζ using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with ⟨l, rfl⟩ | hx
    · exact ⟨false, {l}, by simp, by simp [powB]⟩
    · rw [Set.mem_singleton_iff.1 hx]
      exact ⟨true, ∅, by simp, by simp [powB]⟩
  | one => exact ⟨false, ∅, by simp, by simp [powB]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨e, S, hS, rfl⟩ := hx
    obtain ⟨e', T, hT, rfl⟩ := hy
    obtain ⟨U, hU, hUe⟩ := exists_small z hsq hprod (symmDiff S T)
    refine ⟨xor e e', U, hU, ?_⟩
    rw [← powB_mul w hw, ← hUe, ← prod_symmDiff_of_sq z hsq]
    exact mul_mul_mul_comm _ _ _ _
  | inv x _ hx =>
    obtain ⟨e, S, hS, rfl⟩ := hx
    refine ⟨e, S, hS, ?_⟩
    have h1 : (powB w e * ∏ s ∈ S, z s) * (powB w e * ∏ s ∈ S, z s) = 1 := by
      have : (powB w e * ∏ s ∈ S, z s) * (powB w e * ∏ s ∈ S, z s) =
          (powB w e * powB w e) * ((∏ s ∈ S, z s) * ∏ s ∈ S, z s) := mul_mul_mul_comm _ _ _ _
      rw [this, powB_mul w hw, prod_symmDiff_of_sq z hsq, symmDiff_self]
      simp [powB]
    exact inv_eq_of_mul_eq_one_right h1

end CFSG.Quasithin.Fan86
