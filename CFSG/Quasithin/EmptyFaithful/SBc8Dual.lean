module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.DotProduct

public section

namespace CFSG.Quasithin

namespace SBc8

private theorem eq_zero_or_eq_one_of_card_eq_two {F : Type} [Field F] [Fintype F]
    (hF : Fintype.card F = 2) (c : F) : c = 0 ∨ c = 1 := by
  have h2 : Nat.card F = 2 := by rw [Nat.card_eq_fintype_card, hF]
  obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (0 : F)).1 h2
  by_cases hc : c = 0
  · exact Or.inl hc
  · exact Or.inr ((hy c hc).trans (hy 1 one_ne_zero).symm)

private theorem exists_ne_zero_dotProduct_eq_zero_of_ne_top {F : Type} [Field F] [Fintype F]
    (hF : Fintype.card F = 2) (N : AddSubgroup (Fin 3 → F)) (hN : N ≠ ⊤) :
    ∃ w : Fin 3 → F, w ≠ 0 ∧ ∀ n ∈ N, w ⬝ᵥ n = 0 := by
  let S : Submodule F (Fin 3 → F) :=
    { carrier := N
      add_mem' := fun ha hb => N.add_mem ha hb
      zero_mem' := N.zero_mem
      smul_mem' := fun c x hx => by
        rcases eq_zero_or_eq_one_of_card_eq_two hF c with rfl | rfl
        · simp
        · simpa using hx }
  have hS : S < ⊤ := by
    refine lt_top_iff_ne_top.2 fun h => hN ?_
    refine (AddSubgroup.eq_top_iff' N).2 fun x => ?_
    have hx : x ∈ S := by rw [h]; exact Submodule.mem_top
    exact hx
  obtain ⟨f, hf0, hfker⟩ := S.exists_le_ker_of_lt_top hS
  have hf : ∀ x : Fin 3 → F, f x = (fun i => f (fun j => if i = j then 1 else 0)) ⬝ᵥ x := by
    intro x
    rw [LinearMap.pi_apply_eq_sum_univ f x, dotProduct_comm]
    simp [dotProduct]
  refine ⟨fun i => f (fun j => if i = j then 1 else 0), fun h => hf0 ?_, fun n hn => ?_⟩
  · refine LinearMap.ext fun x => ?_
    rw [hf x, h]
    simp
  · rw [← hf n]
    exact LinearMap.mem_ker.1 (hfker (show n ∈ S from hn))

theorem closure_dual_commutators_eq_top {F : Type} [Field F] [Fintype F] (hF : Fintype.card F = 2)
    (𝒢 : Set (Matrix (Fin 3) (Fin 3) F)) (hdet : ∀ A ∈ 𝒢, IsUnit A)
    (hfix : ∀ u : Fin 3 → F, (∀ A ∈ 𝒢, A.mulVec u = u) → u = 0) :
    AddSubgroup.closure {x : Fin 3 → F | ∃ A ∈ 𝒢, ∃ u : Fin 3 → F, x = (A⁻¹).transpose.mulVec u - u} = ⊤ := by
  by_contra hN
  obtain ⟨w, hw0, hw⟩ := exists_ne_zero_dotProduct_eq_zero_of_ne_top hF _ hN
  refine hw0 (hfix w fun A hA => ?_)
  have hAinv : A⁻¹.mulVec w = w := by
    refine sub_eq_zero.1 (dotProduct_eq_zero _ fun u => ?_)
    have h := hw ((A⁻¹).transpose.mulVec u - u) (AddSubgroup.subset_closure ⟨A, hA, u, rfl⟩)
    rw [dotProduct_sub, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose] at h
    rwa [sub_dotProduct]
  calc A.mulVec w = A.mulVec (A⁻¹.mulVec w) := by rw [hAinv]
    _ = (A * A⁻¹).mulVec w := Matrix.mulVec_mulVec w A A⁻¹
    _ = w := by rw [Matrix.mul_nonsing_inv A (A.isUnit_iff_isUnit_det.1 (hdet A hA)), Matrix.one_mulVec]

end SBc8

end CFSG.Quasithin
