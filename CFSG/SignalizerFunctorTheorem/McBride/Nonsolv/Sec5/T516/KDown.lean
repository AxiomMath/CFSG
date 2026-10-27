module

public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Basic

public section

open CFSG.Open
open scoped commutatorElement

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.T516

variable {Γ : Type*} [Group Γ]

theorem commutator_mem_sol_iff {X : Subgroup Γ} (a b : ↥X) :
    ⁅(a : Γ), (b : Γ)⁆ ∈ sol X ↔ ⁅a, b⁆ ∈ CFSG.solvableRadical ↥X := by
  rw [← subgroupOf_sol, Subgroup.mem_subgroupOf]
  rfl

theorem mcalA_eq_empty_of_kDown_eq_self {G A : Subgroup Γ} (h : kDown G A = G) :
    mcalA G A = ∅ := by
  ext M
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hM
  obtain ⟨-, -, -, -, hnc⟩ := hM.1
  refine hnc (isMulCommutative_iff.mpr fun a b => ?_)
  obtain ⟨x, hx, hxa⟩ := a.2
  obtain ⟨y, hy, hyb⟩ := b.2
  have hMk : M ≤ kUp G A := le_iSup₂_of_le M hM le_rfl
  have hxG : (x : Γ) ∈ kDown G A := by
    rw [h]
    exact x.2
  have h1 := (mem_kDown_iff.mp hxG).2 (y : Γ) (hMk hy)
  have h2 : ⁅x, y⁆ ∈ CFSG.solvableRadical ↥G := (commutator_mem_sol_iff x y).mp h1
  have h3 : QuotientGroup.mk' (CFSG.solvableRadical ↥G) ⁅x, y⁆ = 1 := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact h2
  rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h3
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hxa, ← hyb]
  exact h3

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.T516
