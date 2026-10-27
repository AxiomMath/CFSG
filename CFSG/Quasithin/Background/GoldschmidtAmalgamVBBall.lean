module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamVBOmega
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3RLab

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL

namespace F6

namespace GoldAmL3

variable {D : Type*} [Group D] [Finite D] {A B : Subgroup D} {z : D} {V : Subgroup D}

namespace GoldHyp3

variable (h : GoldHyp3 A B z V)

include h

theorem ballStab_one_γ₀_eq : ballStab 1 (γ₀ (A ⊔ B) A B) = pCoreOf 2 A := by
  have hA : A ≤ A ⊔ B := le_sup_left
  have hB : B ≤ A ⊔ B := le_sup_right
  refine le_antisymm ?_ ?_
  · rw [ballStab_one_eq_coreIn rfl (adj_γ₀_γ₁ (G₀ := A ⊔ B) (G₁ := A) (G₂ := B)),
      stab_γ₀ hA, stab_γ₁ hB]
    exact le_pCoreOf_of_le_normalizer 2 (coreIn_le_left _ _) (le_normalizer_coreIn _ _)
      (h.gold.isSylowTwoOf_left.2.1.to_le (coreIn_le_right _ _))
  · have := pCoreOf_stab_le_ballStab_one h.gold.amalgamHyp (γ₀ (A ⊔ B) A B)
    rwa [stab_γ₀ hA] at this

theorem ballStab_one_γ₁_eq : ballStab 1 (γ₁ (A ⊔ B) A B) = pCoreOf 2 B := by
  have hA : A ≤ A ⊔ B := le_sup_left
  have hB : B ≤ A ⊔ B := le_sup_right
  refine le_antisymm ?_ ?_
  · rw [ballStab_one_eq_coreIn rfl (adj_γ₀_γ₁ (G₀ := A ⊔ B) (G₁ := A) (G₂ := B)).symm,
      stab_γ₀ hA, stab_γ₁ hB, inf_comm]
    exact le_pCoreOf_of_le_normalizer 2 (coreIn_le_left _ _) (le_normalizer_coreIn _ _)
      (h.gold.isSylowTwoOf_right.2.1.to_le (coreIn_le_right _ _))
  · have := pCoreOf_stab_le_ballStab_one h.gold.amalgamHyp (γ₁ (A ⊔ B) A B)
    rwa [stab_γ₁ hB] at this

theorem sq_mem_ballStab_one_of_adj {u v : CosetGeom (A ⊔ B) A B}
    (huv : (graph (A ⊔ B) A B).Adj u v) {x : D} (hxu : x ∈ stab u) (hxv : x ∈ stab v) :
    x * x ∈ ballStab 1 u := by
  cases hu : vtype u
  · obtain ⟨g, rfl, rfl⟩ := exists_smul_edge_AB huv hu
    rw [stab_smul, stab_γ₀ le_sup_left, mem_conjSub] at hxu
    rw [stab_smul, stab_γ₁ le_sup_right, mem_conjSub] at hxv
    rw [ballStab_smul, h.ballStab_one_γ₀_eq, mem_conjSub]
    have := mul_self_mem_of_relIndex_two h.gold.relIndex_pCoreOf_T_left
      (show (g : D)⁻¹ * x * g ∈ A ⊓ B from ⟨hxu, hxv⟩)
    have e : (g : D)⁻¹ * (x * x) * g = ((g : D)⁻¹ * x * g) * ((g : D)⁻¹ * x * g) := by group
    rw [e]
    exact this
  · have hv : vtype v = false := vtype_eq_false_of_adj huv hu
    obtain ⟨g, rfl, rfl⟩ := exists_smul_edge_AB huv.symm hv
    rw [stab_smul, stab_γ₁ le_sup_right, mem_conjSub] at hxu
    rw [stab_smul, stab_γ₀ le_sup_left, mem_conjSub] at hxv
    rw [ballStab_smul, h.ballStab_one_γ₁_eq, mem_conjSub]
    have := mul_self_mem_of_relIndex_two h.gold.relIndex_pCoreOf_T_right
      (show (g : D)⁻¹ * x * g ∈ A ⊓ B from ⟨hxv, hxu⟩)
    have e : (g : D)⁻¹ * (x * x) * g = ((g : D)⁻¹ * x * g) * ((g : D)⁻¹ * x * g) := by group
    rw [e]
    exact this

end GoldHyp3

end GoldAmL3

end F6

end CFSG.Quasithin
