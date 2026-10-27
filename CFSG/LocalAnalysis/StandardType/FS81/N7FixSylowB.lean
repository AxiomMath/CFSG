module

public import CFSG.LocalAnalysis.StandardType.FS81.N7FixSylowN
import CFSG.LocalAnalysis.StandardType.FS81.N7FixGen

public section

namespace CFSG.StandardType.FrameRoute.FS81

open scoped Matrix

namespace N7Setup

variable {X : Type} [Group X] [Finite X] (S : N7Setup X)

theorem conj_E6_mem {τ : X} (hτ : S.ρ τ ∈ E6set) {x : X} (hx : x * τ * x⁻¹ ∈ S.H) :
    S.ρ (x * τ * x⁻¹) ∈ E6set := by
  have hτ' := hτ
  obtain ⟨T, h0, hT, hτT⟩ := hτ'
  have h2 : S.ρ τ * S.ρ τ = 1 := by rw [hτT]; exact q2nN7_sgn_mul_self T
  have hM : S.ρ (x * τ * x⁻¹) ∈ evenFix0 7 := (S.mem_H_iff _).1 hx
  have hττ : τ * τ = 1 := S.ρ_inj (by rw [map_mul, map_one, h2])
  have hsq : S.ρ (x * τ * x⁻¹) * S.ρ (x * τ * x⁻¹) = 1 := by
    rw [← map_mul]
    have e : x * τ * x⁻¹ * (x * τ * x⁻¹) = x * (τ * τ) * x⁻¹ := by group
    rw [e, hττ, mul_one, mul_inv_cancel, map_one]
  have h9 : fixCount (S.ρ (x * τ * x⁻¹)) = 9 := by
    have hconj : S.ρ (x * τ * x⁻¹) = S.ρ x * S.ρ τ * S.ρ x⁻¹ := by rw [map_mul, map_mul]
    rw [hconj, fixCount_conj (g := S.ρ x) (g' := S.ρ x⁻¹)
      (by rw [← map_mul, mul_inv_cancel, map_one]) (by rw [← map_mul, inv_mul_cancel, map_one])]
    exact fixCount_of_mem_E6set hτ
  exact mem_E6set_of_fixCount hM hsq h9

theorem q2nN7_F1_normal : (S.F1.subgroupOf S.H).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  exact S.conj_mem_F1 g.2 hn

theorem q2nN7_F1_isPGroup : IsPGroup 2 S.F1 := by
  intro g
  refine ⟨1, ?_⟩
  apply Subtype.ext
  show (g : X) ^ 2 ^ 1 = 1
  rw [pow_one, pow_two]
  exact S.F1_sq g.2

theorem q2nN7_F1_weakly_closed :
    ∀ y : X, (∀ f ∈ S.F1, y * f * y⁻¹ ∈ S.H) → ∀ f ∈ S.F1, y * f * y⁻¹ ∈ S.F1 := by
  intro y hy f hf
  refine Subgroup.closure_induction (p := fun f _ => y * f * y⁻¹ ∈ S.F1) ?_ ?_ ?_ ?_ hf
  · intro τ hτ
    exact Subgroup.subset_closure (S.conj_E6_mem hτ (hy τ (Subgroup.subset_closure hτ)))
  · simp
  · intro a b _ _ ha hb
    have e : y * (a * b) * y⁻¹ = (y * a * y⁻¹) * (y * b * y⁻¹) := by group
    rw [e]
    exact mul_mem ha hb
  · intro a _ ha
    have e : y * a⁻¹ * y⁻¹ = (y * a * y⁻¹)⁻¹ := by group
    rw [e]
    exact inv_mem ha

theorem exists_sylow_le_H : ∃ P : Sylow 2 X, (P : Subgroup X) ≤ S.H :=
  q2nN7_exists_sylow_le S.H S.F1 S.F1_le_H S.q2nN7_F1_normal S.q2nN7_F1_isPGroup
    (S.normalizer_F1).le S.q2nN7_F1_weakly_closed

theorem F1_le_sylow {P : Sylow 2 X} (hPH : (P : Subgroup X) ≤ S.H) : S.F1 ≤ P :=
  q2nN7_le_sylow_of_normal S.F1_le_H S.q2nN7_F1_normal S.q2nN7_F1_isPGroup P hPH

end N7Setup

end CFSG.StandardType.FrameRoute.FS81

end
