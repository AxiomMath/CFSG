module

public import CFSG.LocalAnalysis.SteinbergSFSingleCommFieldFusionBridge

public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

namespace SingleCommParts

open Subgroup GomiFusion
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis RootAxisTwoCore FullCenter
open scoped Pointwise

section Steps

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {L : Subgroup G} {K : Type} [Field K]
  [CharP K 2] [Finite K] {n : ℕ} {φ : L ≃* antiSp K} {t : G} {i : Axis}

theorem sixFF_ff8_factor2 (hS : SCSetting L K n φ t i) (hH : SixHConclusion φ t i)
    (hE : EmbConclusion φ t i) (hK : SixKConclusion φ t i) (f7 : FF7Concl φ t i) :
    FF8FactorConcl n φ t i 1 := by
  intro v₀ hv2 hvC hvF hn h1 h0 _
  have hcard := ffTorus_card_K hS hn
  have hFC := hS.fc
  obtain ⟨μ, f, g, hμJ, hμ, hχ, hfrob⟩ := ffTorus_exists_adapted_u φ (n := n)
    (by have := hS.fc.setup.two_le; omega) hS.fc.setup.card_K i.swap
  obtain ⟨c₁, h₁⟩ := ffLayer_U φ i.swap hμ hχ
  have hW := ffLayer_W φ hFC i.swap hμJ h₁
  have hcomm : ∀ x ∈ Z₀ φ, ∀ z ∈ Z₀ φ, x * z = z * x := fun x hx z hz =>
    FullCenterTorus.comm_ZP hFC (FullCenterTorus.ZP_le_H hx) hz
  have hZ : ∃ c : G → K, ScalarLayer μ (Z₀ φ) (U φ i) c := by
    refine ScalarLayer.of_sup (Y := U φ i.swap) (cY := c₁) (pull_mono φ (rootU_le_center i))
      (pull_mono φ (rootU_le_center i.swap)) (fun x hx => ?_) (fun y hy m hm => ?_)
      (fun l => ffLayer_U_normalizer φ i hμ l) (fun l => ffLayer_U_normalizer φ i.swap hμ l) ?_
    · obtain ⟨u, hu, v, hv, e⟩ := RootStandard.exists_U_mul_U i hx
      exact ⟨u, hu, v, hv, e⟩
    · rw [hcomm y (pull_mono φ (rootU_le_center i.swap) hy) m (pull_mono φ (rootU_le_center i) hm),
        mul_inv_cancel_right]
      exact hm
    · rw [FullCenterTorus.U_inf_U_swap]
      exact h₁
  have hswap : i.swap.swap = i := by cases i <;> rfl
  have hF : ∃ c : G → K, ScalarLayer μ (F φ t ⊓ D φ t i.swap) (Z₀ φ) c := by
    refine ScalarLayer.of_sup (Y := Wk φ t i.swap)
      (cY := fun x => c₁ (t⁻¹ * (x⁻¹ * t * x))) (FullCenterTorus.ZP_le_Fi hFC i.swap)
      (FullCenterTorus.W_le_Fi hFC i.swap) (fun x hx => ?_) (fun y hy m hm => ?_)
      (fun l => ?_) (fun l => ?_) ?_
    · have hx' : x ∈ ((Wk φ t i.swap : Subgroup G) : Set G) *
          ((U φ i.swap.swap : Subgroup G) : Set G) := by
        rw [FullCenterTorus.W_mul_U hFC i.swap]
        exact hx
      obtain ⟨w, hw, u, hu, rfl⟩ := Set.mem_mul.mp hx'
      rw [hswap] at hu
      have huZ : u ∈ Z₀ φ := pull_mono φ (rootU_le_center i) hu
      refine ⟨u, huZ, w, hw, ?_⟩
      exact FullCenterTorus.comm_ZP hFC
        ((FullCenterTorus.W_le_F i.swap).trans (FullCenterTorus.F_le_H hFC) hw) huZ
    · rw [FullCenterTorus.comm_ZP hFC
        ((FullCenterTorus.W_le_F i.swap).trans (FullCenterTorus.F_le_H hFC) hy) hm,
        mul_inv_cancel_right]
      exact hm
    · exact ffTorus_normalizer_of_conj (hμJ l)
        (fun g hg x hx => FullCenterTorus.conj_torus_mem_ZP hg hx)
    · exact ffTorus_normalizer_of_conj (hμJ l)
        (fun g hg x hx => FullCenterTorus.conj_torus_mem_W hFC i.swap hg hx)
    · have e : Z₀ φ ⊓ Wk φ t i.swap = U φ i.swap := by
        rw [inf_comm]
        exact FullCenterTorus.W_inf_ZP hFC i.swap
      rw [e]
      exact hW
  obtain ⟨c₂, hc₂⟩ := hZ
  obtain ⟨c₃, hc₃⟩ := hF
  haveI := (f7.2.2.1 1).choose_spec
  refine ffBridge_scalar_section_two hcard μ hv2 (hfrob hv2 hvF) h1 h0 (Z₀ φ) ?_ ?_ ?_ ?_ ?_
    hc₂ hc₃
  · exact pull_mono φ (rootU_le_center i)
  · exact FullCenterTorus.ZP_le_Fi hFC i.swap
  · intro l
    exact ffTorus_normalizer_of_conj (hμJ l) (fun g hg x hx => mem_inf.mpr
      ⟨FullCenterTorus.conj_torus_mem_F hFC hg (mem_inf.mp hx).1,
        FullCenterTorus.conj_torus_mem_D hFC i.swap hg (mem_inf.mp hx).2⟩)
  · intro l
    exact ffTorus_normalizer_of_conj (hμJ l)
      (fun g hg x hx => FullCenterTorus.conj_torus_mem_ZP hg hx)
  · intro l
    exact ffLayer_U_normalizer φ i hμ l

end Steps

end SingleCommParts

end CFSG.LocalAnalysis.SymplecticFourStandard
