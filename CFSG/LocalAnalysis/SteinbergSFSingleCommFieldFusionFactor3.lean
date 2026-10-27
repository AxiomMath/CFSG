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

theorem sixFF_ff8_factor3 (hS : SCSetting L K n φ t i) (hH : SixHConclusion φ t i)
    (hE : EmbConclusion φ t i) (hK : SixKConclusion φ t i) (f7 : FF7Concl φ t i) :
    FF8FactorConcl n φ t i 2 := by
  intro v₀ hv2 hvC hvF hn h1 h0 _
  have hcard := ffTorus_card_K hS hn
  have hFC := hS.fc
  have hne := hS.ne_bot
  have hbot := hS.eq_bot
  obtain ⟨μ, f, g, hμJ, hμ, hχ, hfrob⟩ := ffTorus_exists_adapted_u φ (n := n)
    (by have := hS.fc.setup.two_le; omega) hS.fc.setup.card_K i
  obtain ⟨c₁, h₁⟩ := ffLayer_U φ i hμ hχ
  have hW := ffLayer_W φ hFC i hμJ h₁
  have hV := ffLayer_V φ hFC i hne hbot hμJ h₁
  have hFcomm : ∀ x ∈ F φ t, ∀ y ∈ F φ t, x * y = y * x := fun x hx y hy =>
    FullCenterTorus.F_comm hFC hx hy
  have hswap : i.swap.swap = i := by cases i <;> rfl
  have hFjW : (F φ t ⊓ D φ t i.swap) ⊓ Wk φ t i = U φ i := by
    apply le_antisymm
    · rintro x ⟨hxF, hxW⟩
      have hx' : x ∈ ((Wk φ t i.swap : Subgroup G) : Set G) *
          ((U φ i.swap.swap : Subgroup G) : Set G) := by
        rw [FullCenterTorus.W_mul_U hFC i.swap]
        exact hxF
      obtain ⟨w, hw, u, hu, rfl⟩ := Set.mem_mul.mp hx'
      rw [hswap] at hu
      have huW : u ∈ Wk φ t i := FullCenterTorus.U_le_W hFC i hu
      have hwW : w ∈ Wk φ t i := by
        have := (Wk φ t i).mul_mem hxW ((Wk φ t i).inv_mem huW)
        simpa using this
      have hw1 : w ∈ Wk φ t i ⊓ Wk φ t i.swap := mem_inf.mpr ⟨hwW, hw⟩
      rw [RootStandard.W_inf_W_swap_eq hFC i, mem_bot] at hw1
      rw [hw1, one_mul]
      exact hu
    · intro u hu
      exact ⟨FullCenterTorus.ZP_le_Fi hFC i.swap (pull_mono φ (rootU_le_center i) hu),
        FullCenterTorus.U_le_W hFC i hu⟩
  have hF : ∃ c : G → K, ScalarLayer μ (F φ t) (F φ t ⊓ D φ t i.swap) c := by
    refine ScalarLayer.of_sup (Y := Wk φ t i) (cY := fun x => c₁ (t⁻¹ * (x⁻¹ * t * x)))
      inf_le_left (FullCenterTorus.W_le_F i) (fun x hx => ?_) (fun y hy m hm => ?_)
      (fun l => ?_) (fun l => ?_) ?_
    · have hx' : x ∈ Wk φ t i ⊔ Wk φ t i.swap := by
        rw [← RootStandard.F_eq_W_sup_W hFC i]
        exact hx
      obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_of_commute (fun x hx y hy =>
        hFcomm x (FullCenterTorus.W_le_F i hx) y (FullCenterTorus.W_le_F i.swap hy))).mp hx'
      exact ⟨b, FullCenterTorus.W_le_Fi hFC i.swap hb, a, ha,
        hFcomm a (FullCenterTorus.W_le_F i ha) b (FullCenterTorus.W_le_F i.swap hb)⟩
    · rw [hFcomm y (FullCenterTorus.W_le_F i hy) m (mem_inf.mp hm).1, mul_inv_cancel_right]
      exact hm
    · exact ffTorus_normalizer_of_conj (hμJ l) (fun g hg x hx => mem_inf.mpr
        ⟨FullCenterTorus.conj_torus_mem_F hFC hg (mem_inf.mp hx).1,
          FullCenterTorus.conj_torus_mem_D hFC i.swap hg (mem_inf.mp hx).2⟩)
    · exact ffTorus_normalizer_of_conj (hμJ l)
        (fun g hg x hx => FullCenterTorus.conj_torus_mem_W hFC i hg hx)
    · rw [hFjW]
      exact hW
  have hM : ∃ c : G → K, ScalarLayer μ (Mc φ t i) (F φ t) c := by
    refine ScalarLayer.of_sup (Y := Vtor φ t i i)
      (cY := fun x => c₁ ((t⁻¹ * (x⁻¹ * t * x)) * (t⁻¹ * (x⁻¹ * t * x))))
      (NextCores.F_le_M hFC i hne hbot) inf_le_left
      (fun x hx => RootStandard.exists_F_mul_V hFC i hne hbot hx) (fun y hy m hm => ?_)
      (fun l => FullCenterTorus.torus_le_normalizer_F hFC (hμJ l))
      (fun l => RootStandard.J_le_normalizer_V hFC i hne hbot i (hμJ l)) ?_
    · exact RootStandard.conj_M_mem_F hFC i hne hbot (mem_inf.mp hy).1 hm
    · have e : F φ t ⊓ Vtor φ t i i = Wk φ t i := by
        rw [inf_comm]
        exact RootStandard.V_inf_F hFC i hne hbot i
      rw [e]
      exact hV
  obtain ⟨c₂, hc₂⟩ := hF
  obtain ⟨c₃, hc₃⟩ := hM
  haveI := (f7.2.2.1 2).choose_spec
  refine ffBridge_scalar_section_two hcard μ hv2 (hfrob hv2 hvF) h1 h0 (F φ t) inf_le_left
    (NextCores.F_le_M hFC i hne hbot) ?_ ?_ ?_ hc₂ hc₃
  · intro l
    exact NextCores.J_le_normalizer_M hFC i hne hbot (hμJ l)
  · intro l
    exact FullCenterTorus.torus_le_normalizer_F hFC (hμJ l)
  · intro l
    exact ffTorus_normalizer_of_conj (hμJ l) (fun g hg x hx => mem_inf.mpr
      ⟨FullCenterTorus.conj_torus_mem_F hFC hg (mem_inf.mp hx).1,
        FullCenterTorus.conj_torus_mem_D hFC i.swap hg (mem_inf.mp hx).2⟩)

end Steps

end SingleCommParts

end CFSG.LocalAnalysis.SymplecticFourStandard
