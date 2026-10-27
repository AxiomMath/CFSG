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

theorem sixFF_ff8_factor4 (hS : SCSetting L K n φ t i) (hH : SixHConclusion φ t i)
    (hE : EmbConclusion φ t i) (hK : SixKConclusion φ t i) (f7 : FF7Concl φ t i) :
    FF8FactorConcl n φ t i 3 := by
  intro v₀ hv2 hvC hvF hn h1 h0 _
  have hcard := ffTorus_card_K hS hn
  have hFC := hS.fc
  have hne := hS.ne_bot
  have hbot := hS.eq_bot
  obtain ⟨μ₀, f, g, hμJ, hμ, hχ, hfrob⟩ := ffTorus_exists_adapted_u φ (n := n)
    (by have := hS.fc.setup.two_le; omega) hS.fc.setup.card_K i.swap
  obtain ⟨c₁, h₁⟩ := ffLayer_U φ i.swap hμ hχ
  have hW := ffLayer_W φ hFC i.swap hμJ h₁
  obtain ⟨hμ'J, hfrob'⟩ := ffTorus_conj_w φ i hμJ hv2 hvF (hfrob hv2 hvF)
  have h₁' := h₁.conj (w φ i)⁻¹
  have hW' := hW.conj (w φ i)⁻¹
  rw [Subgroup.map_bot] at h₁'
  have hw2 : w φ i * w φ i = 1 := FullCenterWeyl.w_mul_self i
  have hwinv : (w φ i)⁻¹ = w φ i := FullCenterWeyl.w_inv i
  have hVw : ∀ x ∈ Vtor φ t i i, w φ i * x * (w φ i)⁻¹ ∈ Vtor φ t i i := by
    intro x hx
    have hVeq : Vtor φ t i i = Mc φ t i ⊓ Mw φ t i i := (SixF.M_inf_Mw hFC i hne hbot).symm
    rw [hVeq] at hx ⊢
    obtain ⟨hxM, hxMw⟩ := mem_inf.mp hx
    refine mem_inf.mpr ⟨FullCenterWeyl.mem_map_conj_inv.mp hxMw, ?_⟩
    rw [FullCenterWeyl.mem_map_conj_inv]
    have e : w φ i * (w φ i * x * (w φ i)⁻¹) * (w φ i)⁻¹ = x := by
      rw [hwinv]
      calc w φ i * (w φ i * x * w φ i) * w φ i = (w φ i * w φ i) * x * (w φ i * w φ i) := by group
        _ = x := by rw [hw2, one_mul, mul_one]
    rw [e]
    exact hxM
  set μ' : Kˣ →* G := (MulAut.conj (w φ i)⁻¹).toMonoidHom.comp μ₀ with hμ'
  set Y₁ : Subgroup G := (U φ i.swap).map (MulAut.conj (w φ i)⁻¹).toMonoidHom with hY₁
  set Y₂ : Subgroup G := (Wk φ t i.swap).map (MulAut.conj (w φ i)⁻¹).toMonoidHom with hY₂
  have hY₂M : Y₂ ≤ Mw φ t i i := Subgroup.map_mono (RootStandard.W_le_M hFC i hne hbot _)
  have hY₁Y₂ : Y₁ ≤ Y₂ := Subgroup.map_mono (FullCenterTorus.U_le_W hFC i.swap)
  have hMY : Mc φ t i ⊓ Y₂ = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxM, hxY⟩ := mem_inf.mp hx
    have hxV : x ∈ Vtor φ t i i := by
      rw [show Vtor φ t i i = Mc φ t i ⊓ Mw φ t i i from (SixF.M_inf_Mw hFC i hne hbot).symm]
      exact mem_inf.mpr ⟨hxM, hY₂M hxY⟩
    have h2 := hVw x hxV
    have h3 : w φ i * x * (w φ i)⁻¹ ∈ Wk φ t i.swap := FullCenterWeyl.mem_map_conj_inv.mp hxY
    have h4 : w φ i * x * (w φ i)⁻¹ ∈ Vtor φ t i i ⊓ Wk φ t i.swap := mem_inf.mpr ⟨h2, h3⟩
    rw [RootStandard.V_inf_W_swap hFC i hne hbot, mem_bot] at h4
    have e : x = (w φ i)⁻¹ * (w φ i * x * (w φ i)⁻¹) * w φ i := by group
    rw [mem_bot, e, h4]
    group
  have hMY₁ : Mc φ t i ⊓ Y₁ = ⊥ := eq_bot_iff.mpr ((inf_le_inf_left _ hY₁Y₂).trans hMY.le)
  have hMhatDec : ∀ x ∈ Mhat φ t i i, ∃ m ∈ Mc φ t i, ∃ y ∈ Y₂, x = m * y := by
    intro x hx
    have hx' : x ∈ ((Mc φ t i : Subgroup G) : Set G) * ((Mw φ t i i : Subgroup G) : Set G) := by
      rw [SixF.M_mul_Mw hFC i hne hbot]
      exact hx
    obtain ⟨m, hm, z, hz, rfl⟩ := Set.mem_mul.mp hx'
    have hz' : w φ i * z * (w φ i)⁻¹ ∈ Mc φ t i := FullCenterWeyl.mem_map_conj_inv.mp hz
    obtain ⟨a, ha, b, hb, hab⟩ := RootStandard.exists_V_mul_W hFC i hne hbot hz'
    have hz_eq : z = ((w φ i)⁻¹ * a * w φ i) * ((w φ i)⁻¹ * b * w φ i) := by
      have e : z = (w φ i)⁻¹ * (w φ i * z * (w φ i)⁻¹) * w φ i := by group
      rw [e, hab]
      group
    have ha' : (w φ i)⁻¹ * a * w φ i ∈ Vtor φ t i i := by
      have := hVw a ha
      rw [hwinv] at this ⊢
      exact this
    have hb' : (w φ i)⁻¹ * b * w φ i ∈ Y₂ := by
      rw [hY₂, FullCenterWeyl.mem_map_conj_inv]
      have e : w φ i * ((w φ i)⁻¹ * b * w φ i) * (w φ i)⁻¹ = b := by group
      rw [e]
      exact hb
    refine ⟨m * ((w φ i)⁻¹ * a * w φ i), mul_mem hm ha'.1, (w φ i)⁻¹ * b * w φ i, hb', ?_⟩
    rw [hz_eq]
    group
  have hTM : Tplus φ t i ≤ normalizer (Mc φ t i : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hH.normal_M.1).mp hH.normal_M.2.1
  have hMhatT : Mhat φ t i i ≤ Tplus φ t i := (hH.normal_Mhat i).1
  have hY₂T : Y₂ ≤ Tplus φ t i := hY₂M.trans (le_sup_right.trans hMhatT)
  have hY₂NM : Y₂ ≤ normalizer (Mc φ t i : Set G) := hY₂T.trans hTM
  have hY₁NM : Y₁ ≤ normalizer (Mc φ t i : Set G) := hY₁Y₂.trans hY₂NM
  have hYY : ∀ y ∈ Y₂, ∀ u ∈ Y₁, y * u = u * y := by
    intro y hy u hu
    have hb : w φ i * y * (w φ i)⁻¹ ∈ Wk φ t i.swap := FullCenterWeyl.mem_map_conj_inv.mp hy
    have ha : w φ i * u * (w φ i)⁻¹ ∈ Wk φ t i.swap :=
      FullCenterTorus.U_le_W hFC i.swap (FullCenterWeyl.mem_map_conj_inv.mp hu)
    have hc := FullCenterTorus.F_comm hFC (FullCenterTorus.W_le_F _ hb) (FullCenterTorus.W_le_F _ ha)
    calc y * u = (w φ i)⁻¹ * ((w φ i * y * (w φ i)⁻¹) * (w φ i * u * (w φ i)⁻¹)) * w φ i := by
          group
      _ = (w φ i)⁻¹ * ((w φ i * u * (w φ i)⁻¹) * (w φ i * y * (w φ i)⁻¹)) * w φ i := by rw [hc]
      _ = u * y := by group
  have hY₂NY₁ : Y₂ ≤ normalizer (Y₁ : Set G) := fun y hy =>
    ffTorus_mem_normalizer_of_commute (fun u hu => hYY y hy u hu)
  have hY₂NC₁ : Y₂ ≤ normalizer ((Mc φ t i ⊔ Y₁ : Subgroup G) : Set G) :=
    ffTorus_le_normalizer_sup hY₂NM hY₂NY₁
  have hC₁Y₂ : (Mc φ t i ⊔ Y₁) ⊓ Y₂ = Y₁ := by
    apply le_antisymm
    · intro z hz
      obtain ⟨hzC, hzY⟩ := mem_inf.mp hz
      have hz' : z ∈ ((Mc φ t i : Subgroup G) : Set G) * ((Y₁ : Subgroup G) : Set G) := by
        rw [← Subgroup.coe_mul_of_right_le_normalizer_left (Mc φ t i) Y₁ hY₁NM]
        exact hzC
      obtain ⟨m, hm, u, hu, rfl⟩ := Set.mem_mul.mp hz'
      have hmY : m ∈ Y₂ := by
        have := Y₂.mul_mem hzY (Y₂.inv_mem (hY₁Y₂ hu))
        simpa using this
      have hm1 : m ∈ Mc φ t i ⊓ Y₂ := mem_inf.mpr ⟨hm, hmY⟩
      rw [hMY, mem_bot] at hm1
      rw [hm1, one_mul]
      exact hu
    · exact le_inf le_sup_right hY₁Y₂
  have hμ'M : ∀ l, μ' l ∈ normalizer (Mc φ t i : Set G) := fun l => hH.normal_M.2.2 (hμ'J l)
  have hμ'Y₁ : ∀ l, μ' l ∈ normalizer (Y₁ : Set G) := fun l =>
    ffTorus_normalizer_map_conj (ffLayer_U_normalizer φ i.swap hμ l) (w φ i)⁻¹
  have hμ'Y₂ : ∀ l, μ' l ∈ normalizer (Y₂ : Set G) := fun l =>
    ffTorus_normalizer_map_conj (X := Wk φ t i.swap)
      (ffTorus_normalizer_of_conj (hμJ l)
        (fun g hg x hx => FullCenterTorus.conj_torus_mem_W hFC i.swap hg hx)) (w φ i)⁻¹
  have hμ'C₁ : ∀ l, μ' l ∈ normalizer ((Mc φ t i ⊔ Y₁ : Subgroup G) : Set G) := fun l =>
    ffTorus_le_normalizer_sup (zpowers_le.mpr (hμ'M l)) (zpowers_le.mpr (hμ'Y₁ l))
      (mem_zpowers _)
  obtain ⟨cY₁, hcY₁⟩ : ∃ c : G → K, ScalarLayer μ' Y₁ ⊥ c := ⟨_, h₁'⟩
  obtain ⟨cY₂, hcY₂⟩ : ∃ c : G → K, ScalarLayer μ' Y₂ Y₁ c := ⟨_, hW'⟩
  obtain ⟨c₂, hc₂⟩ : ∃ c : G → K, ScalarLayer μ' (Mc φ t i ⊔ Y₁) (Mc φ t i) c := by
    refine ScalarLayer.of_sup (Y := Y₁) (cY := cY₁) le_sup_left le_sup_right (fun x hx => ?_)
      (fun y hy m hm => ?_) hμ'M hμ'Y₁ ?_
    · have hx' : x ∈ ((Mc φ t i : Subgroup G) : Set G) * ((Y₁ : Subgroup G) : Set G) := by
        rw [← Subgroup.coe_mul_of_right_le_normalizer_left (Mc φ t i) Y₁ hY₁NM]
        exact hx
      obtain ⟨m, hm, u, hu, rfl⟩ := Set.mem_mul.mp hx'
      exact ⟨m, hm, u, hu, rfl⟩
    · exact (mem_normalizer_iff.mp (hY₁NM hy) m).mp hm
    · rw [hMY₁]
      exact hcY₁
  obtain ⟨c₃, hc₃⟩ : ∃ c : G → K, ScalarLayer μ' (Mhat φ t i i) (Mc φ t i ⊔ Y₁) c := by
    refine ScalarLayer.of_sup (Y := Y₂) (cY := cY₂)
      (sup_le le_sup_left (hY₁Y₂.trans (hY₂M.trans le_sup_right))) (hY₂M.trans le_sup_right)
      (fun x hx => ?_) (fun y hy m hm => ?_) hμ'C₁ hμ'Y₂ ?_
    · obtain ⟨m, hm, y, hy, rfl⟩ := hMhatDec x hx
      exact ⟨m, mem_sup_left hm, y, hy, rfl⟩
    · exact (mem_normalizer_iff.mp (hY₂NC₁ hy) m).mp hm
    · rw [hC₁Y₂]
      exact hcY₂
  haveI := (f7.2.2.1 3).choose_spec
  refine ffBridge_scalar_section_two hcard μ' hv2 hfrob' h1 h0 (Mc φ t i ⊔ Y₁) le_sup_left
    (sup_le le_sup_left (hY₁Y₂.trans (hY₂M.trans le_sup_right))) ?_ hμ'C₁ hμ'M hc₂ hc₃
  intro l
  exact (hH.normal_Mhat i).2.2 (hμ'J l)

end Steps

end SingleCommParts

end CFSG.LocalAnalysis.SymplecticFourStandard
