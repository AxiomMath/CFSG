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

theorem sixFF_ff8_factor6 (hS : SCSetting L K n φ t i) (hH : SixHConclusion φ t i)
    (hE : EmbConclusion φ t i) (hK : SixKConclusion φ t i) (f7 : FF7Concl φ t i) :
    FF8FactorConcl n φ t i 5 := by
  intro v₀ hv2 hvC hvF hn h1 h0 _
  have hcard := ffTorus_card_K hS hn
  have hFC := hS.fc
  have hne := hS.ne_bot
  have hbot := hS.eq_bot
  obtain ⟨μ₀, f, g, hμJ, hμ, hχ, hfrob⟩ := ffTorus_exists_adapted_u φ (n := n)
    (by have := hS.fc.setup.two_le; omega) hS.fc.setup.card_K i
  obtain ⟨c₁, h₁⟩ := ffLayer_U φ i hμ hχ
  have hW := ffLayer_W φ hFC i hμJ h₁
  have hV := ffLayer_V φ hFC i hne hbot hμJ h₁
  obtain ⟨hμ'J, hfrob'⟩ := ffTorus_conj_w φ i.swap hμJ hv2 hvF (hfrob hv2 hvF)
  have h₁' := h₁.conj (w φ i.swap)⁻¹
  have hW' := hW.conj (w φ i.swap)⁻¹
  have hV' := hV.conj (w φ i.swap)⁻¹
  have hwinv : (w φ i.swap)⁻¹ = w φ i.swap := FullCenterWeyl.w_inv i.swap
  set μ' : Kˣ →* G := (MulAut.conj (w φ i.swap)⁻¹).toMonoidHom.comp μ₀ with hμ'
  set Y₁ : Subgroup G := (U φ i).map (MulAut.conj (w φ i.swap)⁻¹).toMonoidHom with hY₁
  set Y₂ : Subgroup G := (Wk φ t i).map (MulAut.conj (w φ i.swap)⁻¹).toMonoidHom with hY₂
  set Y₃ : Subgroup G := (Vtor φ t i i).map (MulAut.conj (w φ i.swap)⁻¹).toMonoidHom with hY₃
  obtain ⟨cY₂, hcY₂⟩ : ∃ c : G → K, ScalarLayer μ' Y₂ Y₁ c := ⟨_, hW'⟩
  obtain ⟨cY₃, hcY₃⟩ : ∃ c : G → K, ScalarLayer μ' Y₃ Y₂ c := ⟨_, hV'⟩
  have hY₁Y₂ : Y₁ ≤ Y₂ := Subgroup.map_mono (FullCenterTorus.U_le_W hFC i)
  have hY₂Y₃ : Y₂ ≤ Y₃ := Subgroup.map_mono (RootStandard.W_le_V hFC i hne hbot i)
  have hTD : Tplus φ t i ≤ normalizer (Dstar φ t i : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hH.normal_Dstar.1).mp hH.normal_Dstar.2.1
  have hTMhat : Tplus φ t i ≤ normalizer (Mhat φ t i i : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (hH.normal_Mhat i).1).mp (hH.normal_Mhat i).2.1
  have hST : S φ t i ≤ Tplus φ t i := by
    rw [← hH.sup_t]
    exact le_sup_left
  have hMhatk : ∀ k : Axis, Mhat φ t i k ≤ S φ t i := by
    intro k
    cases k
    · exact le_sup_left
    · exact le_sup_right
  have hY₃S : Y₃ ≤ S φ t i := by
    refine (Subgroup.map_mono (inf_le_left : Vtor φ t i i ≤ Mc φ t i)).trans ?_
    exact le_sup_right.trans (hMhatk i.swap)
  have hMD : Mhat φ t i i ≤ Dstar φ t i := le_sup_left
  have hDS : Dstar φ t i ≤ S φ t i := f7.2.1 5
  have hY₃T : Y₃ ≤ Tplus φ t i := hY₃S.trans hST
  have hY₃NM : Y₃ ≤ normalizer (Mhat φ t i i : Set G) := hY₃T.trans hTMhat
  have hY₃ND : Y₃ ≤ normalizer (Dstar φ t i : Set G) := hY₃T.trans hTD
  have hY₂ND : Y₂ ≤ normalizer (Dstar φ t i : Set G) := hY₂Y₃.trans hY₃ND
  have hY₁ND : Y₁ ≤ normalizer (Dstar φ t i : Set G) := hY₁Y₂.trans hY₂ND
  have hSprod : ∀ x ∈ S φ t i, ∃ m ∈ Mhat φ t i i, ∃ y ∈ Y₃, x = m * y := by
    intro x hx
    rw [← hE.sup_Vw] at hx
    have hx' : x ∈ ((Mhat φ t i i : Subgroup G) : Set G) * ((Y₃ : Subgroup G) : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left (Mhat φ t i i) Y₃ hY₃NM]
      exact hx
    obtain ⟨m, hm, y, hy, rfl⟩ := Set.mem_mul.mp hx'
    exact ⟨m, hm, y, hy, rfl⟩
  have hY₁D : Y₁ ≤ Dstar φ t i := by
    intro u hu
    have hu' : w φ i.swap * u * (w φ i.swap)⁻¹ ∈ U φ i := FullCenterWeyl.mem_map_conj_inv.mp hu
    have hA : u ∈ A φ i.swap := by
      have h1' := FullCenterWeyl.conj_w_mem_A hFC i.swap
        (pull_mono φ (center_le_rootA i.swap) (pull_mono φ (rootU_le_center i) hu'))
      have e : w φ i.swap * (w φ i.swap * u * (w φ i.swap)⁻¹) * (w φ i.swap)⁻¹ = u := by
        rw [hwinv]
        calc w φ i.swap * (w φ i.swap * u * w φ i.swap) * w φ i.swap
            = (w φ i.swap * w φ i.swap) * u * (w φ i.swap * w φ i.swap) := by group
          _ = u := by rw [FullCenterWeyl.w_mul_self, one_mul, mul_one]
      rwa [e] at h1'
    exact (le_sup_left.trans le_sup_right : A φ i.swap ≤ Dstar φ t i) hA
  have hDY : Dstar φ t i ⊓ Y₃ = Y₁ := by
    apply le_antisymm
    · have hBM : Dstar φ t i ⊓ Y₃ ≤ normalizer (Mhat φ t i i : Set G) := inf_le_right.trans hY₃NM
      have hMB : Mhat φ t i i ⊓ (Dstar φ t i ⊓ Y₃) = ⊥ := by
        rw [eq_bot_iff, ← hE.inf_Vw]
        exact inf_le_inf_left _ inf_le_right
      have hDeq : Dstar φ t i = Mhat φ t i i ⊔ (Dstar φ t i ⊓ Y₃) := by
        apply le_antisymm
        · intro d hd
          obtain ⟨m, hm, y, hy, rfl⟩ := hSprod d (hDS hd)
          have hyD : y ∈ Dstar φ t i := by
            have := (Dstar φ t i).mul_mem ((Dstar φ t i).inv_mem (hMD hm)) hd
            simpa using this
          exact mul_mem (mem_sup_left hm) (mem_sup_right (mem_inf.mpr ⟨hyD, hy⟩))
        · exact sup_le hMD inf_le_left
      have hc := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer
        (A := Mhat φ t i i) (B := Dstar φ t i ⊓ Y₃) hBM
      rw [← hDeq, hMB, card_bot, mul_one, hH.card_Dstar, SixF.card_Mhat hFC i hne hbot] at hc
      have hq : 0 < Nat.card K ^ 7 := pow_pos Nat.card_pos 7
      have hBq : Nat.card (Dstar φ t i ⊓ Y₃ : Subgroup G) = Nat.card K :=
        (Nat.eq_of_mul_eq_mul_left hq (by rw [← hc]; ring)).symm
      have hY₁c : Nat.card Y₁ = Nat.card K := by
        rw [hY₁, Subgroup.card_map_of_injective (MulAut.conj (w φ i.swap)⁻¹).injective,
          card_U φ i]
      exact (eq_of_le_of_card_ge (le_inf hY₁D (hY₁Y₂.trans hY₂Y₃)) (by rw [hBq, hY₁c])).ge
    · exact le_inf hY₁D (hY₁Y₂.trans hY₂Y₃)
  have hDY₂ : Dstar φ t i ⊓ Y₂ = Y₁ :=
    le_antisymm ((inf_le_inf_left _ hY₂Y₃).trans hDY.le) (le_inf hY₁D hY₁Y₂)
  obtain ⟨hWN, -⟩ := RootStandard.quotient_V hFC i hne hbot
  have hVNW : Vtor φ t i i ≤ normalizer (Wk φ t i : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (RootStandard.W_le_V hFC i hne hbot i)).mp hWN
  have hY₃NY₂ : Y₃ ≤ normalizer (Y₂ : Set G) := by
    rintro _ ⟨y, hy, rfl⟩
    exact ffTorus_normalizer_map_conj (hVNW hy) _
  have hY₃NC₁ : Y₃ ≤ normalizer ((Dstar φ t i ⊔ Y₂ : Subgroup G) : Set G) :=
    ffTorus_le_normalizer_sup hY₃ND hY₃NY₂
  have hC₁Y₃ : (Dstar φ t i ⊔ Y₂) ⊓ Y₃ = Y₂ := by
    apply le_antisymm
    · intro z hz
      obtain ⟨hzC, hzY⟩ := mem_inf.mp hz
      have hz' : z ∈ ((Dstar φ t i : Subgroup G) : Set G) * ((Y₂ : Subgroup G) : Set G) := by
        rw [← Subgroup.coe_mul_of_right_le_normalizer_left (Dstar φ t i) Y₂ hY₂ND]
        exact hzC
      obtain ⟨d, hd, u, hu, rfl⟩ := Set.mem_mul.mp hz'
      have hdY : d ∈ Y₃ := by
        have := Y₃.mul_mem hzY (Y₃.inv_mem (hY₂Y₃ hu))
        simpa using this
      have hd1 : d ∈ Dstar φ t i ⊓ Y₃ := mem_inf.mpr ⟨hd, hdY⟩
      rw [hDY] at hd1
      exact Y₂.mul_mem (hY₁Y₂ hd1) hu
    · exact le_inf le_sup_right hY₂Y₃
  have hμ'D : ∀ l, μ' l ∈ normalizer (Dstar φ t i : Set G) := fun l =>
    hH.normal_Dstar.2.2 (hμ'J l)
  have hμ'Y₂ : ∀ l, μ' l ∈ normalizer (Y₂ : Set G) := fun l =>
    ffTorus_normalizer_map_conj (X := Wk φ t i)
      (ffTorus_normalizer_of_conj (hμJ l)
        (fun g hg x hx => FullCenterTorus.conj_torus_mem_W hFC i hg hx)) (w φ i.swap)⁻¹
  have hμ'Y₃ : ∀ l, μ' l ∈ normalizer (Y₃ : Set G) := fun l =>
    ffTorus_normalizer_map_conj (X := Vtor φ t i i)
      (RootStandard.J_le_normalizer_V hFC i hne hbot i (hμJ l)) (w φ i.swap)⁻¹
  have hμ'C₁ : ∀ l, μ' l ∈ normalizer ((Dstar φ t i ⊔ Y₂ : Subgroup G) : Set G) := fun l =>
    ffTorus_le_normalizer_sup (zpowers_le.mpr (hμ'D l)) (zpowers_le.mpr (hμ'Y₂ l))
      (mem_zpowers _)
  have hμ'S : ∀ l, μ' l ∈ normalizer (S φ t i : Set G) := fun l =>
    ffTorus_le_normalizer_sup (zpowers_le.mpr ((hH.normal_Mhat Axis.one).2.2 (hμ'J l)))
      (zpowers_le.mpr ((hH.normal_Mhat Axis.two).2.2 (hμ'J l))) (mem_zpowers _)
  have hY₂S : Y₂ ≤ S φ t i := hY₂Y₃.trans hY₃S
  have hC₁S : Dstar φ t i ⊔ Y₂ ≤ S φ t i := sup_le hDS hY₂S
  obtain ⟨c₂, hc₂⟩ : ∃ c : G → K, ScalarLayer μ' (Dstar φ t i ⊔ Y₂) (Dstar φ t i) c := by
    refine ScalarLayer.of_sup (Y := Y₂) (cY := cY₂) le_sup_left le_sup_right (fun x hx => ?_)
      (fun y hy m hm => ?_) hμ'D hμ'Y₂ ?_
    · have hx' : x ∈ ((Dstar φ t i : Subgroup G) : Set G) * ((Y₂ : Subgroup G) : Set G) := by
        rw [← Subgroup.coe_mul_of_right_le_normalizer_left (Dstar φ t i) Y₂ hY₂ND]
        exact hx
      obtain ⟨m, hm, u, hu, rfl⟩ := Set.mem_mul.mp hx'
      exact ⟨m, hm, u, hu, rfl⟩
    · exact (mem_normalizer_iff.mp (hY₂ND hy) m).mp hm
    · rw [hDY₂]
      exact hcY₂
  obtain ⟨c₃, hc₃⟩ : ∃ c : G → K, ScalarLayer μ' (S φ t i) (Dstar φ t i ⊔ Y₂) c := by
    refine ScalarLayer.of_sup (Y := Y₃) (cY := cY₃) hC₁S hY₃S (fun x hx => ?_)
      (fun y hy m hm => ?_) hμ'C₁ hμ'Y₃ ?_
    · obtain ⟨m, hm, y, hy, rfl⟩ := hSprod x hx
      exact ⟨m, mem_sup_left (hMD hm), y, hy, rfl⟩
    · exact (mem_normalizer_iff.mp (hY₃NC₁ hy) m).mp hm
    · rw [hC₁Y₃]
      exact hcY₃
  haveI := (f7.2.2.1 5).choose_spec
  exact ffBridge_scalar_section_two hcard μ' hv2 hfrob' h1 h0 (Dstar φ t i ⊔ Y₂) le_sup_left hC₁S
    hμ'S hμ'C₁ hμ'D hc₂ hc₃

end Steps

end SingleCommParts

end CFSG.LocalAnalysis.SymplecticFourStandard
