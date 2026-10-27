module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenTwelveA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenGlue2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem s15_Twelve_conjSubgroup_sup (A B : Subgroup G) (g : G) :
    conjSubgroup (A ⊔ B) g = conjSubgroup A g ⊔ conjSubgroup B g := by
  unfold conjSubgroup
  exact Subgroup.map_sup _ _ _

theorem s15_Twelve_nine_core (D : Data G) {V₀ V L : Subgroup G} (h : Hyp154 D V₀ V L)
    (hV : IsElemAbelian 2 V) (hL : barSub V₀ V hV L ≠ ⊥) {g : G}
    (hBM : conjSubgroup (wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L) g ≤ D.M)
    (hBW : conjSubgroup (wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L) g ≤
      normalizer (wSub V₀ V hV L : Set G))
    (hWg : ¬ wSub V₀ V hV L ≤ conjSubgroup D.M g) : False := by
  have h151 : Hyp151 D V₀ V L := h.hyp151
  have h125 : Hyp125 D V₀ V := h151.hyp125
  have hWV : wSub V₀ V hV L ≤ V := preTil_le V₀ V hV _
  obtain ⟨B, hBdef⟩ : ∃ B : Subgroup G,
      B = conjSubgroup (wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L) g := ⟨_, rfl⟩
  have hBM' : B ≤ D.M := hBdef ▸ hBM
  have hBW' : B ≤ normalizer (wSub V₀ V hV L : Set G) := hBdef ▸ hBW
  have hVg : ¬ V ≤ conjSubgroup D.M g := fun hVg => hWg (hWV.trans hVg)
  have hBV0 : B ⊓ V = ⊥ := hBdef ▸ s15_Glue_inf_V_eq_bot D h hV hVg
  have hMs : D.M ≤ stabTil (v1Sub D.M V₀ V hV L) V :=
    le_stabTil h125.pairFacts.le_normalizer (s15_Infra_le_normalizer_v1Sub h125 hV)
  have hBs : B ≤ stabTil (v1Sub D.M V₀ V hV L) V := hBM'.trans hMs
  have hS : gamma15 D.M V₀ V hV L ≤
      rk ↥(autSub (barSub (v1Sub D.M V₀ V hV L) V hV B) (wStar D.M V₀ V hV L)) := by
    have hst : barSub (v1Sub D.M V₀ V hV L) V hV B ≤ stabSub (wStar D.M V₀ V hV L) :=
      s15_LP_barSub_le_stabSub_imgTil hV hBs hBW'
    rw [s15_LP_rk_autSub_eq_mQuot hst]
    have hCB : barSub (v1Sub D.M V₀ V hV L) V hV B ⊓ centSub (wStar D.M V₀ V hV L) ≤
        barSub (v1Sub D.M V₀ V hV L) V hV B := inf_le_left
    rw [s15_LP_mQuot_barSub_preBarSub hV hBs hCB]
    obtain ⟨E, hEdef⟩ : ∃ E : Subgroup G, E = preBarSub B (v1Sub D.M V₀ V hV L) V hV
        (barSub (v1Sub D.M V₀ V hV L) V hV B ⊓ centSub (wStar D.M V₀ V hV L)) := ⟨_, rfl⟩
    rw [← hEdef]
    have hEB : E ≤ B := hEdef ▸ inf_le_left
    have hfix : ∀ e ∈ E, ∀ w ∈ wSub V₀ V hV L, e * w * e⁻¹ * w⁻¹ ∈ v1Sub D.M V₀ V hV L := by
      intro e he w hw
      obtain ⟨-, hes, hmem⟩ := (mem_preBarSub B _ V hV _).1 (hEdef ▸ he)
      have hwV : w ∈ V := hWV hw
      have hwm : mkTil (v1Sub D.M V₀ V hV L) V hV (IntMod.mk hV ⟨w, hwV⟩) ∈
          wStar D.M V₀ V hV L :=
        (mem_imgTil _ V hV (wSub V₀ V hV L) _).2 ⟨IntMod.mk hV ⟨w, hwV⟩, hw, rfl⟩
      have := (mem_centSub.1 (Subgroup.mem_inf.1 hmem).2) _ hwm
      rw [actTil_mk, mkTil_eq_iff, actStab_apply_val] at this
      exact this
    have hδ : mSub E ≤ delta15 D.M V₀ V hV L :=
      s15_Tools_mSub_le_delta D h hV hBdef hEB (hEB.trans hBW') hfix hWg
    have hδ₁ : delta15 D.M V₀ V hV L ≤ rk ↥(v1Sub D.M V₀ V hV L) :=
      rk_mono (inf_le_left : v1Sub D.M V₀ V hV L ⊓ wSub V₀ V hV L ≤ v1Sub D.M V₀ V hV L)
    have h1 := s15_Tools_mQuot_le_add (B := B) (D := E) (C := ⊥) hEB
    have h2 := s15_FiveTen_mQuot_conj_bot (L := L) D h125 hV g
    rw [← hBdef] at h2
    rw [inf_bot_eq, h2] at h1
    have e1 := s15_FiveTen_mQuot_bot_eq_rk (v1Sub D.M V₀ V hV L)
    have e2 := s15_FiveTen_mQuot_bot_eq_rk E
    have h3 : mSub E = rk ↥E := rfl
    omega
  have hQ : ∀ E : Subgroup G, E ≤ B → E3.mQuot B E < gamma15 D.M V₀ V hV L →
      wSub V₀ V hV L ⊓ preTil (v1Sub D.M V₀ V hV L) V hV
        (fixV (barSub (v1Sub D.M V₀ V hV L) V hV E)) ≤ conjSubgroup D.M g := by
    intro E hEB hm x hx
    obtain ⟨hxW, hxfix⟩ := hx
    have hfix := (s15_Glue_mem_preTil_fixV_iff (v1Sub D.M V₀ V hV L) V E hV
      (hEB.trans hBs) (hWV hxW)).1 hxfix
    exact s15_Tools_mem_conj_of_mQuot_lt D h hV hBdef hBW' hEB hm hxW hfix
  have hR : ∀ Y : Subgroup G, Y ≤ wSub V₀ V hV L ⊓ conjSubgroup D.M g →
      B ≤ normalizer (Y : Set G) →
      ∃ N : Subgroup G, N ≤ Y ∧ B ≤ centralizer (N : Set G) ∧ E3.mQuot Y N ≤ 1 := by
    intro Y hY hBY
    have hYW : Y ≤ wSub V₀ V hV L := hY.trans inf_le_left
    have hYM : Y ≤ conjSubgroup D.M g := hY.trans inf_le_right
    have hY2 : IsPGroup 2 Y := hV.isPGroup.to_le (hYW.trans hWV)
    have hcommY : ∀ a ∈ B, ∀ y ∈ Y, a * y * a⁻¹ * y⁻¹ ∈ Y := fun a ha y hy =>
      Y.mul_mem ((Subgroup.mem_normalizer_iff.1 (hBY ha) y).1 hy) (Y.inv_mem hy)
    by_cases hs2 : s15 D.M V₀ V hV L = 2
    · refine ⟨Y ⊓ normalizer (B : Set G), inf_le_left, ?_,
        s15_Glue2_mQuot_inf_normalizer_le_one D h151 hV hBdef hYM hY2 hs2⟩
      intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      obtain ⟨hyY, hyB⟩ := Subgroup.mem_inf.1 hy
      have hcB : a * y * a⁻¹ * y⁻¹ ∈ B := by
        have h1 : y * a⁻¹ * y⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.1 hyB a⁻¹).1 (B.inv_mem ha)
        have h2 : a * y * a⁻¹ * y⁻¹ = a * (y * a⁻¹ * y⁻¹) := by group
        rw [h2]
        exact B.mul_mem ha h1
      have hc1 : a * y * a⁻¹ * y⁻¹ ∈ B ⊓ V :=
        Subgroup.mem_inf.2 ⟨hcB, hWV (hYW (hcommY a ha y hyY))⟩
      rw [hBV0] at hc1
      have hc2 : a * y * a⁻¹ * y⁻¹ = 1 := Subgroup.mem_bot.1 hc1
      calc y * a = (a * y * a⁻¹ * y⁻¹)⁻¹ * (a * y) := by group
        _ = a * y := by rw [hc2, inv_one, one_mul]
    · refine ⟨Y, le_rfl, ?_, ?_⟩
      · intro a ha
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        have hsd : ¬ (s15 D.M V₀ V hV L = 2 ∧
            delta15 D.M V₀ V hV L < gamma15 D.M V₀ V hV L - 1) := fun hh => hs2 hh.1
        have hc2 : a * y * a⁻¹ * y⁻¹ = 1 :=
          s15_Glue2_comm_eq_one D h hV hBdef hVg hsd ha (hYM hy)
            (Subgroup.mem_sup_left (hYW (hcommY a ha y hy)))
        calc y * a = (a * y * a⁻¹ * y⁻¹)⁻¹ * (a * y) := by group
          _ = a * y := by rw [hc2, inv_one, one_mul]
      · rw [(E3.mQuot_eq_zero_iff hY2 le_rfl).2 rfl]
        exact Nat.zero_le 1
  have hγ : 0 < gamma15 D.M V₀ V hV L := by
    have := two_le_gamma15 D h151 hV hL
    omega
  exact fifteen_nine_lp D h151 hV hγ hBdef hBM' hBW' hS hQ hR

theorem s15_Twelve_whole (D : Data G) (h1217 : R1217 D) {V₀ V L : Subgroup G}
    (h : Hyp154 D V₀ V L) (hV : IsElemAbelian 2 V) (hL : barSub V₀ V hV L ≠ ⊥) {n : ℕ} {k : G}
    (hk : Cond1512 n D.M V k) {X : Subgroup G} (hX : X ∈ wConj D.M V₀ V hV L)
    (hin : conjSubgroup (fSub15 D.M V₀ V hV L X) k ≤ D.M)
    (hc : E3.mQuot V (centralizer (ySub15 D.M V₀ V hV L X k : Set G)) < gamma15 D.M V₀ V hV L) :
    False := by
  have h151 : Hyp151 D V₀ V L := h.hyp151
  have hWV : wSub V₀ V hV L ≤ V := preTil_le V₀ V hV _
  have hMN : D.M ≤ normalizer (v1Sub D.M V₀ V hV L : Set G) :=
    s15_Infra_le_normalizer_v1Sub h151.hyp125 hV
  have hVk : ¬ V ≤ conjSubgroup D.M k := hk.2.1
  obtain ⟨Z, hZ, hZk⟩ : ∃ Z ∈ wConj D.M V₀ V hV L, ¬ Z ≤ conjSubgroup D.M k := by
    by_contra hcon
    apply hVk
    rw [← iSup_wConj_eq D h1217 h151 hV hL]
    refine iSup₂_le fun Z hZ => ?_
    by_contra hZk
    exact hcon ⟨Z, hZ, hZk⟩
  obtain ⟨m, hm, rfl⟩ := hX
  obtain ⟨m', hm', rfl⟩ := hZ
  have hYeq : ySub15 D.M V₀ V hV L (conjSubgroup (wSub V₀ V hV L) m) k =
      conjSubgroup (fSub15 D.M V₀ V hV L (conjSubgroup (wSub V₀ V hV L) m)) k :=
    inf_eq_left.2 hin
  obtain ⟨-, hfixZ⟩ := s15_Twelve_fixes D h1217 h151 hV hL
    (Y := ySub15 D.M V₀ V hV L (conjSubgroup (wSub V₀ V hV L) m) k) inf_le_right hc
    (Z := conjSubgroup (wSub V₀ V hV L) m') ⟨m', hm', rfl⟩
  rw [hYeq] at hfixZ
  have hV1m : conjSubgroup (v1Sub D.M V₀ V hV L) m = v1Sub D.M V₀ V hV L :=
    conjSubgroup_eq_iff_mem_normalizer.mpr (hMN hm)
  have hFconj : fSub15 D.M V₀ V hV L (conjSubgroup (wSub V₀ V hV L) m) =
      conjSubgroup (wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L) m := by
    unfold fSub15
    rw [s15_Twelve_conjSubgroup_sup, hV1m]
  have hFk : conjSubgroup (fSub15 D.M V₀ V hV L (conjSubgroup (wSub V₀ V hV L) m)) k =
      conjSubgroup (wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L) (m * k) := by
    rw [hFconj, conjSubgroup_conjSubgroup]
  rw [hFk] at hin hfixZ
  let g' : G := m * k * m'⁻¹
  have hBM : conjSubgroup (wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L) g' ≤ D.M := by
    have h1 := E3.conjSubgroup_mono_left m'⁻¹ hin
    rw [conjSubgroup_conjSubgroup, s15_Tools_conjSubgroup_M D (D.M.inv_mem hm')] at h1
    exact h1
  have hBW : conjSubgroup (wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L) g' ≤
      normalizer (wSub V₀ V hV L : Set G) := by
    have h1 := E3.conjSubgroup_mono_left m'⁻¹ hfixZ
    rw [conjSubgroup_conjSubgroup, E3.conjSubgroup_normalizer, conjSubgroup_conjSubgroup,
      mul_inv_cancel, conjSubgroup_one] at h1
    exact h1
  have hWg : ¬ wSub V₀ V hV L ≤ conjSubgroup D.M g' := by
    intro hle
    apply hZk
    have h1 : conjSubgroup (wSub V₀ V hV L) m' ≤ conjSubgroup (conjSubgroup D.M g') m' :=
      (E3.conjSubgroup_le_conjSubgroup_iff m').2 hle
    rw [conjSubgroup_conjSubgroup] at h1
    have h2 : g' * m' = m * k := by
      show m * k * m'⁻¹ * m' = m * k
      group
    rw [h2, ← conjSubgroup_conjSubgroup, s15_Tools_conjSubgroup_M D hm] at h1
    exact h1
  exact s15_Twelve_nine_core D h hV hL hBM hBW hWg

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
