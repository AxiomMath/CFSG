module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenResults
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenGlue
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenGlue2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenTools
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenFiveTen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenTwo
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenNineLP
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs15

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem s15_Nine_exists_conj (D : Data G) (h1217 : R1217 D) {V₀ V L : Subgroup G}
    (h : Hyp154 D V₀ V L) (hV : IsElemAbelian 2 V) (hL : barSub V₀ V hV L ≠ ⊥) {g : G}
    (hVg : ¬ V ≤ conjSubgroup D.M g) :
    ∃ m ∈ D.M, ¬ wSub V₀ V hV L ≤ conjSubgroup D.M (g * m⁻¹) := by
  by_contra hcon
  push Not at hcon
  apply hVg
  rw [← iSup_wConj_eq D h1217 h.hyp151 hV hL]
  refine iSup₂_le fun X hX => ?_
  obtain ⟨m, hm, rfl⟩ := hX
  have h1 := E3.conjSubgroup_mono_left m (hcon m hm)
  rwa [conjSubgroup_conjSubgroup, inv_mul_cancel_right] at h1

theorem s15_Nine_core (D : Data G) {V₀ V L : Subgroup G} (h : Hyp154 D V₀ V L)
    (hV : IsElemAbelian 2 V) (hL : barSub V₀ V hV L ≠ ⊥)
    (h158 : E3.wClos V 0 D.M ≤ normalizer (wSub V₀ V hV L : Set G)) {g : G}
    (hgM : conjSubgroup V g ≤ D.M) (hWg : ¬ wSub V₀ V hV L ≤ conjSubgroup D.M g) : False := by
  have h151 : Hyp151 D V₀ V L := h.hyp151
  have h125 : Hyp125 D V₀ V := h151.hyp125
  have hWV : wSub V₀ V hV L ≤ V := preTil_le V₀ V hV _
  have hWV₁ : wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L ≤ V :=
    sup_le hWV (s15_Infra_v1Sub_le h125 hV)
  obtain ⟨B, hBdef⟩ : ∃ B : Subgroup G,
      B = conjSubgroup (wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L) g := ⟨_, rfl⟩
  have hBV : B ≤ conjSubgroup V g := hBdef ▸ E3.conjSubgroup_mono_left g hWV₁
  have hBM : B ≤ D.M := hBV.trans hgM
  have hVg : ¬ V ≤ conjSubgroup D.M g := fun hVg => hWg (hWV.trans hVg)
  have hBV0 : B ⊓ V = ⊥ := hBdef ▸ s15_Glue_inf_V_eq_bot D h hV hVg
  have hVgP : IsPGroup 2 (conjSubgroup V g) := (E3.isElemAbelian_conjSubgroup hV g).isPGroup
  have hBW : B ≤ normalizer (wSub V₀ V hV L : Set G) := by
    refine hBV.trans (le_trans ?_ h158)
    have hmem : conjSubgroup V g ∈ E3.gammaSet V 0 D.M :=
      ⟨hgM, g, le_rfl, (E3.mQuot_eq_zero_iff hVgP le_rfl).2 rfl⟩
    exact le_iSup₂ (f := fun A (_ : A ∈ E3.gammaSet V 0 D.M) => A) _ hmem
  have hMs : D.M ≤ stabTil (v1Sub D.M V₀ V hV L) V :=
    le_stabTil h125.pairFacts.le_normalizer (s15_Infra_le_normalizer_v1Sub h125 hV)
  have hBs : B ≤ stabTil (v1Sub D.M V₀ V hV L) V := hBM.trans hMs
  have hS : gamma15 D.M V₀ V hV L ≤
      rk ↥(autSub (barSub (v1Sub D.M V₀ V hV L) V hV B) (wStar D.M V₀ V hV L)) := by
    have hst : barSub (v1Sub D.M V₀ V hV L) V hV B ≤ stabSub (wStar D.M V₀ V hV L) :=
      s15_LP_barSub_le_stabSub_imgTil hV hBs hBW
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
      s15_Tools_mSub_le_delta D h hV hBdef hEB (hEB.trans hBW) hfix hWg
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
    exact s15_Tools_mem_conj_of_mQuot_lt D h hV hBdef hBW hEB hm hxW hfix
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
  exact fifteen_nine_lp D h151 hV hγ hBdef hBM hBW hS hQ hR

theorem s15_Nine_le_conj (D : Data G) (h1217 : R1217 D) {V₀ V L : Subgroup G}
    (h : Hyp154 D V₀ V L) (hV : IsElemAbelian 2 V) (hL : barSub V₀ V hV L ≠ ⊥)
    (h158 : E3.wClos V 0 D.M ≤ normalizer (wSub V₀ V hV L : Set G)) {g : G}
    (hgM : conjSubgroup V g ≤ D.M) : V ≤ conjSubgroup D.M g := by
  by_contra hVg
  obtain ⟨m, hm, hWm⟩ := s15_Nine_exists_conj D h1217 h hV hL hVg
  refine s15_Nine_core D h hV hL h158 (g := g * m⁻¹) ?_ hWm
  rw [← conjSubgroup_conjSubgroup]
  have h1 := E3.conjSubgroup_mono_left m⁻¹ hgM
  rwa [s15_Tools_conjSubgroup_M D (D.M.inv_mem hm)] at h1

theorem fifteen_nine (D : Data G) (h1217 : R1217 D) (h156 : R15_6 D) (h158 : R15_8 D) :
    R15_9 D := by
  intro V₀ V L h hL
  have hV : IsElemAbelian 2 V := h.hyp151.isElemAbelian
  refine s15_Glue_wClos_zero_le hV (fun g hgM => ?_)
  have hVg := s15_Nine_le_conj D h1217 h hV hL (h158 V₀ V L h hL) hgM
  have hcomm : ⁅V, conjSubgroup V g⁆ = ⊥ := h156 V₀ V L h hL g hVg hgM
  intro b hb
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have h1 : ⁅x, b⁆ ∈ ⁅V, conjSubgroup V g⁆ := Subgroup.commutator_mem_commutator hx hb
  rw [hcomm] at h1
  have h2 : x * b * x⁻¹ * b⁻¹ = 1 := by
    have := Subgroup.mem_bot.1 h1
    rwa [commutatorElement_def] at this
  calc x * b = (x * b * x⁻¹ * b⁻¹) * (b * x) := by group
    _ = b * x := by rw [h2, one_mul]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
