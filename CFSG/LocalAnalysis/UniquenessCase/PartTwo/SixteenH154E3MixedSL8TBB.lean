module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3OmegaA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3OmegaE
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23Odd
public import CFSG.Quasithin.Vol2.Ch5Sec1L34Lem516
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL8TBBA1
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL8TBBA2
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22uc
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin.B15P4
open CFSG.AGLEmbedding

variable {G : Type} [Group G] [Finite G]

theorem s16h_e3_sl28_cover_cent (D : Data G) {V L : Subgroup G} (h : Setting16 D ⊥ V L)
    {x : G} (hxM : x ∈ D.M) (hxn : x ∉ nBar D.M ⊥ V h.hyp151.isElemAbelian L)
    {K : Subgroup G} (hK : K ∈ calC D.M)
    (hKbar : barSub ⊥ V h.hyp151.isElemAbelian K =
      barSub ⊥ V h.hyp151.isElemAbelian (conjSubgroup L x)) :
    K ≤ centralizer (wSub ⊥ V h.hyp151.isElemAbelian L : Set G) := by
  have hV := h.hyp151.isElemAbelian
  have h125 := h.hyp16.hyp125
  have hMs : D.M ≤ stabTil ⊥ V :=
    le_stabTil h125.pairFacts.le_normalizer h125.pairFacts.le_normalizer₀
  have hfix : wTil ⊥ V hV L ≤ fixV (barSub ⊥ V hV (conjSubgroup L x)) :=
    commSub_eq_bot_iff.1 (h.hyp151.commute x hxM hxn).2
  intro k hk
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  have hwV : w ∈ V := preTil_le ⊥ V hV _ hw
  have hks : k ∈ stabTil ⊥ V := hMs (hK.1.le hk)
  have hkbar : actTil ⊥ V hV ⟨k, hks⟩ ∈ barSub ⊥ V hV (conjSubgroup L x) := by
    rw [← hKbar]
    exact actTil_mem_barSub ⊥ V hV hk hks
  have hmkW : mkTil ⊥ V hV (IntMod.mk hV ⟨w, hwV⟩) ∈ wTil ⊥ V hV L :=
    (mem_preTil_iff_of_mem ⊥ V hV _ hwV).1 hw
  have hfixw := (mem_fixV.1 (hfix hmkW)) (actTil ⊥ V hV ⟨k, hks⟩) hkbar
  have h1 : mkTil ⊥ V hV (actStab ⊥ V hV ⟨k, hks⟩ (IntMod.mk hV ⟨w, hwV⟩)) =
      mkTil ⊥ V hV (IntMod.mk hV ⟨w, hwV⟩) := by
    simpa only [actTil_mk] using hfixw
  have h2 : (actStab ⊥ V hV ⟨k, hks⟩ (IntMod.mk hV ⟨w, hwV⟩)).val * w⁻¹ ∈ (⊥ : Subgroup G) :=
    (mkTil_eq_iff ⊥ V hV _ _).1 h1
  rw [Subgroup.mem_bot, actStab_apply_val, mul_inv_eq_one] at h2
  exact (mul_inv_eq_iff_eq_mul.mp h2).symm

theorem s16h_e3_sl28_cover_bar2_isL2 (D : Data G) (S : s16h_Std D) {V L : Subgroup G}
    (h : Setting16 D ⊥ V L)
    (hrow : s16h_H5RowSL2 (lBar ⊥ V h.hyp151.isElemAbelian L)
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L))
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
        fixV (lBar ⊥ V h.hyp151.isElemAbelian L)) 3)
    {x : G} (hxM : x ∈ D.M) (hxn : x ∉ nBar D.M ⊥ V h.hyp151.isElemAbelian L)
    {K : Subgroup G} (hK : K ∈ calC D.M)
    (hKbar : barSub ⊥ V h.hyp151.isElemAbelian K =
        lBar ⊥ V h.hyp151.isElemAbelian L ∨
      barSub ⊥ V h.hyp151.isElemAbelian K =
        barSub ⊥ V h.hyp151.isElemAbelian (conjSubgroup L x)) :
    IsL2 (Bar2 K) 3 := by
  obtain ⟨e⟩ := s16h_e3_sl28_bar2_center_quotient_psl2 D S h hrow hxM hxn hK hKbar
  have hZ : Subgroup.center (Bar2 K) = ⊥ :=
    s16h_center_eq_bot_of_center_quotient_psl2_eight hK.2.2 e
  have e' : Bar2 K ≃* PSL2GF 2 3 :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans e
  obtain ⟨-, hc | ⟨hn, -⟩⟩ :=
    CFSG.Walter.lieModel_psl_two_of_mulEquiv (p := 2) (f := 3) (by norm_num) e'
  · exact Or.inl ⟨by decide, hc⟩
  · exact absurd hn (by norm_num)

theorem s16h_e3_sl28_cover_pCore (D : Data G) {K : Subgroup G} (hK : K ∈ calC D.M)
    (hK2 : IsL2 (Bar2 K) 3) : pCoreOf 2 K ≠ ⊥ := by
  have hM : CFSG.QuasithinUnique.CharTwo D.M := D.standing.charTwo D.M D.maxLocal.1
  refine CFSG.Quasithin.H13.pCoreOf_ne_bot_of_subnormal hK.1 hM ?_
  intro hbot
  have hcard := s16h_e3_omega_card_of_isL2 hK2
  rw [hbot] at hcard
  have h1 : Nat.card (Bar2 (⊥ : Subgroup G)) = 1 :=
    Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨1⟩⟩
  rw [h1] at hcard
  norm_num [ordA] at hcard

theorem s16h_e3_sl28_cover_normal (D : Data G) {V L : Subgroup G} (h : Setting16 D ⊥ V L)
    (hcomp : IsComponentOf (lBar ⊥ V h.hyp151.isElemAbelian L)
      (Mbar D.M ⊥ V h.hyp151.isElemAbelian))
    (hs2 : s15 D.M ⊥ V h.hyp151.isElemAbelian L = 2)
    {x : G} (hxM : x ∈ D.M) (hxn : x ∉ nBar D.M ⊥ V h.hyp151.isElemAbelian L)
    {L₀ L₁ : Subgroup G} (hL₀ : L₀ ∈ calC D.M) (hL₁ : L₁ ∈ calC D.M) (hne : L₀ ≠ L₁)
    (h₀ : barSub ⊥ V h.hyp151.isElemAbelian L₀ =
      barSub ⊥ V h.hyp151.isElemAbelian (conjSubgroup L x))
    (h₁ : barSub ⊥ V h.hyp151.isElemAbelian L₁ = lBar ⊥ V h.hyp151.isElemAbelian L) :
    D.M ≤ normalizer ((L₀ ⊔ L₁ : Subgroup G) : Set G) := by
  have hV := h.hyp151.isElemAbelian
  have h125 := h.hyp16.hyp125
  have hMs : D.M ≤ stabTil ⊥ V :=
    le_stabTil h125.pairFacts.le_normalizer h125.pairFacts.le_normalizer₀
  have hna : ⁅lBar ⊥ V hV L, lBar ⊥ V hV L⁆ ≠ ⊥ := by
    rw [perfect_of_isComponentOf hcomp]
    exact ne_bot_of_isComponentOf hcomp
  have hnaLbx : ⁅barSub ⊥ V hV (conjSubgroup L x),
      barSub ⊥ V hV (conjSubgroup L x)⁆ ≠ ⊥ := by
    rw [s15_Infra_barSub_conjSubgroup ⊥ V hV (hMs hxM) L, ← Subgroup.map_commutator]
    change (⁅lBar ⊥ V hV L, lBar ⊥ V hV L⁆).map _ ≠ ⊥
    rw [perfect_of_isComponentOf hcomp]
    intro hbot
    exact ne_bot_of_isComponentOf hcomp
      ((Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj _).injective).1 hbot)
  have key : ∀ m ∈ D.M, conjSubgroup (L₀ ⊔ L₁) m = L₀ ⊔ L₁ := by
    intro m hm
    have hms : m ∈ stabTil ⊥ V := hMs hm
    have hcal₀ : conjSubgroup L₀ m ∈ calC D.M :=
      uc22p22u_calC_conj (Subgroup.le_normalizer (H := D.M)) hL₀ hm
    have hcal₁ : conjSubgroup L₁ m ∈ calC D.M :=
      uc22p22u_calC_conj (Subgroup.le_normalizer (H := D.M)) hL₁ hm
    have hbar₀ : barSub ⊥ V hV (conjSubgroup L₀ m) = lBar ⊥ V hV L ∨
        barSub ⊥ V hV (conjSubgroup L₀ m) =
          barSub ⊥ V hV (conjSubgroup L x) := by
      have h' : barSub ⊥ V hV (conjSubgroup L₀ m) =
          barSub ⊥ V hV (conjSubgroup (conjSubgroup L x) m) := by
        rw [s15_Infra_barSub_conjSubgroup ⊥ V hV hms L₀,
          s15_Infra_barSub_conjSubgroup ⊥ V hV hms (conjSubgroup L x), h₀]
      rw [h', conjSubgroup_conjSubgroup]
      exact c23_barSub_conj_cases D h.hyp151 hV hs2 hxM hxn (D.M.mul_mem hxM hm)
    have hbar₁ : barSub ⊥ V hV (conjSubgroup L₁ m) = lBar ⊥ V hV L ∨
        barSub ⊥ V hV (conjSubgroup L₁ m) =
          barSub ⊥ V hV (conjSubgroup L x) := by
      have h' : barSub ⊥ V hV (conjSubgroup L₁ m) = barSub ⊥ V hV (conjSubgroup L m) := by
        rw [s15_Infra_barSub_conjSubgroup ⊥ V hV hms L₁,
          s15_Infra_barSub_conjSubgroup ⊥ V hV hms L, h₁]
        rfl
      rw [h']
      exact c23_barSub_conj_cases D h.hyp151 hV hs2 hxM hxn hm
    have hc₀ : conjSubgroup L₀ m = L₀ ∨ conjSubgroup L₀ m = L₁ := by
      rcases hbar₀ with hb | hb
      · refine Or.inr (s16h_e3_omega_calC_eq_of_barSub_eq h125 hcal₀ hL₁
          (hb.trans h₁.symm) ?_)
        rw [hb]; exact hna
      · refine Or.inl (s16h_e3_omega_calC_eq_of_barSub_eq h125 hcal₀ hL₀
          (hb.trans h₀.symm) ?_)
        rw [hb]; exact hnaLbx
    have hc₁ : conjSubgroup L₁ m = L₀ ∨ conjSubgroup L₁ m = L₁ := by
      rcases hbar₁ with hb | hb
      · refine Or.inr (s16h_e3_omega_calC_eq_of_barSub_eq h125 hcal₁ hL₁
          (hb.trans h₁.symm) ?_)
        rw [hb]; exact hna
      · refine Or.inl (s16h_e3_omega_calC_eq_of_barSub_eq h125 hcal₁ hL₀
          (hb.trans h₀.symm) ?_)
        rw [hb]; exact hnaLbx
    have hinj : Function.Injective (fun A : Subgroup G => conjSubgroup A m) := by
      intro A B hAB
      have h' := congrArg (fun C : Subgroup G => conjSubgroup C m⁻¹) hAB
      simpa only [conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one] using h'
    rw [show conjSubgroup (L₀ ⊔ L₁) m = conjSubgroup L₀ m ⊔ conjSubgroup L₁ m from by
      simp only [conjSubgroup, Subgroup.map_sup]]
    rcases hc₀ with h₀' | h₀'
    · rcases hc₁ with h₁' | h₁'
      · exact absurd (hinj (h₀'.trans h₁'.symm)) hne
      · simp only [h₀', h₁']
    · rcases hc₁ with h₁' | h₁'
      · simp only [h₀', h₁', sup_comm]
      · exact absurd (hinj (h₀'.trans h₁'.symm)) hne
  intro m hm
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  simpa [conjSubgroup] using key m⁻¹ (D.M.inv_mem hm)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
