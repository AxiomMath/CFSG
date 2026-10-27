module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1TwoCommonBase
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveSeventeen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2EighteenCfg2Fix
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeS

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

private theorem s16e_twoCg_summands (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D) (h127 : R127 D)
    (h1214 : F12.R1214 D) {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V)
    (hset : Setting16 D V₀ V L) (hL : barSub V₀ V hV L ≠ ⊥) (hs : s15 D.M V₀ V hV L = 1)
    {P : s16e_two_NatPred (vStar D.M V₀ V hV L)} (hF : s16e_two_Fam D V₀ V L hV P) :
    ∃ J₀ J₁ : Subgroup (vStar D.M V₀ V hV L),
      P (lStar D.M V₀ V hV L) J₀ ⊥ ∧ P (lStar D.M V₀ V hV L) J₁ ⊥ ∧
      J₀ ⊓ J₁ = ⊥ ∧ J₀ ⊔ J₁ = ⊤ := by
  have h1217 : R1217 D := r1217_of_twelve_seventeen D hx h61 h127 h1214
  have hwtop : wStar D.M V₀ V hV L = ⊤ := s15_Three_wStar_eq_top D h1217 hset.hyp151 hV hL hs
  have hsum : SumOfNat P (lStar D.M V₀ V hV L) ⊤ ⊥ 2 := by
    have h := hF.sum
    rwa [hwtop] at h
  exact s16c167_sumOfNat_two hsum

private theorem s16e_twoCg_fixV (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D) (h127 : R127 D)
    (h1214 : F12.R1214 D) {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V)
    (hset : Setting16 D V₀ V L) (hL : barSub V₀ V hV L ≠ ⊥) (hs : s15 D.M V₀ V hV L = 1)
    {P : s16e_two_NatPred (vStar D.M V₀ V hV L)} (hF : s16e_two_Fam D V₀ V L hV P) :
    fixV (lStar D.M V₀ V hV L) = ⊥ := by
  obtain ⟨J₀, J₁, hN₀, hN₁, hinf, hsup⟩ :=
    s16e_twoCg_summands D hx h61 h127 h1214 hV hset hL hs hF
  exact s16c167_fixV_eq_bot_of_two (hF.natFacts.irr J₀ hN₀).2.2.1 (hF.natFacts.irr J₁ hN₁).2.2.1
    (hF.natFacts.fixV_inf J₀ hN₀) (hF.natFacts.fixV_inf J₁ hN₁) hinf hsup

theorem s16e_two_cfg2 (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D) (h127 : R127 D)
    (h1214 : F12.R1214 D) {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V)
    (hset : Setting16 D V₀ V L) (hL : barSub V₀ V hV L ≠ ⊥) (hs : s15 D.M V₀ V hV L = 1)
    {P : s16e_two_NatPred (vStar D.M V₀ V hV L)} (hF : s16e_two_Fam D V₀ V L hV P) :
    ∃ J₀ J₁ : Subgroup (vStar D.M V₀ V hV L),
      P (lStar D.M V₀ V hV L) J₀ ⊥ ∧ P (lStar D.M V₀ V hV L) J₁ ⊥ ∧
      Cfg2Setting (Mbar D.M (v1Sub D.M V₀ V hV L) V hV) (lStar D.M V₀ V hV L) J₀ J₁ := by
  have h1217 : R1217 D := r1217_of_twelve_seventeen D hx h61 h127 h1214
  obtain ⟨J₀, J₁, hN₀, hN₁, hinf, hsup⟩ :=
    s16e_twoCg_summands D hx h61 h127 h1214 hV hset hL hs hF
  refine ⟨J₀, J₁, hN₀, hN₁, ?_⟩
  have hh := hset.hyp151
  have hMs₀ : D.M ≤ stabTil V₀ V :=
    le_stabTil hh.hyp125.pairFacts.le_normalizer hh.hyp125.pairFacts.le_normalizer₀
  have hMN : D.M ≤ nBar D.M V₀ V hV L := by
    intro m hm
    refine (mem_preBarSub D.M V₀ V hV _ ).2 ⟨hm, hMs₀ hm, ?_⟩
    exact Subgroup.mem_normalizer_iff_map_conj_eq.2
      (lBar_conj_eq_of_s15_eq_one hs (actTil_mem_barSub V₀ V hV hm (hMs₀ hm)))
  have hnorm := s15_T7_barSub_le_normalizer_lStar D hh hMN
  obtain ⟨e⟩ := s16e_two_lStar_equiv D h1217 hh hV
  haveI : IsSimpleGroup ↥(lBar V₀ V hV L) := hF.simple
  haveI : IsSimpleGroup ↥(lStar D.M V₀ V hV L) := e.isSimpleGroup
  haveI : Group.IsPerfect ↥(lBar V₀ V hV L) := Subgroup.isPerfect_iff.2 hF.perfect
  haveI : Group.IsPerfect ↥(lStar D.M V₀ V hV L) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  exact ⟨s15_Infra_vtil_sq_eq_one _ V hV,
    fun x hx => Subgroup.mem_normalizer_iff_map_conj_eq.1 (hnorm hx), inferInstance,
    Subgroup.isPerfect_iff.1 inferInstance,
    s16e_twoCg_fixV D hx h61 h127 h1214 hV hset hL hs hF, hF.natFacts.irr J₀ hN₀,
    hF.natFacts.irr J₁ hN₁, hinf, hsup⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
