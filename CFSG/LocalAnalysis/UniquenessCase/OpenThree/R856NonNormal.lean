module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight56U14CoverTwo
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight56Residual
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight6xBOutCover
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.SylowNormalizer859
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846h
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight62CenterOfNormal
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811CoordsLift
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.InnerActionOut
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.InnerBarDecomp
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.CoverUpperCentral
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.ExtraspecialCommutator
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.R69CenterApps
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.CoverCentralizerNoncyclic
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight6xBR861E
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.PartOneSixNine
public import CFSG.LocalAnalysis.UniquenessCase.UC6K36SporGe4
public import CFSG.LocalAnalysis.UniquenessCase.UC6K36ODCCent
public import CFSG.LocalAnalysis.UniquenessCase.UC6K316Out
public import CFSG.LieType.SeitzGeneration.SeitzStatus
public import CFSG.LocalAnalysis.UniquenessCase.UC6K36SporPairs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Three.R856NonNormal

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
open CFSG.LocalAnalysis.RankThreeUC.SmallClassTwoGroups (IsExtraspecialExpP)
open scoped commutatorElement


theorem centralizes_sylow_of_cover_choice
    {G : Type} [Group G] [Finite G] {D : Data G} {L Q P X : Subgroup G}
    (hSg : UC6S846.SigmaStd D) (h69 : UC6.R6_9 D)
    (hX : ChoiceX D L Q P X) (hcover : List857Clause2 (Bar2 L))
    (hPL : P ≤ normalizer (L : Set G)) :
    ∀ x ∈ X, ∀ q ∈ Q, x * q = q * x := by
  classical
  have hc := hX.cex
  have hQext : IsExtraspecialExpP 3 1 ↥Q :=
    isExtraspecialExpP_of_isSylowOf_bar hc.sylowQ
      (threeCoverSylowExtraspecial_holds (Bar2 L) hcover)
  have hQeq : Q = P ⊓ L :=
    (hc.sylowQ.eq_of_le (le_inf hc.le hc.sylowQ.le) inf_le_right
      (hc.sylowP.isPGroup.to_le inf_le_left)).symm
  have hQnorm : (Q.subgroupOf P).Normal :=
    normal_subgroupOf_of_isSylowOf_of_le_normalizer hc.sylowQ hc.le hc.sylowP.isPGroup hPL
  have hPQ : P ≤ normalizer (Q : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hc.le).1 hQnorm
  have hInner := inner_action_of_not_three_dvd_outer
    (not_three_dvd_card_outer_of_cover hcover) hc.sylowP.isPGroup hPL
  have hPC : P ≤ Q ⊔ centralizerBar P L :=
    le_sup_centralizerBar_of_inner hc.le hc.sylowQ.le hQeq hQnorm hc.sylowQ
      hc.sylowP.isPGroup hPL le_rfl hInner
  have hQC : ⁅Q, centralizerBar P L⁆ = ⊥ :=
    commutator_eq_bot_centralizerBar hc.sylowQ.le hc.inf_pCore_eq_bot hPQ
  have hCQ : ∀ c ∈ centralizerBar P L, ∀ q ∈ Q, c * q = q * c := by
    intro c hcC q hq
    have hmem : ⁅q, c⁆ ∈ ⁅Q, centralizerBar P L⁆ :=
      Subgroup.commutator_mem_commutator hq hcC
    rw [hQC, Subgroup.mem_bot] at hmem
    exact (commutatorElement_eq_one_iff_mul_comm.mp hmem).symm
  obtain ⟨x, hx, hx1⟩ : ∃ x ∈ X, x ≠ 1 := by
    by_contra h
    push Not at h
    have hbot : X = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      exact (Subgroup.mem_bot).2 (h x hx)
    have hcard := hX.card
    rw [hbot, Subgroup.card_bot] at hcard
    exact (by norm_num : (1 : ℕ) ≠ 3) hcard
  have hCX : centralizer (X : Set G) = centralizer ({x} : Set G) :=
    PartOne.Theorem82.Coords.centralizer_eq_of_card_eq_three hX.card hx hx1
  have hnc : ¬ IsCyclic ↥(centralizer ({x} : Set G) ⊓ Q) :=
    not_isCyclic_centralizer_of_mem_sup hQext hPC hCQ (hX.le hx)
  have hrQ : 2 ≤ CFSG.Open.pRank 3 (centralizer ({x} : Set G) ⊓ Q) :=
    CFSG.LocalAnalysis.RankThreeTheoremC.two_le_pRank_of_not_isCyclic
      Nat.prime_three (by decide) (hc.sylowQ.isPGroup.to_le inf_le_right) hnc
  have hrL : 1 < CFSG.Open.pRank 3 (centralizer (X : Set G) ⊓ L) := by
    rw [hCX]
    exact lt_of_lt_of_le (by norm_num : (1 : ℕ) < 2)
      (hrQ.trans (CFSG.SectionRank.pRank_mono (by norm_num) (inf_le_inf_left _ hc.sylowQ.le)))
  obtain ⟨E, hEM, hEel, hEc, hGamma, hEX⟩ := hasGammaE9_of_pRank hc hrL
  have hXN : ¬ normalizer (X : Set G) ≤ D.M :=
    fun hN => hX.notLe ((centralizer_le_normalizer _).trans hN)
  have hsub : D.sig ⊆ D.sig1 :=
    UC6S846.sig_subset_sig1 hSg (UC6S846.not_solvable_of_mem_calC hc.mem)
  have hXZ2 : X ≤ (Subgroup.upperCentralSeries ↥(Q ⊔ X) 2).map (Q ⊔ X).subtype :=
    le_map_upperCentralSeries_two_of_sup_cover (hX.le.trans hPC) hCQ
      (commutator_le_center_of_isExtraspecialExpP hQext) hX.card
  have hXZ : X ≤ (center ↥(Q ⊔ X)).map (Q ⊔ X).subtype :=
    X_le_center_sup_of_R6_9 h69 hsub hEM hEel hEc hGamma (hX.le.trans hc.sylowP.le)
      hX.card hEX hXN ((sup_le hc.le hX.le).trans hc.sylowP.le)
      (hc.sylowP.isPGroup.to_le (sup_le hc.le hX.le)) le_sup_right hXZ2
  intro x hx q hq
  obtain ⟨z, hz, hzx⟩ := Subgroup.mem_map.mp (hXZ hx)
  have h := congrArg (Q ⊔ X).subtype
    (Subgroup.mem_center_iff.mp hz (⟨q, Subgroup.mem_sup_left hq⟩ : ↥(Q ⊔ X)))
  have hzx' : (z : G) = x := hzx
  change q * (z : G) = (z : G) * q at h
  rw [hzx'] at h
  exact h.symm

theorem false_of_cover_choice_two
    {G : Type} [Group G] [Finite G] {D : Data G} {L Q P X : Subgroup G}
    (hSg : UC6S846.SigmaStd D) (h69 : UC6.R6_9 D)
    (hX : ChoiceX D L Q P X) (hcover : List857Clause2 (Bar2 L))
    (h2 : (MConjSet D.M L).ncard = 2) : False := by
  have hc := hX.cex
  have hPL : P ≤ normalizer (L : Set G) :=
    sylow_le_normalizer_of_ncard_conjSetOf_le_two hc.sylowP hc.mem h2.le
  obtain ⟨L', hL', hne, hPL', hLL', hL'L⟩ :=
    exists_other_conj_of_ncard_two hc.mem h2 hc.sylowP.le hPL
  obtain ⟨hc', hcover'⟩ := hc.conj_other hL' hPL'
  have hX' : ChoiceX D L' (P ⊓ L') P X := ⟨hc', hX.le, hX.card, hX.notLe⟩
  have hQext : IsExtraspecialExpP 3 1 ↥Q :=
    isExtraspecialExpP_of_isSylowOf_bar hc.sylowQ
      (threeCoverSylowExtraspecial_holds (Bar2 L) hcover)
  have hQext' : IsExtraspecialExpP 3 1 ↥(P ⊓ L') :=
    isExtraspecialExpP_of_isSylowOf_bar hc'.sylowQ
      (threeCoverSylowExtraspecial_holds (Bar2 L') (hcover' hcover))
  have hcomm := commute_of_ne_calC_sylow hc.mem hc'.mem hne.symm hLL' hL'L
    hc.sylowP.isPGroup hc.sylowQ hc'.sylowQ hc.le inf_le_left hPL hPL'
  exact false_of_two_commuting_extraspecial hQext hQext' hc.le inf_le_left
    (hc.pRank_sylowP_le_three hSg) hcomm
    (centralizes_sylow_of_cover_choice hSg h69 hX hcover hPL)
    (centralizes_sylow_of_cover_choice hSg h69 hX' (hcover' hcover) hPL') hX.le hX.card
    (fun hXZ => hX.not_le_sylowQ (hXZ.trans inf_le_left))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Three.R856NonNormal

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Three

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.RankThreeUC (Standing Setup AGL81TheoremC)



theorem false_of_nonnormal_triple_cover_dataOfSetup
    {G : Type} [Group G] [Finite G]
    (hS : Standing G) (hUC : CFSG.Open.rankThreeUC G) (hC : AGL81TheoremC G) (S : Setup G)
    (hMS : S.InMSigma) {L Q P X : Subgroup G}
    (hX : PartOne.Section8.ChoiceX (dataOfSetup hS S) L Q P X)
    (hML : ¬ S.M ≤ normalizer (L : Set G))
    (h2 : (PartOne.Section8.MConjSet S.M L).ncard = 2)
    (hcover : PartOne.Section8.List857Clause2 (Bar2 L)) : False := by
  have _ := hMS
  have _ := hML
  exact R856NonNormal.false_of_cover_choice_two
    (UC6S846.sigmaStd_dataOfSetup hS S)
    (r6_9_dataOfSetup hS hUC hC (UCK.k36_of_eqlStar
        (UCK.k36EqlStar_of_catalog CFSG.LieType.SeitzGeneration.kFactSeitzRankTwo_holds
            UCK.k36OddDefChar_holds UCK.k315Spor_holds UCK.k36EqlStarSporGe4_holds) UCK.l34OuterFree) S) hX hcover h2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Three
