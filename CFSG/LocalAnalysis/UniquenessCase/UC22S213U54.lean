module

import CFSG.LocalAnalysis.UniquenessCase.UC22S213PrimeSylow
import CFSG.LocalAnalysis.UniquenessCase.UC22S213Inner
import CFSG.LocalAnalysis.UniquenessCase.UC22S218Center
import CFSG.LocalAnalysis.UniquenessCase.UC22P21d
import CFSG.LocalAnalysis.UniquenessCase.UC22P20a
import CFSG.LocalAnalysis.UniquenessCase.UC6R869MConj
import CFSG.LocalAnalysis.UniquenessCase.UCFront07Use
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.CentralizingRank
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Setup
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Gamma614Application
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight63General
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K33MissingRanks
import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7StdEven
import CFSG.Adapters.LieModelUnitaryOuter
public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerReductionDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.KInputs
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21d
public import CFSG.LocalAnalysis.UniquenessCase.UC6Inst
import CFSG.LieType.SteinbergBRMulEquivCores
import CFSG.LocalAnalysis.UniquenessCase.UC6S846b
import CFSG.LocalAnalysis.UniquenessCase.UC6S846c

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.Blueprint.Multiplier (genericOrders exceptionalOrders)
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 PartIAt SigmaOne4)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (Conclusion76 StronglyEmbeddedFive)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.ABGLocalTools (IsSylowOf)

variable {G : Type} [Group G] [Finite G]

theorem uc22s213_le_centralizer_of_not_dvd_outer {L P : Subgroup G}
    (hq : CFSG.Open.IsQuasisimple (Bar2 L)) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hout : ¬ r ∣ Nat.card (Outer (BarInf L))) (hPr : IsPGroup r P)
    (hPN : P ≤ normalizer (L : Set G)) (hQ : IsSylowOf r (P ⊓ L) L)
    (hQab : IsMulCommutative ↥(P ⊓ L)) : P ⊓ L ≤ centralizer (P : Set G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact r.Prime := ⟨hr⟩
  have hout2 := uc22s213_not_dvd_card_outer_bar2 hq hout
  have hPQ : P ≤ normalizer ((P ⊓ L : Subgroup G) : Set G) :=
    (le_inf le_normalizer hPN).trans inf_normalizer_le_normalizer_inf
  have hQO2 : P ⊓ L ⊓ CFSG.Open.pCoreOf 2 L = ⊥ :=
    (IsPGroup.disjoint_of_ne r 2 hr2 _ _ hQ.isPGroup (UC6S846.isPGroup_pCoreOf L)).eq_bot
  have hdec : P ≤ P ⊓ L ⊔ PartOne.Section8.centralizerBar P L :=
    PartOne.Section8.le_sup_centralizerBar_of_inner_prime inf_le_left inf_le_right rfl
      (normal_subgroupOf_of_le_normalizer hPQ) hQ hPr hPN le_rfl fun y hy =>
        PartOne.Section8.exists_conj_of_not_dvd_outer y (hPN hy)
          (hPr.to_le (zpowers_le.mpr hy)) hout2
  have hcomm := PartOne.Section8.commutator_eq_bot_centralizerBar inf_le_right hQO2 hPQ
  have hPC : P ≤ centralizer ((P ⊓ L : Subgroup G) : Set G) :=
    hdec.trans (sup_le (le_centralizer_iff_isMulCommutative.mpr hQab)
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp
        ((Subgroup.commutator_comm _ _).trans hcomm)))
  exact le_centralizer_iff.mp hPC

theorem uc22s213_strong_of_not_three_dvd_outer (hS : Standing4 G) (hU : uniqueFourUnique G)
    (S : Setup4 G) (hσ : S.InMSigma) (hPart : PartIAt S.M) (hSE : StronglyEmbeddedFive)
    (hOut : CFSG.LocalAnalysis.RankThreeTheoremC.KFactOutCyclic) {L : Subgroup G}
    (hL : L ∈ calC S.M) (hZ : ¬ 3 ∣ Nat.card (center (Bar2 L)))
    (hout : ¬ 3 ∣ Nat.card (Outer (BarInf L))) (h27 : ¬ 27 ∣ Nat.card (BarInf L))
    (h2 : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (BarInf L)))
    (hp : CFSG.Open.pRank S.p L ≤ 1) : IsStronglyPEmbedded 3 S.M := by
  by_contra hnot
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hLM : L ≤ S.M := CFSG.Quasithin.A3.subnormal_le hL.1
  have hL3 : 2 ≤ CFSG.Open.pRank 3 L := uc22s213_pRank_three_barInf hL.2.2 hZ ▸ h2
  have hMN : S.M ≤ normalizer (L : Set G) := by
    by_contra hMN
    exact hZ (PartOne.Section8.three_dvd_center_bar2_of_calC_of_not_normal hS hU S hσ hnot hL
      (PartOne.Section8.pRank_three_eq_two_of_mem_calC_of_list880 hS S hPart hnot hL hL3) hMN)
  obtain ⟨P, hP⟩ := CFSG.ABGLocalTools.exists_isSylowOf 3 S.M
  have hQ : IsSylowOf 3 (P ⊓ L) L := hP.inf_of_le_normalizer hLM hMN
  obtain ⟨hQel, hQ9⟩ := uc22s213_isElemAbelian_of_isSylowOf hL.2.2 hZ h27 h2 hQ
  have hQC : P ⊓ L ≤ centralizer (P : Set G) :=
    uc22s213_le_centralizer_of_not_dvd_outer hL.2.2 Nat.prime_three (by norm_num) hout
      hP.isPGroup (hP.le.trans hMN) hQ hQel.1
  have h3β : 3 ∉ uniqueFourBeta G := fun h =>
    hnot (isStronglyPEmbedded_three_of_mem_uniqueFourBeta hU S hσ h)
  have hpp : S.p.Prime := S.hp.1.1
  have hp2 : S.p ≠ 2 := S.hp.1.2.1
  haveI : Fact S.p.Prime := ⟨hpp⟩
  have hsp := PartOne.Section8.isStronglyPEmbedded_of_mem_sigma_of_calC hS hU S hL S.hp
  have h76 : Conclusion76 S.M S.p := UC6.conclusion76_dataOfSetup4 hSE hS hU S h3β S.hp hsp
  obtain ⟨B, hBM, hBel, hBc⟩ :=
    UC6S846.exists_elemAbelian_card_of_le_pRank hpp (UC6.four_le_pRank_of_sigma S.hp)
  have hLtop : L ≠ ⊤ :=
    ne_top_of_le_ne_top (uc22p20a_M_ne_top (UC6.dataOfSetup4 hS hU S)) hLM
  have hF := UC6.R869S.two_le_pRank_centralizer_of_pRank_mulAut hLM hpp hp2
    (UC6.R869S.pRank_mulAut_bar2_le_two hOut (hS.kProper.isKGroup L hLtop) hL.2.2 hpp hp2 hp)
    hBM (hBM.trans hMN) hBel hBc Nat.prime_three (by norm_num) inf_le_right hQ.isPGroup
  have hQr : 2 ≤ CFSG.Open.pRank 3 (P ⊓ L) :=
    CFSG.SectionRank.le_pRank (by norm_num) le_rfl hQel (by rw [hQ9]; norm_num)
  have hΓ : CFSG.Open.rankThreeGamma 1 3 (P ⊓ L) ≤ S.M :=
    PartOne.Section7.rankThreeGamma_le_of_two_le_pRank_inf_centralizer hsp h76
      (inf_le_right.trans hLM) hQ.isPGroup hQr hF
  have hsub : uniqueFourSigma S.M ⊆ SigmaOne4 G := fun q hq =>
    ⟨hq.1, S.M, S.maxLocal, hq,
      PartOne.Section8.isStronglyPEmbedded_of_mem_sigma_of_calC hS hU S hL hq⟩
  exact hnot (PartOne.Section8.stronglyPEmbedded_of_e9_le_center_sylow hS hU S hPart.2.1 hsub
    (fun h => h3β h.1) hP (le_inf inf_le_left hQC) hQel hQ9 hΓ)

theorem uc22s213_not_centralizesBar_of_not_three_dvd_outer (hS : Standing4 G)
    (hU : uniqueFourUnique G) (S : Setup4 G) (hσ : S.InMSigma) (hPart : PartIAt S.M)
    (hSE : StronglyEmbeddedFive) (hOut : CFSG.LocalAnalysis.RankThreeTheoremC.KFactOutCyclic)
    {L : Subgroup G} (hL : L ∈ calC S.M) (hZ : ¬ 3 ∣ Nat.card (center (Bar2 L)))
    (hout : ¬ 3 ∣ Nat.card (Outer (BarInf L))) (h27 : ¬ 27 ∣ Nat.card (BarInf L))
    (h2 : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (BarInf L)))
    (hk1 : IsStronglyPEmbedded 3 S.M → CFSG.Open.pRank 3 L ≤ 1) {a : G}
    (hodd : Odd (orderOf a)) (hpr : (orderOf a).Prime)
    (hN : CFSG.Open.pRank S.p (normalizer ((zpowers a : Subgroup G) : Set G) ⊓ S.M) ≤ 1) :
    ¬ CentralizesBar a L := by
  intro haL
  have hp := uc22s213_pRank_le_one_of_centralizesBar (CFSG.Quasithin.A3.subnormal_le hL.1) hodd
    hpr haL S.hp.1.1 S.hp.1.2.1 hN
  have h1 := hk1 (uc22s213_strong_of_not_three_dvd_outer hS hU S hσ hPart hSE hOut hL hZ hout h27
    h2 hp)
  have hb := uc22s213_pRank_three_barInf hL.2.2 hZ
  omega

@[expose] def S21_3ClosedU54 (L : Subgroup G) : Prop :=
  LieModel (BarInf L) .PSU 5 2 2

theorem uc22s213_not_centralizesBar_of_u54 (hGA : GriessAllModelsStatement) (hS : Standing4 G)
    (hU : uniqueFourUnique G) (S : Setup4 G) (hσ : S.InMSigma) (hPart : PartIAt S.M)
    (hSE : StronglyEmbeddedFive) (hOut : CFSG.LocalAnalysis.RankThreeTheoremC.KFactOutCyclic)
    (Ch : Choice2011 G) (c : Ctx21 (UC6.dataOfSetup4 hS hU S) Ch) {L : Subgroup G}
    (hL : L ∈ calC S.M) (hT : S21_3ClosedU54 L)
    (hk1 : IsStronglyPEmbedded 3 S.M → CFSG.Open.pRank 3 L ≤ 1) {a : G} (ha : a ∈ c.B)
    (hpr : (orderOf a).Prime)
    (hN : ∀ p ∈ uniqueFourSigma S.M,
      CFSG.Open.pRank p (normalizer ((zpowers a : Subgroup G) : Set G) ⊓ S.M) ≤ 1) :
    ¬ CentralizesBar a L := by
  have hX : LieModel (BarInf L) .PSU 5 2 2 := hT
  have hZ : ¬ 3 ∣ Nat.card (center (Bar2 L)) := by
    have hrow := griessRow_of_lieModel_classical hGA hX (by decide)
    have hg : genericOrders .PSU 5 2 2 = (5, 1) := rfl
    have he : exceptionalOrders .PSU 5 2 2 = (1, 1) := rfl
    have hdvd : Nat.card (center (Bar2 L)) ∣ 5 := by
      simpa [hg, he] using card_center_bar2_dvd_of_row hL (by rw [hg, he]; norm_num) hrow
    exact fun h3 => absurd (h3.trans hdvd) (by norm_num)
  have hout : ¬ 3 ∣ Nat.card (Outer (BarInf L)) := by
    rw [hX.card_outer_psu (by norm_num) (by omega)]
    norm_num
  have h27 : ¬ 27 ∣ Nat.card (BarInf L) := by
    rw [CFSG.ComponentClassification.GSThmB.Catalog7Std.card_of_lieModel_PSU (by norm_num)
      (by norm_num) hX]
    decide
  have h2 : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (BarInf L)) :=
    (PartOne.Section8.pRank_three_eq_two_of_lieModel_PSU_five_of_mod_one (by norm_num) hX).ge
  exact uc22s213_not_centralizesBar_of_not_three_dvd_outer hS hU S hσ hPart hSE hOut hL hZ hout h27
    h2 hk1 (uc22p21d_odd_orderOf_of_mem_calB1 c.hB ha) hpr (hN S.p S.hp)

end CFSG.LocalAnalysis.UniquenessCase.UC22
