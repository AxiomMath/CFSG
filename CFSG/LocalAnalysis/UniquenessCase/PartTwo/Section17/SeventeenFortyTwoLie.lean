module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.TenFiveBridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyTwoChev
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixtyFour
public import CFSG.LocalAnalysis.UniquenessCase.UCInspL2Exc
public import CFSG.Adapters.StatedPSLTwo
public import CFSG.RankThree.PartOne.S11d.PlaneCases
public import CFSG.Quasithin.H13.A5S1327j

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase.UC22.F08

variable {G : Type} [Group G] [Finite G]

private theorem calC_ne_top_of_lie {D : Data G} {L : Subgroup G} (hL : L ∈ calC D.M) :
    L ≠ ⊤ := by
  intro htop
  exact uc22p20a_M_ne_top D (top_le_iff.mp (htop ▸ CFSG.Open.IsSubnormal.le hL.1))

private theorem catalog_barInf_of_lie {D : Data G} {L : Subgroup G} (hL : L ∈ calC D.M)
    (hTCB : CFSG.RankThree.PartOne.TauCetiCatalogBridge) :
    CFSG.Blueprint.Catalog (BarInf L) := by
  have hLtop : L ≠ ⊤ := calC_ne_top_of_lie hL
  have hK : CFSG.Open.IsKGroup ↥L := D.standing.kProper.isKGroup L hLtop
  obtain ⟨hsimple, hnonab⟩ := uc22p20c_barInf_simple (uc22p20e_cComp_of_calC hL)
  haveI : IsSimpleGroup (BarInf L) := hsimple
  have hiso : CFSG.Open.IsCatalogGroup (BarInf L) := by
    refine hK.isCatalogGroup_of_surjective (⊤ : Subgroup ↥L) hnonab ?_ ?_
    · exact (QuotientGroup.mk' (CFSG.solvableRadical ↥L)).comp Subgroup.topEquiv.toMonoidHom
    · exact (QuotientGroup.mk'_surjective _).comp Subgroup.topEquiv.surjective
  exact hTCB (BarInf L) hnonab hiso

theorem exists_cIsChevOver_of_not_concl17_42 (D : Data G) {V₀ V : Subgroup G}
    (hTCB : CFSG.RankThree.PartOne.TauCetiCatalogBridge)
    (h175 : R17_5At D V₀ V) (h1761 : R17_6_1At D V₀ V) (h1763 : R17_6_3At D V₀ V)
    (h1717 : R17_17At D V₀ V) {L : Subgroup G} (hL : L ∈ calC D.M) {p : ℕ}
    (hcounter : ¬ Concl17_42 D L (conjClosure D.M L) p) :
    ∃ n, CIsChevOver (BarInf L) n := by
  classical
  obtain ⟨-, hnonab⟩ := uc22p20c_barInf_simple (uc22p20e_cComp_of_calC hL)
  rcases CFSG.RankThree.PartOne.PlaneCases.catalog_cases
      (catalog_barInf_of_lie hL hTCB) with
    ⟨q, hq, ⟨e⟩⟩ | ⟨m, hm, ⟨e⟩⟩ | ⟨t, n, r, f, hadm, hmodel⟩ | hspor
  ·
    obtain ⟨a, b, hab⟩ := hnonab
    exact absurd (by
      have hcomm : e a * e b = e b * e a := mul_comm _ _
      simpa using congrArg e.symm hcomm) hab
  ·
    rcases eq_or_lt_of_le hm with rfl | hm5
    ·
      have hL2 : LieModel (BarInf L) .PSL 2 2 2 :=
        CFSG.Quasithin.H13.A5.lieModel_of_alternating_five e
      exact ⟨2, .PSL, 2, hL2.admissible, hL2⟩
    ·
      have hisoBar : Nonempty (BarO2Z17 L ≃* alternatingGroup (Fin m)) :=
        ⟨(barO2Z17_equiv_barInf hL).some.trans e⟩
      exact absurd hisoBar (h175 L hL m hm5)
  ·
    by_cases hr : r = 2
    ·
      subst hr
      exact ⟨f, t, n, hadm, hmodel⟩
    ·
      have hrPrime : r.Prime := hadm.1
      have hchev : IsChev (BarInf L) r := ⟨t, n, f, hadm, hmodel⟩
      have hL2 : IsL2Over17 (Bar2 L) r := h1761 L hL r hr hchev
      by_cases hr3 : r = 3
      ·
        subst hr3
        exact absurd hL2 (not_isL2Over17_three (Bar2 L))
      by_cases hr5 : r = 5
      ·
        subst hr5
        have hodd : IsL2Odd (Bar2 L) 5 :=
          isL2Odd_of_isL2Over17_prime Nat.prime_five hL2
        have hq : CFSG.Open.IsQuasisimple (Bar2 L) := hL.2.2
        haveI : IsSimpleGroup (Bar2 L) := LieModel.isSimpleGroup_psl_two hodd
        have hZ : Subgroup.center (Bar2 L) = ⊥ := uc22p21k_center_eq_bot hq
        obtain ⟨eZ⟩ := uc22p21k_barInf_equiv_of_center_bot hq hZ
        obtain ⟨-, K, hKfield, hKfinite, hKcard, ⟨eK⟩⟩ :=
          LieModel.statedClassicalModel hodd (by decide)
        letI : Field K := hKfield
        letI : Finite K := hKfinite
        have hK5 : Nat.card K = 5 := by rw [hKcard, pow_one]
        have hmodel4 : LieModel (Bar2 L) .PSL 2 2 2 :=
          CFSG.LocalAnalysis.UniquenessCase.UCK.Insp.lieModel_psl_two_five_two_two hK5 eK
        have hmodel4' : LieModel (BarInf L) .PSL 2 2 2 :=
          LieModel.of_mulEquiv eZ.symm hmodel4
        exact ⟨2, .PSL, 2, hmodel4'.admissible, hmodel4'⟩
      ·
        have hr7 : 5 < r := by
          by_contra hle
          have hle' : r ≤ 5 := Nat.le_of_not_gt hle
          have h2 : 2 ≤ r := hrPrime.two_le
          interval_cases r
          · exact absurd rfl hr
          · exact absurd rfl hr3
          · norm_num at hrPrime
          · exact absurd rfl hr5
        have hodd : IsL2Odd (Bar2 L) r := isL2Odd_of_isL2Over17_prime hrPrime hL2
        have hthin : F08.Thin8 L := thin8_of_isL2Odd hodd
        have hm3 : CFSG.Open.pRank 3 L = 1 := pRank_three_eq_one_of_isL2Odd hodd
        obtain ⟨⟨K₀, hK₀, huniq₀⟩, -⟩ := h1763 L hL r hr hchev hr7
        have huniq : ∀ K ∈ calC D.M, F08.Thin8 K → CFSG.Open.pRank 3 K = 1 → K = L := by
          intro K hK hthinK hm3K
          exact (huniq₀ K ⟨hK, hthinK, hm3K⟩).trans
            (huniq₀ L ⟨hL, hthin, hm3⟩).symm
        exact absurd (false_of_concl_of_unique_thin hL rfl hthin hm3 huniq hcounter)
          not_false
  ·
    obtain ⟨s, he⟩ := hspor
    have hconcl : Concl17_17 D V₀ V L := h1717 L hL ⟨s, he⟩
    have hm3 : CFSG.Open.pRank 3 L = 1 := by
      rw [← CFSG.SectionRank.pRank_coe_eq_openPRank 3 L]
      exact hconcl.2.1.2.1
    have huniq : ∀ K ∈ calC D.M, F08.Thin8 K → CFSG.Open.pRank 3 K = 1 → K = L := by
      intro K hK hthinK hm3K
      have hm3K' : CFSG.pRank 3 ↥K = 1 := by
        rwa [CFSG.SectionRank.pRank_coe_eq_openPRank 3 K]
      exact hconcl.2.1.2.2 K hK hthinK hm3K'
    exact absurd (false_of_concl_of_unique_thin hL rfl hconcl.2.1.1 hm3 huniq hcounter)
      not_false

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
