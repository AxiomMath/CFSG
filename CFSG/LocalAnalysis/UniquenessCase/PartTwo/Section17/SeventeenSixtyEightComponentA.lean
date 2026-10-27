module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixtyEightSetup
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixtyEightCentralizer
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen3a
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenGlueB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.CatalogueThreePrime

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {G : Type} [Group G] [Finite G]

theorem not_three_dvd_card_of_mem_calC {D : Data G} {L L' J : Subgroup G}
    (c : Ctx1768 D L L') (hR82 : F08.R82 D) (hk2 : D.k = 2)
    (hJ : J ∈ calC D.M) (hJL : J ≠ L) (hJL' : J ≠ L') :
    ¬ 3 ∣ Nat.card J := by
  intro h3
  have hXM : conjClosure D.M L ≤ D.M := Ctx1768.conjClosure_le c
  have hJM : J ≤ D.M := s13_le_of_mem_calC hJ
  have hJ3ge : 1 ≤ CFSG.Open.pRank 3 J :=
    s13_one_le_pRank_of_dvd J Nat.prime_three h3
  have hJC : barImage D.M J ≤ Subgroup.centralizer
      (barImage D.M (conjClosure D.M L) : Set (Bar2 D.M)) :=
    barImage_le_centralizer c.hL c.hL' c.hX hJ hJL hJL'
  have hJbar_le : CFSG.Open.pRank 3 (barImage D.M J) ≤ 1 :=
    calc CFSG.Open.pRank 3 (barImage D.M J)
        ≤ CFSG.Open.pRank 3 (Subgroup.centralizer
            (barImage D.M (conjClosure D.M L) : Set (Bar2 D.M))) :=
          CFSG.SectionRank.pRank_mono (by norm_num) hJC
      _ ≤ 1 := pRank_centralizer_le_one (Or.inl rfl) c.he3 c.isA5xA5_barImage
  have hJbar_eq : CFSG.Open.pRank 3 (barImage D.M J) = 1 := by
    refine le_antisymm hJbar_le ?_
    rw [s13_pRank_barImage Nat.prime_three (by norm_num) hJM]
    exact hJ3ge
  have hJ3 : CFSG.Open.pRank 3 J = 1 := by
    rw [← s13_pRank_barImage Nat.prime_three (by norm_num) hJM]
    exact hJbar_eq
  have hL3 : CFSG.Open.pRank 3 L = 1 := pRank_three_eq_one_of_isAlt_five c.hAlt
  have hL'3 : CFSG.Open.pRank 3 L' = 1 := pRank_three_eq_one_of_isAlt_five c.hAlt'
  have hX2 : CFSG.Open.pRank 3 (conjClosure D.M L) = 2 := by
    rw [← s13_pRank_barImage Nat.prime_three (by norm_num) hXM,
      CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
    exact pRank_eq_two_of_isA5xA5 c.isA5xA5_barImage (Or.inl rfl)
  have hadd := pRank_add_pRank_le_of_le_centralizer (D := D) (X := conjClosure D.M L)
    Nat.prime_three (by norm_num) c.isA5xA5_barImage (C := barImage D.M J) hJC
  have hsup : CFSG.Open.pRank 3 (barImage D.M (conjClosure D.M L) ⊔ barImage D.M J) =
      CFSG.Open.pRank 3 (conjClosure D.M L ⊔ J) := by
    rw [← s13_barImage_sup hXM hJM,
      s13_pRank_barImage Nat.prime_three (by norm_num) (sup_le hXM hJM)]
  have h3le : 3 ≤ CFSG.Open.pRank 3 (conjClosure D.M L ⊔ J) := by
    calc 3 = CFSG.Open.pRank 3 (conjClosure D.M L) + CFSG.Open.pRank 3 J := by
          rw [hX2, hJ3]
      _ = CFSG.Open.pRank 3 (barImage D.M (conjClosure D.M L)) +
            CFSG.Open.pRank 3 (barImage D.M J) := by
          rw [s13_pRank_barImage Nat.prime_three (by norm_num) hXM,
            s13_pRank_barImage Nat.prime_three (by norm_num) hJM]
      _ ≤ CFSG.Open.pRank 3 (barImage D.M (conjClosure D.M L) ⊔ barImage D.M J) := hadd
      _ = CFSG.Open.pRank 3 (conjClosure D.M L ⊔ J) := hsup
  have h2lt : 2 < CFSG.Open.pRank 3 (L ⊔ L' ⊔ J) := by
    have h' : 2 < CFSG.Open.pRank 3 (conjClosure D.M L ⊔ J) := by omega
    rwa [c.hX] at h'
  have h81 : F08.Hyp81 D.M (L ⊔ L' ⊔ J) := by
    refine ⟨isSubnormal_sup_sup c.hL c.hL' hJ, commutator_sup_sup c.hL c.hL' hJ, h2lt,
      Or.inr ⟨L, L', J, c.hL, c.hL', hJ, hL3, hL'3, hJ3, ?_, ?_, ?_,
        coe_sup_sup_eq_mul c.hL c.hL' hJ c.hne.symm hJL.symm hJL'.symm⟩⟩
    · exact le_sup_left.trans le_sup_left
    · exact le_sup_right.trans le_sup_left
    · exact le_sup_right
  have hk1 : D.k = 1 := Data.k_eq_one_of_isStronglyPEmbedded D (hR82 _ h81)
  omega

theorem exists_isSz_of_not_three_dvd
    (hK7 : CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.K_CatalogueThreePrimeSz)
    {D : Data G} {J : Subgroup G} (hJ : J ∈ calC D.M) (h3 : ¬ 3 ∣ Nat.card J) :
    ∃ n, IsSz (Bar2 J) n := by
  have hJM : J ≤ D.M := s13_le_of_mem_calC hJ
  have hMJ : CFSG.Open.IsKGroup ↥D.M :=
    D.standing.kProper.isKGroup D.M (uc22br4_M_ne_top D)
  have hJk : CFSG.Open.IsKGroup (Bar2 J) :=
    (hMJ.of_le hJM).quotient (CFSG.pCore 2 ↥J)
  have h3bar : ¬ 3 ∣ Nat.card (Bar2 J) := by
    have hdvd : Nat.card (Bar2 J) ∣ Nat.card ↥J :=
      Subgroup.card_quotient_dvd_card (CFSG.pCore 2 ↥J)
    exact fun h => h3 (h.trans hdvd)
  have hpi : 3 ∉ piSet (⊤ : Subgroup (Bar2 J)) := by
    intro hmem
    exact h3bar (by simpa [Subgroup.card_top] using hmem.2)
  obtain ⟨n, hn⟩ := hK7 (Bar2 J) hJk hJ.2.2 hpi
  refine ⟨n, ?_⟩
  exact CFSG.Blueprint.LieModel.of_mulEquiv
    ((QuotientGroup.quotientMulEquivOfEq (s13_pCore_bar_eq_bot J)).trans
      (QuotientGroup.quotientBot (G := Bar2 J))) hn

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
