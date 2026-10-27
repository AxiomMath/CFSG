module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenStdSixFourteen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Conclusion76Three
public import CFSG.LocalAnalysis.AGLEmbedding.CatalogSchreier
public import CFSG.LocalAnalysis.UniquenessCase.UC7P3ThreeKIBA6
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.R72.Setup4Core
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.R72.RankThree
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.R72.ReeThreeType
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Theorem76
public import CFSG.LocalAnalysis.UniquenessCase.UC7P3Theorem76
public import Certificates.Certificate17430
public import Certificates.Certificate9726
public import Certificates.Certificate9530

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

section


theorem r76Sig_of_s168e3Std {D : Data G} (s : S168e3Std D) :
    UC22.F07.R76Sig D := by
  intro p hp hp2 hsp r hr E hEM hEel hEcard hcent hXsub
  have hpp : p.Prime := (D.sig_prime p hp).1
  have hUniq : ∀ U : Subgroup G, U ≠ ⊥ → IsPGroup 2 U →
      2 ≤ CFSG.Open.pRank p (Subgroup.normalizer (U : Set G) ⊓ D.M) → Subgroup.normalizer (U : Set G) ≤ D.M := by
    intro U hU1 hU2 hUr
    obtain ⟨E', hE'le, hE'el, hE'card⟩ :=
      CFSG.AGLEmbedding.exists_isElemAbelian_card_sq_of_two_le_pRank hpp hUr
    have hE'M : E' ≤ D.M := hE'le.trans inf_le_right
    have hE'nc : ¬ IsCyclic E' :=
      @CFSG.IsElementaryAbelian.not_isCyclic_of_card_eq_prime_sq ↥E' _ _ p ⟨hpp⟩
        hE'el.isElementaryAbelian hE'card
    have hUM : UniqueMax D.M E' := s.h61 p hp E' hE'M hE'el.isPGroup hE'nc
    have hHN : IsTwoLocal (Subgroup.normalizer (U : Set G)) := ⟨U, hU1, hU2, rfl⟩
    obtain ⟨N, hN, hHNle⟩ :=
      CFSG.RankThreeCoreUniqueness.Helpers.twoLocal_le_maxTwoLocal _ hHN
    have hNmem : N ∈ calMOf E' := ⟨hN, (hE'le.trans inf_le_left).trans hHNle⟩
    rw [hUM] at hNmem
    have hNM : N = D.M := by simpa using hNmem
    exact hHNle.trans (le_of_eq hNM)
  let k : CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Sec7Core4 G :=
    CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Sec7Core4.ofThree
      (standingOfS168e3Std s) D.M D.maxLocal p hpp hp2 hsp hUniq
  have hG3 :=
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.gls3StronglyThreeEmbeddedPlus_holds
  have hSE3 :
      CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.StronglyEmbeddedThree :=
    CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.StronglyEmbeddedThree_of_KIB hG3
      CFSG.AGLEmbedding.kFactCatalogSchreier_holds
      (CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.StronglyEmbeddedThreeKIB_of_small
        hG3 CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.KIB3Small_holds)
  rcases eq_or_ne p 3 with rfl | hp3
  · exact k.conclusion76_of_stronglyEmbeddedThree rfl hSE3 r hr E hEM hEel hEcard hcent hXsub
  · exact k.conclusion76_of_kIDExcluded
      (hpp.five_le_of_ne_two_of_ne_three hp2 hp3)
      (k.kIDExcluded_of_evenRank_le_three (le_of_eq s.h3))
      CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive.stronglyEmbeddedFive_holds
      r hr E hEM hEel hEcard hcent hXsub


end

section


theorem r72_of_s168e3Std {D : Data G} (s : S168e3Std D) : UC22.F07.R72 D := by
  intro p H h7
  have hUniq : ∀ U : Subgroup G, U ≠ ⊥ → IsPGroup 2 U →
      2 ≤ CFSG.Open.pRank p (Subgroup.normalizer (U : Set G) ⊓ D.M) → Subgroup.normalizer (U : Set G) ≤ D.M :=
    CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.R72.normalizer_le_of_theoremCAt
      (M := D.M) (theoremCAt_of_r6_3 D s.h63) h7.1 h7.2.1 h7.2.2.1
  let k : CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Sec7Core4 G :=
    CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Sec7Core4.ofThree
      (standingOfS168e3Std s) D.M D.maxLocal p h7.1 h7.2.1 h7.2.2.1 hUniq
  have hHk : k.Config H :=
    CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.R72.config_of_sec7Hyp k h7 rfl
  exact CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.R72.r72_of_core
    UCK.kFactSmallIdent_holds UCK.kFactOneLieIdent_holds
    UCK.stronglyEmbeddedCyclicOuter_holds
    (CFSG.AGLEmbedding.kFactSmallOutPPrime_of_smallIdent UCK.kFactSmallIdent_holds)
    CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group
    (fun _ _ _ => CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.R72.isReeType_one_of_psl28)
    k
    (fun hp5 => ⟨k.kIDExcluded_of_evenRank_le_three (le_of_eq s.h3),
      k.step75 hp5 CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive.stronglyEmbeddedFive_holds⟩)
    hHk
    (fun hp3 => k.exists_rows3_of_config
      CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.gls3StronglyThreeEmbeddedPlus_holds
      CFSG.AGLEmbedding.kFactReeInvolution hp3 hHk)

end

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
