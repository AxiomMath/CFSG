module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UC147Local
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UC147CaseTwo
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerPClosure

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup CFSG.Open CFSG.LocalAnalysis.RankThreeUC CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC22.F08
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 PartIAt)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
  (relPPrimeCore_le relPPrimeCore_normal coprime_card_relPPrimeCore)

variable {G : Type} [Group G] [Finite G]

namespace Ctx147

variable {D : Data G} {L : Fin 2 → Subgroup G} {n : Fin 2 → ℕ} {r p : ℕ} {A X B R : Subgroup G}

theorem eq_of_mem_calMOf (c : Ctx147 D L n r p A X B R)
    (hsp3 : IsStronglyPEmbedded 3 D.M)
    (hU4b : ∀ H : Subgroup G, IsTwoLocal H → 2 ≤ CFSG.Open.pRank 3 (H ⊓ D.M) → H ≤ D.M)
    (hRi : ∀ i, R ⊓ L i ∈ uniqueSet D.M) (hKG : KGen147)
    (hSz : CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.KFactSuzukiThreeFree)
    {N : Subgroup G} (hN : N ∈ calMOf (B ⊔ R)) : N = D.M := by
  have hQN : relPPrimeCore 3 N ≤ N := relPPrimeCore_le N
  have hNQ : N ≤ normalizer (relPPrimeCore 3 N : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQN).1 (relPPrimeCore_normal Nat.prime_three N)
  have hQM : relPPrimeCore 3 N ≤ D.M :=
    c.le_M_of_coprime_three hsp3 hRi hSz ((le_sup_left.trans hN.2).trans hNQ)
      ((le_sup_right.trans hN.2).trans hNQ) (coprime_card_relPPrimeCore Nat.prime_three N)
  have hNM : N ≤ D.M :=
    (c.le_relPPrimeCore_sup hsp3 hU4b hRi hKG hN).trans (sup_le hQM inf_le_right)
  exact (hN.1.2 D.M D.maxLocal.1 hNM).symm

theorem uniqueMax_sup (c : Ctx147 D L n r p A X B R)
    (hsp3 : IsStronglyPEmbedded 3 D.M)
    (hU4b : ∀ H : Subgroup G, IsTwoLocal H → 2 ≤ CFSG.Open.pRank 3 (H ⊓ D.M) → H ≤ D.M)
    (hRi : ∀ i, R ⊓ L i ∈ uniqueSet D.M) (hKG : KGen147)
    (hSz : CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.KFactSuzukiThreeFree) :
    UniqueMax D.M (B ⊔ R) :=
  Set.eq_singleton_iff_unique_mem.2 ⟨⟨D.maxLocal, sup_le c.hB c.R_le⟩,
    fun _ hN => c.eq_of_mem_calMOf hsp3 hU4b hRi hKG hSz hN⟩

end Ctx147

theorem uc2_14_7BR_setup4
    (hSE : PartOne.Section7.StronglyEmbeddedFive)
    (hSS : PartOne.Section7.StronglyEmbeddedSolvable)
    (hSE3 : PartOne.Section7.StronglyEmbeddedThree) (hB : PartOne.Section7.BadNoStrongThree)
    (hGL : GL3Excl.GL3Excl) (hKG : KGen147)
    (hSz : CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.KFactSuzukiThreeFree)
    (hS : Standing4 G) (hU : uniqueFourUnique G) (S : Setup4 G) (hMS : S.InMSigma)
    (hPart : PartIAt S.M) (h847 : R847 (UC6.dataOfSetup4 hS hU S)) :
    UC2_14_7BR (UC6.dataOfSetup4 hS hU S) := by
  intro L n r p A X B R hH hc hR hBM hBp hRB
  have c : Ctx147 (UC6.dataOfSetup4 hS hU S) L n r p A X B R := ⟨hH, hc, hR, hBM, hBp, hRB⟩
  have h3 : 3 ∈ uniqueFourSigma S.M := c.three_mem_sig
  have hRi : ∀ i, R ⊓ L i ∈ uniqueSet (UC6.dataOfSetup4 hS hU S).M := by
    refine Fin.forall_fin_two.2 ⟨?_, ?_⟩
    · exact mem_uniqueSet_case8100Three_setup4 hSE hSS hSE3 hB hGL hS hU S hMS hPart h847 hH hc
        (Or.inl inf_le_right) (c.frame.2.2.1 0).1
    · exact mem_uniqueSet_case8100Three_setup4 hSE hSS hSE3 hB hGL hS hU S hMS hPart h847 hH hc
        (Or.inr inf_le_right) (c.frame.2.2.1 1).1
  exact c.uniqueMax_sup (isStronglyPEmbedded_three_of_mem_sigma hU S h3)
    (fun H hH2 h2 => (hU S.M S.maxLocal ⟨3, h3⟩).2 H hH2 ⟨3, h3, h2⟩) hRi hKG hSz

theorem uc2_14_7Three_setup4
    (hSE : PartOne.Section7.StronglyEmbeddedFive)
    (hSS : PartOne.Section7.StronglyEmbeddedSolvable)
    (hSE3 : PartOne.Section7.StronglyEmbeddedThree) (hB : PartOne.Section7.BadNoStrongThree)
    (hGL : GL3Excl.GL3Excl) (hKG : KGen147)
    (hSz : CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.KFactSuzukiThreeFree)
    (hS : Standing4 G) (hU : uniqueFourUnique G) (S : Setup4 G) (hMS : S.InMSigma)
    (hPart : PartIAt S.M) (h847 : R847 (UC6.dataOfSetup4 hS hU S)) :
    UC2_14_7Three (UC6.dataOfSetup4 hS hU S) :=
  uc2_14_7Three_of_BR (uc2_14_7BR_setup4 hSE hSS hSE3 hB hGL hKG hSz hS hU S hMS hPart h847)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
