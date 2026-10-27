module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.TransferCentralizer108
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.GammaQ108
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Theorem76

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
  (Conclusion76 StronglyEmbeddedFive Sec7Core4 five_le_of_mem_uniqueFourSigma)
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 TheoremCAt)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.PartOne (IsSL3Four)

variable {G : Type} [Group G] [Finite G]

theorem rankThreeGamma_le_of_e9_le_X
    (hS : Standing4 G) (hU : CFSG.Open.uniqueFourUnique G) (S : Setup4 G)
    (hMS : S.InMSigma) (hC : CFSG.Yardstones.Mf4cdcdf2e013.TheoremCAt S.M)
    (hnot : ¬ CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 S.M)
    (hSE : StronglyEmbeddedFive)
    {L L' : Subgroup G} (hL : L ∈ CFSG.LocalAnalysis.UniquenessCase.UC22.calC S.M)
    (hset : CFSG.LocalAnalysis.UniquenessCase.UC22.conjSetOf S.M L = {L, L'})
    (hSL : CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.PartOne.IsSL3Four
      (CFSG.LocalAnalysis.UniquenessCase.UC22.Bar2 L))
    {E : Subgroup G} (hEX : E ≤ CFSG.LocalAnalysis.UniquenessCase.UC22.conjClosure S.M L)
    (hEel : CFSG.Open.IsElemAbelian 3 E) (hEcard : Nat.card E = 9) :
    CFSG.Open.rankThreeGamma 1 3 E ≤ S.M := by
  classical
  haveI : Fact S.p.Prime := ⟨S.hp.1.1⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hXM : CFSG.LocalAnalysis.UniquenessCase.UC22.conjClosure S.M L ≤ S.M :=
    (uc22p22u_conjClosure_isProd (M := S.M) (X := S.M) (K := L)
      le_rfl Subgroup.le_normalizer hL).1
  have hEM : E ≤ S.M := hEX.trans hXM
  have hB : IsPGroup 3 E := CFSG.Open.IsElemAbelian.isPGroup hEel
  have hBr : 2 ≤ CFSG.Open.pRank 3 E := by
    refine CFSG.SectionRank.le_pRank (p := 3) (by norm_num : 1 < 3) le_rfl hEel ?_
    rw [hEcard]
    norm_num
  have hF : 2 ≤ CFSG.Open.pRank S.p
      (S.M ⊓ Subgroup.centralizer (E : Set G)) :=
    two_le_pRank_centralizer_of_e9_le_X hS hU S hMS hnot hL hset hSL hEX hEel hEcard
  have h3β : 3 ∉ CFSG.Open.uniqueFourBeta G :=
    three_not_mem_uniqueFourBeta_of_not_strong hU S hMS hnot
  have hp5 : 5 ≤ S.p := five_le_of_mem_uniqueFourSigma S.hp h3β
  have hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded S.p S.M :=
    isStronglyPEmbedded_of_mem_sigma_of_calC hS hU S hL S.hp
  have h76 : Conclusion76 S.M S.p :=
    (Sec7Core4.ofSetup4 hS hU S S.hp hsp h3β).conclusion76 hp5 h3β hSE
  exact CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.rankThreeGamma_le_of_two_le_pRank_inf_centralizer
    hsp h76 hEM hB hBr hF

theorem rankThreeGamma_Q_le_of_le_X
    (hS : Standing4 G) (hU : CFSG.Open.uniqueFourUnique G) (S : Setup4 G)
    (hMS : S.InMSigma) (hC : CFSG.Yardstones.Mf4cdcdf2e013.TheoremCAt S.M)
    (hnot : ¬ CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 S.M)
    (hSE : StronglyEmbeddedFive)
    {L L' : Subgroup G} (hL : L ∈ CFSG.LocalAnalysis.UniquenessCase.UC22.calC S.M)
    (hset : CFSG.LocalAnalysis.UniquenessCase.UC22.conjSetOf S.M L = {L, L'})
    (hSL : CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.PartOne.IsSL3Four
      (CFSG.LocalAnalysis.UniquenessCase.UC22.Bar2 L))
    {Q : Subgroup G} (hQX : Q ≤ CFSG.LocalAnalysis.UniquenessCase.UC22.conjClosure S.M L)
    (hQp : IsPGroup 3 Q) (hQexp : ∀ x ∈ Q, x ^ 3 = 1)
    (hE9contain : ∀ x ∈ Q, x ≠ 1 → ∃ E : Subgroup G, x ∈ E ∧ E ≤ Q ∧
      CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 9) :
    CFSG.Open.rankThreeGamma 1 3 Q ≤ S.M := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h63 : CFSG.LocalAnalysis.UniquenessCase.UC6.R6_3
      (CFSG.LocalAnalysis.UniquenessCase.UC6.dataOfSetup4 hS hU S) :=
    CFSG.LocalAnalysis.UniquenessCase.UC6.r6_3_dataOfSetup4 hS hU S hC
  have hE9 : ∀ E : Subgroup G, E ≤ Q → CFSG.Open.IsElemAbelian 3 E →
      Nat.card E = 9 → CFSG.Open.rankThreeGamma 1 3 E ≤ S.M := by
    intro E hEQ hEel hEcard
    exact rankThreeGamma_le_of_e9_le_X hS hU S hMS hC hnot hSE hL hset hSL
      (hEQ.trans hQX) hEel hEcard
  refine rankThreeGamma_one_le_of_forall_e9 hQexp hE9contain hE9 ?_
  intro E hEM hEel hEcard hΓ
  have h := h63 3 Nat.prime_three (by norm_num : (3 : ℕ) ≠ 2) E hEM hEel
    (by rw [hEcard]; norm_num) hΓ
  simpa [CFSG.LocalAnalysis.UniquenessCase.UC6.dataOfSetup4] using h

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
