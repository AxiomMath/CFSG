module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Theorem8108
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.OppNormalizer
public import CFSG.LocalAnalysis.UniquenessCase.UCFront07Use
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFiftyNine
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointSetup
public import CFSG.GroupTheory.PGroup.CardCoprime
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Theorem76
public import CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.Aut

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped commutatorElement

open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 PartIAt)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.PartOne (IsSL3Four)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
  (Conclusion76 StronglyEmbeddedFive Sec7Core4 five_le_of_mem_uniqueFourSigma)

variable {G : Type} [Group G] [Finite G]

theorem exists_gamma_le_of_isSL3Four
    (hS : Standing4 G) (hU : CFSG.Open.uniqueFourUnique G) (S : Setup4 G)
    (hMS : S.InMSigma) (hPart : CFSG.Yardstones.Mf4cdcdf2e013.PartIAt S.M)
    (hnot : ¬ CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 S.M)
    (hSE : StronglyEmbeddedFive)
    {L : Subgroup G} (hL : L ∈ CFSG.LocalAnalysis.UniquenessCase.UC22.calC S.M)
    (hc2 : (conjSetOf S.M L).ncard ≤ 2)
    (hSL : CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.PartOne.IsSL3Four
      (CFSG.LocalAnalysis.UniquenessCase.UC22.Bar2 L)) :
    ∃ R : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 3 R L ∧
      CFSG.Open.rankThreeGamma 1 3 R ≤ S.M := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact S.p.Prime := ⟨S.hp.1.1⟩
  have h3β : 3 ∉ CFSG.Open.uniqueFourBeta G :=
    three_not_mem_uniqueFourBeta_of_not_strong hU S hMS hnot
  have hp5 : 5 ≤ S.p := five_le_of_mem_uniqueFourSigma S.hp h3β
  have hp2 : S.p ≠ 2 := S.hp.1.2.1
  have hp3 : S.p ≠ 3 := by
    intro h
    exact h3β (h ▸ S.hp.1)
  have hLM : L ≤ S.M := hL.1.le
  have hLrank_le : CFSG.Open.pRank 3 L ≤ 2 := by
    by_contra h
    exact hnot (isStronglyPEmbedded_three_of_calC_three_le hS S hPart hL (by omega))
  have hLrank_ge : 2 ≤ CFSG.Open.pRank 3 L := by
    rw [← CFSG.LocalAnalysis.UniquenessCase.UC22.pRank_bar2_eq_of_odd
      (Y := L) (p := 3) Nat.prime_three (by norm_num : (3 : ℕ) ≠ 2)]
    refine CFSG.GroupTheory.two_le_pRank_of_quotient (Y := Bar2 L)
      (N := Subgroup.center (Bar2 L)) (p := 3) Nat.prime_three
      (by norm_num : (3 : ℕ) ≠ 2) ?_
    obtain ⟨K, hfield, hfin, hKcard, ⟨e⟩⟩ :=
      CFSG.RankThree.PartOne.AUTSL.exists_projectiveSL_equiv_of_lieModel hSL.1.2
    letI := hfield
    letI := hfin
    have hk : Nat.card K = 4 := by rw [hKcard]; norm_num
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) e]
    simpa only [CFSG.SectionRank.pRank_eq_open_pRank_top] using
      (CFSG.RankThree.PartTwo.KFacts.L34.pRank_three_projectiveSL hk).ge
  have hLrank : CFSG.Open.pRank 3 L = 2 := le_antisymm hLrank_le hLrank_ge
  obtain ⟨R, hR⟩ := CFSG.ABGLocalTools.exists_isSylowOf (p := 3) L
  refine ⟨R, hR, ?_⟩
  have hRrankEq : CFSG.Open.pRank 3 R = CFSG.Open.pRank 3 L :=
    CFSG.LocalAnalysis.RankFourTheoremC.pRank_eq_of_isSylowOf Nat.prime_three hR
  have hRrank : 2 ≤ CFSG.Open.pRank 3 R := by
    simp [hRrankEq, hLrank]
  have hRM : R ≤ S.M := hR.le.trans hLM
  set N : Subgroup G := S.M ⊓ Subgroup.normalizer (L : Set G) with hNdef
  have hNle : N ≤ Subgroup.normalizer (L : Set G) := inf_le_right
  have hMN : CFSG.Open.pRank S.p S.M = CFSG.Open.pRank S.p N := by
    refine le_antisymm ?_ (CFSG.SectionRank.pRank_mono (Fact.out : S.p.Prime).one_lt inf_le_left)
    obtain ⟨E, hEM, hEel, hEcard⟩ :=
      CFSG.SectionRank.exists_pRank (Fact.out : S.p.Prime).one_lt S.M
    have hEN : E ≤ N := by
      refine le_inf hEM ?_
      rw [Subgroup.le_normalizer_iff]
      intro x hx y hy
      have hxM : x ∈ S.M := hEM hx
      have hpow : x ^ S.p = 1 := hEel.2 x hx
      have hodd : Odd (orderOf x) := by
        have hdvd : orderOf x ∣ S.p := orderOf_dvd_of_pow_eq_one hpow
        rcases (Nat.dvd_prime (Fact.out : S.p.Prime)).mp hdvd with h1 | hSp
        · rw [h1]; norm_num
        · rw [hSp]
          exact (Fact.out : S.p.Prime).odd_of_ne_two hp2
      exact (Subgroup.mem_normalizer_iff.mp
        (mem_normalizer_of_ncard_conjSetOf_le_two_of_odd_order hc2 hxM hodd) y).mp hy
    exact CFSG.SectionRank.le_pRank (Fact.out : S.p.Prime).one_lt hEN hEel hEcard
  have hrankIneq := CFSG.GroupTheory.pRank_le_pRank_map_ker_add_pRank_range
    (p := 2) (q := S.p) (Fact.out : S.p.Prime) L N hNle
  have hcardAut : Nat.card (MulAut (Bar2 L ⧸ Subgroup.center (Bar2 L))) =
      2 ^ 8 * 3 ^ 3 * 5 * 7 := by
    obtain ⟨K, hfield, hfin, hKcard, ⟨e⟩⟩ :=
      CFSG.RankThree.PartOne.AUTSL.exists_projectiveSL_equiv_of_lieModel hSL.1.2
    letI := hfield
    letI := hfin
    have hk : Nat.card K = 4 := by rw [hKcard]; norm_num
    rw [Nat.card_congr (MulAut.congr e).toEquiv,
      CFSG.RankThree.PartTwo.KFacts.L34.card_mulAut hk]
    norm_num
  have hrange : CFSG.Open.pRank S.p
      (CFSG.GroupTheory.conjModPCore 2 L N hNle).range ≤ 1 := by
    refine (CFSG.SectionRank.pRank_mono (Fact.out : S.p.Prime).one_lt le_top).trans ?_
    have hperf : Group.IsPerfect (Bar2 L) := Group.isPerfect_def.mpr hSL.1.1.1
    haveI : Group.IsPerfect (Bar2 L) := hperf
    refine (CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.pRank_mulAut_le
      (J := Bar2 L) (Fact.out : S.p.Prime)).trans ?_
    refine CFSG.QuasithinUnique.Id2519.pRank_le_one_of_not_sq_dvd
      (Fact.out : S.p.Prime) ?_
    rw [hcardAut]
    exact CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.prime_sq_not_dvd_aut_L34
      (Fact.out : S.p.Prime) hp2 hp3
  obtain ⟨Sₚ, hSₚ⟩ := CFSG.ABGLocalTools.exists_isSylowOf (p := S.p)
    ((CFSG.GroupTheory.conjModPCore 2 L N hNle).ker.map N.subtype)
  have hSpRank : CFSG.Open.pRank S.p Sₚ =
      CFSG.Open.pRank S.p
        ((CFSG.GroupTheory.conjModPCore 2 L N hNle).ker.map N.subtype) :=
    CFSG.LocalAnalysis.RankFourTheoremC.pRank_eq_of_isSylowOf
      (Fact.out : S.p.Prime) hSₚ
  have hSpK : Sₚ ≤ (CFSG.GroupTheory.conjModPCore 2 L N hNle).ker.map N.subtype := hSₚ.le
  have hSpM : Sₚ ≤ S.M := (hSpK.trans (Subgroup.map_subtype_le _)).trans inf_le_left
  have hSpN : Sₚ ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
    (hSpK.trans (Subgroup.map_subtype_le _)).trans
      (hNle.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf (r := 2) L))
  have hRN : R ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
    hR.le.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf (r := 2) L)
  have hcomm : ⁅Sₚ, R⁆ ≤ pCoreOf 2 L := by
    rw [Subgroup.commutator_le]
    intro s hs r hr
    have hsK : s ∈ (CFSG.GroupTheory.conjModPCore 2 L N hNle).ker.map N.subtype := hSpK hs
    have hmem := ((CFSG.GroupTheory.mem_map_ker_conjModPCore_iff 2 L N hNle).1 hsK).2
      r (hR.le hr)
    simpa [commutatorElement_def] using hmem
  have hpCore : ¬ S.p ∣ Nat.card (pCoreOf 2 L) :=
    CFSG.GroupTheory.not_dvd_card_of_isPGroup
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) L)
      (Fact.out : S.p.Prime) hp2
  have h3Core : ¬ 3 ∣ Nat.card (pCoreOf 2 L) :=
    CFSG.GroupTheory.not_dvd_card_of_isPGroup
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) L)
      Nat.prime_three (by norm_num : (3 : ℕ) ≠ 2)
  have hkey : 2 ≤ CFSG.Open.pRank S.p
      (S.M ⊓ Subgroup.centralizer (R : Set G)) := by
    have hKle : CFSG.Open.pRank S.p
        ((CFSG.GroupTheory.conjModPCore 2 L N hNle).ker.map N.subtype) ≤
        CFSG.Open.pRank S.p (S.M ⊓ Subgroup.centralizer (R : Set G)) := by
      rw [← hSpRank]
      exact CFSG.GroupTheory.pRank_le_pRank_inf_centralizer_of_commutator_le
        (p := S.p) (q := 3) (M := S.M) (N := pCoreOf 2 L)
        (R := Sₚ) (B := R) hSpM
        ((CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans hLM)
        hSpN hRN hSₚ.isPGroup hR.isPGroup hpCore h3Core hcomm
    have h4 : 4 ≤ CFSG.Open.pRank S.p S.M :=
      CFSG.LocalAnalysis.UniquenessCase.UC6.four_le_pRank_of_sigma S.hp
    omega
  have hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded S.p S.M :=
    isStronglyPEmbedded_of_mem_sigma_of_calC hS hU S hL S.hp
  have h76 : Conclusion76 S.M S.p :=
    (Sec7Core4.ofSetup4 hS hU S S.hp hsp h3β).conclusion76 hp5 h3β hSE
  exact CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.rankThreeGamma_le_of_two_le_pRank_inf_centralizer
    hsp h76 hRM hR.isPGroup hRrank hkey

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
