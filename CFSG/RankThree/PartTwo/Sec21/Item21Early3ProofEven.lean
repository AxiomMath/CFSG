module

public import CFSG.RankThree.PartTwo.Sec21.Item21Early3ProofRep
public import CFSG.RankThree.PartTwo.Sec21.Item21Early3ProofCover
import CFSG.RankThree.PartTwo.Sec6.Item612Local
import CFSG.GroupTheory.ABGDGroups.LinearEmbedding
import CFSG.RankThree.PartTwo.Sec4.Census.DoubleCoverRanksL34
public import CFSG.RankThree.PartTwo.Sec21.Item21Early3ProofTheta

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL)

open Item21EarlyProof Item21Early2Proof Item21Early3Proof

theorem item213CenterRankEven_of
    (h211 : Item211) (h45 : Sec4.Item4_5) (hL34 : Sec4.Census.FourL34NotSLFourOdd) :
    Item213CenterRankEven := by
  intro G _ _ A E U c L hpair hO2 h3Z hθ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hlt
  push Not at hlt
  have hpairs := mem_lThreeStarPairs_iff.mp hpair.mem_pair
  have hLc : L ∈ thetaComponentsAt 3 c := (lZeroStarAt_subset A c) hpairs.2.2.1
  have hLp : Group.IsPerfect L := Sec6.isPerfect_of_mem_thetaComponentsAt hLc
  have hLq : IsQuasisimple (lBar L) := Sec6.isQuasisimple_of_mem_thetaComponentsAt hLc
  have hX : IsBar211 (lBar L) := isBar211_of_case211 (h211 G A E U c L hpair)
  obtain ⟨hTs, hTch, -, -⟩ := solvable_prime_complement_core_characterization (H := L)
    Nat.prime_three
  set T := aschbacherSolvableCore 3 L with hT
  have hTn : T.Normal := Subgroup.normal_of_characteristic T
  have : IsSimpleGroup (lBar L ⧸ Subgroup.center (lBar L)) := hLq.2.1
  have : IsSimpleGroup (L ⧸ centerPre T) := (centerPreEquiv T).isSimpleGroup
  have hTL := theta_commutator_le_oddCore h45 hpair
  obtain ⟨hJq, hZ2, hZnt, ⟨e₀⟩⟩ := isTwoCover_quot_oddCore T hTs hTL (even_iff_two_dvd.mpr
    (even_iff_two_dvd.mp hθ))
  set J := L ⧸ CFSG.oddCore L with hJ
  have hcov : ∀ {S : Type} [Group S], (lBar L ⧸ Subgroup.center (lBar L) ≃* S) →
      Sec4.Census.IsTwoCover J S := fun f =>
    ⟨hJq, hZ2, hZnt, ⟨(e₀.trans (centerPreEquiv T)).trans f⟩⟩
  have hModd : ¬ 2 ∣ Nat.card (CFSG.oddCore L) := fun h =>
    (Nat.not_even_iff_odd.mpr (CFSG.ABGDGroups.odd_card_oddCore L)) (even_iff_two_dvd.mpr h)
  have hrank : CFSG.pRank 2 J = CFSG.Open.pRank 2 (⊤ : Subgroup L) := by
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top]
    exact CFSG.SectionRank.pRank_quotient_eq (CFSG.oddCore L) hModd
  have hJ3 : CFSG.pRank 2 J ≤ 3 := by omega
  rcases center_cases_of_isBar211 hX h3Z with hf | ⟨n, hn2, hne, hf⟩ | hf
  ·
    obtain ⟨f⟩ := hf
    have := four_le_pRank_of_isTwoCover_m22 (hcov f)
    omega
  ·
    obtain ⟨f⟩ := hf
    have hn := le_pRank_of_isTwoCover_psl3 hn2 (hcov f)
    obtain rfl : n = 2 := by
      obtain ⟨k, rfl⟩ := hne
      omega
    have hr3 : CFSG.pRank 2 J = 3 := by omega
    obtain ⟨hcyc, hZ4⟩ := Sec4.Census.DoubleCoverRanksTwo.psl34_center J (hcov f) hr3
    obtain ⟨-, -, -, ⟨e⟩⟩ := hcov f
    have hnq : ¬ IsQuasisimple L := by
      intro hq
      obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := T) 2 (even_iff_two_dvd.mp hθ)
      have hTZ : T ≤ Subgroup.center L := by
        rcases CFSG.LocalCores.quasisimple_normal_subgroups hq hTn with h | h
        · exfalso
          have hsol := hTs
          rw [h] at hsol
          have hsolL : Group.IsSolvable L := Group.isSolvable_of_isSolvable_injective
            (f := (Subgroup.topEquiv (G := L)).symm.toMonoidHom)
            (Subgroup.topEquiv (G := L)).symm.injective
          have : Nontrivial L := ⟨⟨(t : L), 1, fun h1 => by
            rw [← Subgroup.orderOf_coe, h1, orderOf_one] at ht
            exact absurd ht (by norm_num)⟩⟩
          exact Group.IsPerfect.not_isSolvable L hsolL
        · exact h
      have ht1 : (t : L) ≠ 1 := by
        intro h1
        rw [← Subgroup.orderOf_coe, h1, orderOf_one] at ht
        exact absurd ht (by norm_num)
      have hto : orderOf (t : L) = 2 := by rw [Subgroup.orderOf_coe]; exact ht
      have hzn : (Subgroup.zpowers (t : L)).Normal := zpowers_normal_of_mem_center (hTZ t.2)
      have hz2 : IsPGroup 2 (Subgroup.zpowers (t : L)) :=
        IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hto, pow_one])
      have hle : Subgroup.zpowers (t : L) ≤ CFSG.pCore 2 L := le_sSup ⟨hzn, hz2⟩
      rw [hO2, le_bot_iff, Subgroup.zpowers_eq_bot] at hle
      exact ht1 hle
    obtain ⟨hL4, p, hp, hp3, D, hD, hodd⟩ :=
      exists_critical_of_sec21 ks213Order ks213Nine hpair hO2 hnq hX
    have hL3 : CFSG.Open.pRank 2 (⊤ : Subgroup L) = 3 := by omega
    exact false_of_critical_L34 hL34 hL4 hL3 hp hp3 hD hodd hJq hcyc hZ4 e
  ·
    obtain ⟨f⟩ := hf
    have := five_le_pRank_of_isTwoCover_j3 (hcov f)
    omega

theorem item213Center_of_items
    (h211 : Item211) (h45 : Sec4.Item4_5) (hL34 : Sec4.Census.FourL34NotSLFourOdd) :
    Item213Center :=
  item213Center_of_rankEven h211 (item213CenterRankEven_of h211 h45 hL34)

theorem item213_of_items
    (h211 : Item211) (h44 : Sec4.Item4_4) (h45 : Sec4.Item4_5)
    (hL34 : Sec4.Census.FourL34NotSLFourOdd) (hTwo : KS213TwoRank) : Item213 :=
  item213_of h211 h44 h45 ks213Order ks213Nine hTwo (item213Center_of_items h211 h45 hL34)

end CFSG.RankThree.PartTwo.Sec21
