module

public import CFSG.RankThree.PartOne.Census3.Interface
public import CFSG.Assembly.LowTwoRankDefs
import CFSG.RankThree.PartTwo.Census.OddClassical.UnitaryWitness
import CFSG.RankThree.PartTwo.Census.Classical.EvenWitness
import CFSG.RankThree.PartTwo.Census.Classical.EvenPrimes
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Index

public section

namespace CFSG.RankThree.PartOne.Census3

open CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.Assembly.LowTwoRank
  CFSG.RankThree.PartTwo.Census CFSG.ClassicalGroups.UnitaryFlag TauCeti

@[expose] def LocalRankThreeU68 : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 64 →
    4 ≤ localRank 3 (StatedProj (StatedSU 6 8 K))

theorem excludedIndex_twistedA_of_four_le (r : ℕ) (q : PrimePower)
    (hv : (LieTypeIndex.twistedA r q).Valid) [Fact q.p.Prime] {s : ℕ} (hs : s.Prime)
    (hs2 : s ≠ 2)
    (h : 4 ≤ localRank s (StatedProj (StatedSU (r + 1) (q.p ^ q.exponent)
      (GaloisField q.p (2 * q.exponent))))) : ExcludedIndex (.lie ⟨.twistedA r q, hv⟩) :=
  excludedIndex_of_equiv (T := StatedProj (StatedSU (r + 1) (q.p ^ q.exponent)
      (GaloisField q.p (2 * q.exponent))))
    (fun _ => ⟨CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj r q hv⟩) hs hs2 h

theorem theoremThreeCase_twistedA_odd (r : ℕ) (q : PrimePower)
    (hv : (LieTypeIndex.twistedA r q).Valid) (hq : q.p ≠ 2) :
    TheoremThreeCase (.lie ⟨.twistedA r q, hv⟩) := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hr2 : 2 ≤ r :=
    LieTypeIndex.two_le_of_twistedA_inStandardRange ((LieTypeIndex.valid_iff _).mp hv).1
  have hu := unitaryFieldData_galoisField q.p q.exponent q.exponent_pos
  have hf1 := q.exponent_pos
  have hwit : ∀ k, k ≤ localRank q.p (unitaryPSU hu (r + 1)) → 4 ≤ k →
      TheoremThreeCase (.lie ⟨.twistedA r q, hv⟩) := by
    intro k hk h4
    refine (excludedIndex_twistedA_of_four_le r q hv q.prime_p hq ?_).case
    rw [← localRank_eq_of_mulEquiv (unitaryPSUEquiv hu (n := r + 1) (by omega)) q.prime_p]
    omega
  rcases (show r = 2 ∨ r = 3 ∨ 4 ≤ r by omega) with rfl | rfl | hr4
  ·
    by_cases hf : q.exponent ≤ 3
    · exact fun G _ _ _ e => TheoremThreeList.of_twistedA2_odd hv hq hf e
    · exact hwit _ (le_localRank_unitaryPSU hu hq (n := 2 + 1) (r := 1) le_rfl (by norm_num))
        (by rw [one_pow, mul_one]; omega)
  ·
    by_cases hf : q.exponent = 1
    · exact fun G _ _ _ e => TheoremThreeList.of_twistedA3_prime hv hq hf e
    · exact hwit _ (le_localRank_unitaryPSU_four hu hq) (by omega)
  ·
    exact hwit _ (le_localRank_unitaryPSU hu hq (n := r + 1) (r := 2) (by norm_num) (by omega))
      (by norm_num; omega)

theorem theoremThreeCase_twistedA_even (hU68 : LocalRankThreeU68) (r : ℕ) (q : PrimePower)
    (hv : (LieTypeIndex.twistedA r q).Valid) (hq : q.p = 2) :
    TheoremThreeCase (.lie ⟨.twistedA r q, hv⟩) := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have : CharP (GaloisField q.p (2 * q.exponent)) 2 := CharP.congr q.p hq
  have hr2 : 2 ≤ r :=
    LieTypeIndex.two_le_of_twistedA_inStandardRange ((LieTypeIndex.valid_iff _).mp hv).1
  have hu := unitaryFieldData_galoisField q.p q.exponent q.exponent_pos
  have hf1 := q.exponent_pos
  rcases (show r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ 6 ≤ r by omega) with rfl | rfl | rfl | rfl | hr6
  · exact fun G _ _ _ e => TheoremThreeList.of_twistedA2_even hv hq e
  · exact fun G _ _ _ e => TheoremThreeList.of_twistedA3_even hv hq e
  · exact fun G _ _ _ e => TheoremThreeList.of_twistedA4_even hv hq e
  · rcases (show q.exponent = 1 ∨ q.exponent = 3 ∨ (2 ≤ q.exponent ∧ q.exponent ≠ 3) by omega)
      with hf | hf | ⟨hf2, hf3⟩
    ·
      exact fun G _ _ _ e => TheoremThreeList.of_twistedA5_two hv hq hf e
    ·
      refine (excludedIndex_twistedA_of_four_le 5 q hv Nat.prime_three (by norm_num) ?_).case
      have hK : Nat.card (GaloisField q.p (2 * q.exponent)) = 64 := by
        rw [GaloisField.card _ _ (by omega), hq, hf]
        norm_num
      have h8 : q.p ^ q.exponent = 8 := by
        rw [hq, hf]
        norm_num
      rw [h8]
      exact hU68 _ hK
    ·
      obtain ⟨s, hs, hs5, hsd⟩ := exists_prime_five_le_dvd_two_pow_add_one hf2 hf3
      refine (excludedIndex_twistedA_of_four_le 5 q hv hs (by omega) ?_).case
      refine le_localRank_statedSU_torus (k := 3) hu hs (by rw [hq]; exact hsd) (by norm_num)
        (Or.inr fun h6 => ?_)
      have hs6 := Nat.le_of_dvd (by norm_num) h6
      interval_cases s
      · exact absurd h6 (by norm_num)
      · exact absurd hs (by norm_num)
  ·
    obtain ⟨s, hs, hs2, hsd⟩ := exists_odd_prime_dvd_two_pow_add_one hf1
    refine (excludedIndex_twistedA_of_four_le r q hv hs hs2 ?_).case
    exact le_localRank_statedSU_torus (k := 3) hu hs (by rw [hq]; exact hsd) (by omega)
      (Or.inl (by omega))

theorem theoremThreeCase_twistedA (hU68 : LocalRankThreeU68) (r : ℕ) (q : PrimePower)
    (hv : (LieTypeIndex.twistedA r q).Valid) : TheoremThreeCase (.lie ⟨.twistedA r q, hv⟩) := by
  by_cases hq : q.p = 2
  · exact theoremThreeCase_twistedA_even hU68 r q hv hq
  · exact theoremThreeCase_twistedA_odd r q hv hq

end CFSG.RankThree.PartOne.Census3
