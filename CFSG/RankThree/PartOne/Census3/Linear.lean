module

public import CFSG.RankThree.PartOne.Census3.Interface
import CFSG.RankThree.PartOne.Census3.LinearWitness
import CFSG.RankThree.PartTwo.Census.OddClassical.LinearWitness
import CFSG.RankThree.PartTwo.Census.Classical.EvenBlocks
import CFSG.RankThree.PartTwo.Census.Classical.EvenPrimes
import CFSG.Adapters.LinearCatalog

public section

namespace CFSG.RankThree.PartOne.Census3

open CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree.PartTwo.Census TauCeti Matrix

theorem excludedIndex_A_of_four_le (r : ℕ) (q : PrimePower) (hv : (LieTypeIndex.A r q).Valid)
    [Fact q.p.Prime] {s : ℕ} (hs : s.Prime) (hs2 : s ≠ 2)
    (h : 4 ≤ localRank s (ProjectiveSpecialLinearGroup (Fin (r + 1))
      (GaloisField q.p q.exponent))) : ExcludedIndex (.lie ⟨.A r q, hv⟩) :=
  excludedIndex_of_equiv (fun _ => ⟨CFSG.ClassicalModels.linearCatalogCandidateEquivPSL r q hv⟩)
    hs hs2 h

theorem theoremThreeCase_A_odd (r : ℕ) (q : PrimePower) (hv : (LieTypeIndex.A r q).Valid)
    (hq : q.p ≠ 2) : TheoremThreeCase (.lie ⟨.A r q, hv⟩) := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hrange := (LieTypeIndex.inStandardRange_iff _).mp ((LieTypeIndex.valid_iff _).mp hv).1
  have hK : Nat.card (GaloisField q.p q.exponent) = q.p ^ q.exponent :=
    GaloisField.card _ _ q.exponent_pos.ne'
  have hf1 := q.exponent_pos
  rcases (show r = 1 ∨ r = 2 ∨ r = 3 ∨ 4 ≤ r by omega) with rfl | rfl | rfl | hr4
  ·
    refine fun G _ _ _ e => TheoremThreeList.of_A1_odd hv hq ?_ e
    have h4 : 4 ≤ q.card := hrange.2 rfl
    obtain ⟨k, hk⟩ : Odd q.card := by
      rw [PrimePower.card_def]
      exact (q.prime_p.eq_two_or_odd'.resolve_left hq).pow
    omega
  ·
    by_cases hf : q.exponent ≤ 3
    · exact fun G _ _ _ e => TheoremThreeList.of_A2_odd hv hq hf e
    · refine (excludedIndex_A_of_four_le 2 q hv q.prime_p hq ?_).case
      exact le_trans (by omega) (le_localRank_PSL_three (K := GaloisField q.p q.exponent) hq hK)
  ·
    by_cases hf : q.exponent = 1
    · exact fun G _ _ _ e => TheoremThreeList.of_A3_prime hv hq hf e
    · refine (excludedIndex_A_of_four_le 3 q hv q.prime_p hq ?_).case
      exact le_trans (by omega) (le_localRank_PSL_four (K := GaloisField q.p q.exponent) hq hK)
  ·
    refine (excludedIndex_A_of_four_le r q hv q.prime_p hq ?_).case
    exact le_trans (by omega)
      (four_mul_le_localRank_PSL (K := GaloisField q.p q.exponent) (n := r + 1) hq hK (by omega))

theorem theoremThreeCase_A_even (r : ℕ) (q : PrimePower) (hv : (LieTypeIndex.A r q).Valid)
    (hq : q.p = 2) : TheoremThreeCase (.lie ⟨.A r q, hv⟩) := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have : CharP (GaloisField q.p q.exponent) 2 := CharP.congr q.p hq
  have hr1 : 1 ≤ r :=
    ((LieTypeIndex.inStandardRange_iff _).mp ((LieTypeIndex.valid_iff _).mp hv).1).1
  have hU : Nat.card (GaloisField q.p q.exponent)ˣ = 2 ^ q.exponent - 1 := by
    rw [Nat.card_units, GaloisField.card _ _ q.exponent_pos.ne', hq]
  have hf1 := q.exponent_pos
  rcases (show r = 1 ∨ r = 2 ∨ r = 3 ∨ (4 ≤ r ∧ r ≤ 6) ∨ 7 ≤ r by omega) with
    rfl | rfl | rfl | ⟨hr4, hr6⟩ | hr7
  · exact fun G _ _ _ e => TheoremThreeList.of_A1_even hv hq e
  · exact fun G _ _ _ e => TheoremThreeList.of_A2_even hv hq e
  · exact fun G _ _ _ e => TheoremThreeList.of_A3_even hv hq e
  · rcases (show q.exponent = 1 ∨ 2 ≤ q.exponent by omega) with hf | hf2
    ·
      rcases (show r = 4 ∨ r = 5 ∨ r = 6 by omega) with rfl | rfl | rfl
      · exact fun G _ _ _ e => TheoremThreeList.of_A4_two hv hq hf e
      · exact fun G _ _ _ e => TheoremThreeList.of_A5_two hv hq hf e
      · exact fun G _ _ _ e => TheoremThreeList.of_A6_two hv hq hf e
    ·
      obtain ⟨s, hs, hs2, hs5, hsd⟩ := exists_prime_ne_five_dvd_two_pow_sub_one hf2
      refine (excludedIndex_A_of_four_le r q hv hs hs2 ?_).case
      refine le_localRank_PSL_torus hs (by rw [hU]; exact hsd) (by omega) (by omega) ?_
      rcases (show r = 4 ∨ 5 ≤ r by omega) with rfl | hr5
      · exact Or.inr fun h5 => hs5 ((Nat.prime_dvd_prime_iff_eq hs (by norm_num)).mp h5)
      · exact Or.inl (by omega)
  ·
    exact (excludedIndex_A_of_four_le r q hv Nat.prime_three (by norm_num)
      (four_le_localRank_PSL_of_eight_le (by omega))).case

theorem theoremThreeCase_A (r : ℕ) (q : PrimePower) (hv : (LieTypeIndex.A r q).Valid) :
    TheoremThreeCase (.lie ⟨.A r q, hv⟩) := by
  by_cases hq : q.p = 2
  · exact theoremThreeCase_A_even r q hv hq
  · exact theoremThreeCase_A_odd r q hv hq

end CFSG.RankThree.PartOne.Census3
