module

import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongOFRCLin
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)

theorem rank_PSL (n : ℕ) (hn : n = 4 ∨ n = 5) {J : Type} [Group J] [Finite J] {p f : ℕ}
    (e : LieModel J .PSL n p f) (hcase : p = 7 ∨ 7 ∣ (p ^ f) ^ 2 - 1) :
    2 ≤ CFSG.Open.pRank 7 (⊤ : Subgroup J) := by
  obtain ⟨hp, hf, hn2, -, -⟩ := e.admissible
  obtain ⟨-, K, hfield, hfinite, hK, ⟨eJ⟩⟩ := e.statedClassicalModel_of_ne_zero (by omega)
  letI : Field K := hfield
  letI : Finite K := hfinite
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (show 1 < 7 by norm_num) eJ]
  by_cases hp7 : p = 7
  · subst hp7
    exact CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL.two_le_pRank_statedProj_PSL
      (p := 7) (n := n) (f₀ := f) (by norm_num) (by norm_num) hn2 hf (Or.inl (by omega)) hK
  · have h7dvd : 7 ∣ (p ^ f) ^ 2 - 1 := hcase.resolve_left hp7
    have h7dvdK : 7 ∣ (Nat.card K) ^ 2 - 1 := by rw [hK]; exact h7dvd
    have hpF : ¬ 7 ∣ Nat.card K := by
      rw [hK]
      intro h
      have h7p : 7 ∣ p := Nat.prime_seven.dvd_of_dvd_pow h
      exact hp7 ((Nat.prime_dvd_prime_iff_eq Nat.prime_seven hp).mp h7p).symm
    have hdiv : ¬ 7 ∣ Nat.gcd n (Nat.card K - 1) := by
      rintro h
      have h7n : 7 ∣ n := h.trans (Nat.gcd_dvd_left n (Nat.card K - 1))
      rcases hn with rfl | rfl <;> omega
    rw [CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL.pRank_statedProj_SL_formula
      (F := K) (p := 7) (n := n) (by norm_num) (by norm_num) (by omega) hpF hdiv]
    split_ifs with h1
    · rcases hn with rfl | rfl <;> norm_num
    · have h7add : 7 ∣ Nat.card K + 1 := by
        have hfac : (Nat.card K) ^ 2 - 1 = (Nat.card K + 1) * (Nat.card K - 1) := by
          rw [← Nat.sq_sub_sq, one_pow]
        rw [hfac] at h7dvdK
        rcases Nat.prime_seven.dvd_mul.mp h7dvdK with h | h
        · exact h
        · exact absurd h h1
      have hzero : ((Nat.card K + 1 : ℕ) : ZMod 7) = 0 :=
        (ZMod.natCast_eq_zero_iff (Nat.card K + 1) 7).2 h7add
      have hneg : (Nat.card K : ZMod 7) = -1 := by
        rw [Nat.cast_add, Nat.cast_one] at hzero
        exact eq_neg_of_add_eq_zero_left hzero
      have hord : orderOf (Nat.card K : ZMod 7) = 2 :=
        (CharP.orderOf_eq_two_iff (R := ZMod 7) 7 (by norm_num)).2 hneg
      rw [hord]
      rcases hn with rfl | rfl <;> norm_num

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg
