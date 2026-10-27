module

public import CFSG.RankThree.PartTwo.Sec4.Item462AltProofKChevTwoL2
public import CFSG.RankThree.PartTwo.Sec4.Item462AltProofKSLThree
public import CFSG.RankThree.PartTwo.Sec4.RonanKChevTwoDFour
public import CFSG.RankThree.PartTwo.Sec4.RonanKChevTwoDFourThreeA
public import CFSG.RankThree.PartTwo.Sec4.RonanKChevTwoGTwo
public import CFSG.RankThree.PartTwo.Sec4.RonanKChevTwoLThree
public import CFSG.RankThree.PartTwo.Sec4.RonanKChevTwoReeF4
public import CFSG.RankThree.PartTwo.Sec4.RonanKChevTwoSpFour
public import CFSG.RankThree.PartTwo.Sec4.RonanKChevTwoSuzuki
public import CFSG.RankThree.PartTwo.Sec4.RonanKChevTwoUThree

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanKChevTwo

open CFSG CFSG.RankThree.PartTwo.Sec4.Item462AltProof
open CFSG.Assembly.RankThreeEven (projSU)

private theorem two_pow_mod_three_cases (m : ℕ) : 2 ^ m % 3 = 1 ∨ 2 ^ m % 3 = 2 := by
  have h : ¬ 3 ∣ 2 ^ m := fun h => by
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h)
    omega
  omega

private theorem two_pow_two_mul_mod_three (m : ℕ) : 2 ^ (2 * m) % 3 = 1 := by
  rw [pow_mul, Nat.pow_mod]
  norm_num

theorem kChevTwo_statedSU_of_mod_two (m : ℕ) (hm : 1 ≤ m) (hq : 2 ^ m % 3 = 2) :
    ∀ (X : Type) [Group X] [Finite X], IsQuasisimple X →
      (∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = (2 ^ m) ^ 2 ∧
        Nonempty (X ≃* CFSG.Assembly.LowTwoRank.StatedSU 3 (2 ^ m) K)) →
      ∀ β : MulAut X, orderOf β = 3 → ¬ InnThetaNoncyclic β := by
  intro X _ _ hXq ⟨K, hF, hFin, hK, he⟩ β hβ hθ
  exact (KSLThree.kSLThreeCentralizerQ_holds X hXq 2 m hm
    (Or.inl ⟨K, hF, hFin, Or.inr ⟨hK, hq, he⟩⟩) β hβ hθ).1 rfl

theorem kChevTwo_projSU_of_mod_two (m : ℕ) (hm : 1 ≤ m) (hq : 2 ^ m % 3 = 2) :
    ∀ (X : Type) [Group X] [Finite X], IsQuasisimple X → Nonempty (X ≃* projSU 3 2 m) →
      ∀ β : MulAut X, orderOf β = 3 → ¬ InnThetaNoncyclic β := by
  intro X _ _ hXq he β hβ hθ
  exact (KSLThree.kSLThreeCentralizerQ_holds X hXq 2 m hm (Or.inr (Or.inr ⟨hq, he⟩)) β hβ
    hθ).1 rfl

theorem kChevTwo_statedSL (m : ℕ) (hm : 1 ≤ m) :
    ∀ (X : Type) [Group X] [Finite X], IsQuasisimple X →
      (∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ (2 * m) ∧
        Nonempty (X ≃* CFSG.Assembly.LowTwoRank.StatedSL 3 K)) →
      ∀ β : MulAut X, orderOf β = 3 → ¬ InnThetaNoncyclic β := by
  intro X _ _ hXq ⟨K, hF, hFin, hK, he⟩ β hβ hθ
  exact (KSLThree.kSLThreeCentralizerQ_holds X hXq 2 (2 * m) (by omega)
    (Or.inl ⟨K, hF, hFin, Or.inl ⟨hK, two_pow_two_mul_mod_three m, he⟩⟩) β hβ hθ).1 rfl

end CFSG.RankThree.PartTwo.Sec4.RonanKChevTwo

namespace CFSG.RankThree.PartTwo.Sec4

open Item462AltProof RonanKChevTwo

theorem kChevTwoCentralizer_holds :
    KChevTwoCentralizer := by
  intro X _ _ hXq hX β hβ
  rcases hX with (⟨m, hm, h⟩ | ⟨n, hn, h⟩) | ⟨n, hn, h⟩
  · rcases h with h | h | h | h
    · exact ChevTwoL2.kChevTwoCentralizer_psl2 m hm X hXq h β hβ
    · rcases two_pow_mod_three_cases m with hq | hq
      · exact kChevTwo_statedSU_three m hm hq X hXq h β hβ
      · exact kChevTwo_statedSU_of_mod_two m hm hq X hXq h β hβ
    · rcases two_pow_mod_three_cases m with hq | hq
      · exact kChevTwo_projSU_three m hm hq X hXq h β hβ
      · exact kChevTwo_projSU_of_mod_two m hm hq X hXq h β hβ
    · exact kChevTwo_statedSL m hm X hXq h β hβ
  · rcases h with h | h | h | h | h
    · exact kChevTwo_suzuki n hn X hXq h β hβ
    · exact kChevTwo_projSL_three n hn X hXq h β hβ
    · exact kChevTwo_projSp_two n hn X hXq h β hβ
    · exact kChevTwo_gTwo n hn X hXq h β hβ
    · exact kChevTwo_reeF4 n hn X hXq h β hβ
  · exact kChevTwo_trialityD4_of_threeA dFourThreeAKill_holds n hn X hXq h β hβ

end CFSG.RankThree.PartTwo.Sec4

end
