module

public import CFSG.RankThree.PartTwo.KFacts.KS12MovesSL
import CFSG.Sporadic.Mathieu.M22
public import CFSG.RankThree.PartTwo.KFacts.KS12Covers
public import CFSG.RankThree.PartTwo.KFacts.KS12Moves

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo

theorem exists_normalizer_moves_of_isTripleCover_M22 {X : Type} [Group X] [Finite X]
    (hq : IsQuasisimple X) (hX : Sec4.IsTripleCover X Blueprint.NativeSporadic.M22)
    (T : Subgroup X) (hT9 : Nat.card T = 9) :
    ∃ x ∈ Subgroup.normalizer (T : Set X), IsPGroup 3 (Subgroup.zpowers x) ∧
      ∃ t ∈ T, x * t * x⁻¹ ≠ t := by
  have hp : commutator X = ⊤ := by
    have h := hq.1
    rwa [Group.isPerfect_def] at h
  have hcard := card_of_isTripleCover hX
  rw [CFSG.Sporadic.Mathieu.card_M22] at hcard
  refine exists_normalizer_moves_of_factorization hp hX.1 ?_ T hT9
  rw [hcard, show (443520 : ℕ) = 9 * 49280 by norm_num]
  exact factorization_three_mul_nine_mul (by norm_num)

theorem ks12NormalizerMoves : KS12NormalizerMoves := by
  intro X _ _ hq hX T hT hT9 hZT
  rcases hX with hSL | hA6 | hA7 | hM22
  · exact exists_normalizer_moves_of_isSLThreePi hSL T hT hT9 hZT
  · exact exists_normalizer_moves_of_isTripleCover_alt hq (Or.inl hA6) T hT9
  · exact exists_normalizer_moves_of_isTripleCover_alt hq (Or.inr hA7) T hT9
  · exact exists_normalizer_moves_of_isTripleCover_M22 hq hM22 T hT9

end CFSG.RankThree.PartTwo.KFacts
