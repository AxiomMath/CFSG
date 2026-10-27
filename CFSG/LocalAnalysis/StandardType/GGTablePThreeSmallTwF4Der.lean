module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeSmallDefs
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly

section TitsRankTwo

theorem svRankTwF4der_holds :
    SVRank (fun t => t = .twF4der) := by
  intro lab hlab ht
  have hs : LargeEvenSplit 3 lab := by
    obtain ⟨t, l, n⟩ := lab
    dsimp only at ht
    subst ht
    dsimp only [LargeEvenInLambda2] at hlab
    exact Or.inr (Or.inr (Or.inr ⟨hlab.2.2, rfl⟩))
  have hcard := CFSG.StandardType.TableBExcSmallRest.largeEvenLabelAll_card_lt_twF4der_holds
    (p := 3) Nat.prime_three hlab ht hs
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht
  subst ht
  intro Q hQ
  have hrec := hcard Q hQ
  dsimp only [LargeEvenRawDatum, LargeEvenRecipeTwF4] at hrec
  obtain ⟨K, i1, i2, hK, hQh, hP1⟩ := hrec
  dsimp only [LargeEvenRawDatum, LargeEvenRecipeTwF4]
  refine ⟨K, i1, i2, hK, hQh, ?_⟩
  intro _hsimple _hnonab B hB hBcl
  have hlt : Nat.card B < 3 ^ 3 := hP1 B (by
    intro x hx
    unfold LargeEvenChevIDImage at hBcl
    rw [Subgroup.closure_eq] at hBcl
    exact hBcl hx) hB
  by_cases hfin : Finite B
  · haveI : Finite B := hfin
    obtain ⟨k, hk⟩ := (CFSG.Open.IsElemAbelian.isPGroup hB).exists_card_eq
    rw [hk] at hlt ⊢
    have hk2 : k ≤ 2 := Nat.lt_succ_iff.mp ((Nat.pow_lt_pow_iff_right (by norm_num)).mp hlt)
    calc 3 ^ k ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) hk2
      _ = 9 := by norm_num
  · haveI : Infinite B := ⟨hfin⟩
    rw [Nat.card_eq_zero_of_infinite]
    norm_num

end TitsRankTwo

end CFSG.StandardType.TablePThreeKG

end
