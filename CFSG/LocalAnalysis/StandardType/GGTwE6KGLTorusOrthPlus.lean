module

public import CFSG.LocalAnalysis.StandardType.GGTableBNoncyclic
public import CFSG.LocalAnalysis.StandardType.GGTableBRank
import CFSG.LocalAnalysis.StandardType.GGCorFourTwoOrthNsLabels
import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestTailHolds
import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestTorus
import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeNbrKnownLemmas

public section

namespace CFSG.StandardType.SCFourCover

open CFSG.Assembly

section Lift

variable {K : Type} [Field K] [Finite K] [CharP K 2]

private theorem sq_add_add_one_ne_zero_orthPlus {n : ℕ} (hK : Nat.card K = 2 ^ n)
    (h3 : 3 ∣ 2 ^ n + 1) (s : K) : s ^ 2 + 1 * s + 1 ≠ 0 := by
  intro hs
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hs2 : s ^ 2 = s + 1 := by linear_combination hs - (s + 1) * h2
  have hs3 : s ^ 3 = 1 := by linear_combination (s + 1) * hs2 + s * h2
  obtain ⟨k, hk⟩ : ∃ k, 2 ^ n = 3 * k + 2 := ⟨(2 ^ n + 1) / 3 - 1, by omega⟩
  have := Fintype.ofFinite K
  have hF : s ^ (3 * k + 2) = s := by
    have h := FiniteField.pow_card s
    rwa [Fintype.card_eq_nat_card, hK, hk] at h
  rw [pow_add, pow_mul, hs3, one_pow, one_mul] at hF
  exact one_ne_zero (by linear_combination hF - hs2 : (1 : K) = 0)

private theorem ggTorusLift_orthPlus_three
    {n m : ℕ}
    (hK : Nat.card K = 2 ^ n) (h3 : 3 ∣ 2 ^ n + 1) (hm : 4 ≤ m) :
    GGTorusLift 3 (m - 1) (OrthRest.RPlus K m) := by
  obtain ⟨M, σ, hM, hσ, -, -⟩ := OrthRestTail.exists_rot hK
    (sq_add_add_one_ne_zero_orthPlus hK h3) Nat.prime_three (by norm_num) h3
  have hP := OrthRestTail.torusConcl_of_frame (OrthRestTail.plusFrame K m) Nat.prime_three
    (by norm_num) hM hσ (by omega) (P := ⊥) (SP := ∅) bot_le (Set.empty_disjoint _)
    OrthRestTail.isElemAbelian_bot' bot_le (e := 0) (by rw [Subgroup.card_bot, pow_zero])
  rw [TableBOrth.coe_qPlusForm, add_zero] at hP
  obtain ⟨U, E, hU, hU2, hEU, hE, hcard⟩ := OrthRestTail.exists_R_of_torusConcl
    (TableBOrth.scalars_subgroupOf_omegaPlus_eq_bot (by omega)) hP
  obtain ⟨hZ, hZp⟩ := OrthNs.center_data_omegaPlus (K := K) Nat.prime_three (by norm_num)
    (by omega : 3 ≤ m)
  exact OrthRest.ggTorusLift_of_R Nat.prime_three hZ hZp hU hU2 hEU hE hcard

end Lift

theorem largeEvenLabelAll_torusLift_orthPlus_threeFive
    {lab : LargeEvenLabel}
    (htag : lab.tag = .D) (h3 : 3 ∣ 2 ^ lab.n + 1) (h6 : 6 ≤ lab.rank) :
    LargeEvenLabelAll lab fun R _ _ _ => GGTorusLift 3 5 R := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag h3 h6 ⊢
  subst htag
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  split_ifs at hQ ⊢ with hl3
  · omega
  obtain ⟨K, _, _, hK, hq⟩ := hQ
  have := CFSG.StandardType.charP_two_of_card hK
  exact ⟨K, inferInstance, inferInstance, hK, hq, ggTorusLift_mono Nat.prime_three
    (ggTorusLift_orthPlus_three hK h3 (by omega)) (by omega)⟩

end CFSG.StandardType.SCFourCover

end
