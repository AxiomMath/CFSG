module

public import CFSG.RankThree.PartTwo.Sec4.Census.DoubleCoverRanksL34

public section

namespace CFSG.RankThree.PartTwo.Sec13.KS135Cover

open CFSG CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL)
open Sec4.Census.DoubleCoverRanksTwo

theorem three_le_pRank_of_projSL_cover {K : Type} [Field K] [CharP K 2] (hK : 4 ≤ Nat.card K)
    {J : Type} [Group J] [Finite J] {φ : J →* projSL 3 K} (hφ : Function.Surjective φ)
    (hker : φ.ker = Subgroup.center J) (hZ2 : IsPGroup 2 (Subgroup.center J))
    (hZ1 : Subgroup.center J ≠ ⊥) : 3 ≤ CFSG.pRank 2 J := by
  have hk : φ.ker ≤ Subgroup.center J := hker.le
  obtain ⟨A, hA, hcard⟩ := Sec4.Census.TransitiveLift.exists_isElementaryAbelian_card hφ hk
    (W := (rootHom (K := K)).range) (fun y y' hy hy' => commute_lift_rootHom hφ hk hy hy')
    (fun y hy => by
      obtain ⟨a, ha⟩ := hy
      exact exists_sq_eq_sq_E hφ hk (by omega) (ha ▸ rootHom_mem_range_uHom a))
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Nontrivial (Subgroup.center J) := (Subgroup.nontrivial_iff_ne_bot _).mpr hZ1
  obtain ⟨n, hn⟩ := hZ2.exists_card_eq
  have hn0 : n ≠ 0 := by
    rintro rfl
    have h1 : 1 < Nat.card (Subgroup.center J) := Finite.one_lt_card
    rw [hn, pow_zero] at h1
    exact lt_irrefl _ h1
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center J) 2
    (by rw [hn]; exact dvd_pow_self 2 hn0)
  have hzker : φ (z : J) = 1 := by
    rw [← MonoidHom.mem_ker, hker]
    exact z.2
  have hz2 : (z : J) ^ 2 = 1 := by
    rw [← Subgroup.coe_pow, ← hz, pow_orderOf_eq_one, Subgroup.coe_one]
  have hz1 : (z : J) ≠ 1 := by
    intro h
    have h' : z = 1 := Subtype.ext h
    rw [h', orderOf_one] at hz
    exact absurd hz (by norm_num)
  have hΩ : 2 ≤ Nat.card {c : J // φ c = 1 ∧ c ^ 2 = 1} := by
    have : Nontrivial {c : J // φ c = 1 ∧ c ^ 2 = 1} :=
      nontrivial_of_ne ⟨1, map_one φ, one_pow 2⟩ ⟨(z : J), hzker, hz2⟩
        (fun h => hz1 (congrArg Subtype.val h).symm)
    exact Finite.one_lt_card
  rw [card_range_rootHom] at hcard
  refine Sec4.Census.TransitiveLift.le_pRank_of_card hA (k := 3) ?_
  rw [hcard]
  calc 2 ^ 3 = 4 * 2 := by norm_num
    _ ≤ Nat.card K * Nat.card {c : J // φ c = 1 ∧ c ^ 2 = 1} := Nat.mul_le_mul hK hΩ

end CFSG.RankThree.PartTwo.Sec13.KS135Cover
