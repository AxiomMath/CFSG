module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312U3Cen
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312U3Ord
public import CFSG.RankThree.SubgroupLists.FieldThreeFamilies

public section

namespace CFSG.Quasithin.A312U3

open Matrix CFSG.Assembly.LowTwoRank CFSG.RankThree.SubgroupLists CFSG.RepresentationTheory
open scoped MatrixGroups

theorem eq_three_of_pow_lt_four' {r f : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hf : 1 ≤ f)
    (h : r ^ f < 4) : r = 3 ∧ f = 1 := by
  have hr3 : 3 ≤ r := by have := hr.two_le; omega
  have hrf : r ≤ r ^ f := Nat.le_self_pow (by omega) r
  have hr' : r = 3 := by omega
  subst hr'
  refine ⟨rfl, ?_⟩
  by_contra hf1
  have : 3 ^ 2 ≤ 3 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem eq_of_card_perfect_cases {n p : ℕ} (hn : 4 ≤ n) (hp : 1 ≤ p)
    (h : n * (n ^ 2 - 1) = 120 ∨ n * (n ^ 2 - 1) = 40 ∨ n * (n ^ 2 - 1) = p * (p ^ 2 - 1) ∨
      n * (n ^ 2 - 1) = p ^ 2 * (p ^ 4 - 1)) : n = 5 ∨ n = p ∨ n = p ^ 2 := by
  have hn1 : 1 ≤ n := by omega
  rcases h with h | h | h | h
  · left
    exact eq_of_mul_sq_sub_one_eq hn1 (by norm_num) (by rw [h]; norm_num)
  · exfalso
    have : 4 * (4 ^ 2 - 1) ≤ n * (n ^ 2 - 1) := Nat.mul_le_mul hn
      (Nat.sub_le_sub_right (Nat.pow_le_pow_left hn 2) 1)
    omega
  · right; left
    exact eq_of_mul_sq_sub_one_eq hn1 hp h
  · right; right
    refine eq_of_mul_sq_sub_one_eq hn1 (Nat.one_le_pow _ _ (by omega)) ?_
    rw [h, show (p ^ 2) ^ 2 = p ^ 4 by ring]

theorem su3NoPSL3_holds : SU3NoPSL3 := by
  intro p hpf hp7 K _ _ hK M H hctx r f hr hr2 hf K' _ _ hK' e
  have hp : p.Prime := hpf.out
  have hp2 : p ≠ 2 := by omega
  have hdet := hctx.det
  have hZ := hctx.center
  have hZ3 : ∀ z ∈ Subgroup.center H, z ^ 3 = 1 := fun z hz =>
    pow_three_eq_one_of_mem_center hZ hz
  have hK3 : (3 : K) ≠ 0 := by
    exact_mod_cast natCast_ne_zero_of_card_sq hK Nat.prime_three (by omega)
  have hK5 : (5 : K) ≠ 0 := by
    exact_mod_cast natCast_ne_zero_of_card_sq hK Nat.prime_five (by omega)
  have hrf : Fact r.Prime := ⟨hr⟩
  have hcharK' : CharP K' r := CFSG.ABGLocalTools.SL2Facts.charP_of_card_eq_prime_pow hr hK'
  set e' := e.trans (projectiveSpecialLinearGroupEquivStatedProj 3 K').symm with he'
  by_cases hq4 : 4 ≤ r ^ f
  · have hF2 : (2 : K') ≠ 0 := by
      intro h
      have : ((2 : ℕ) : K') = 0 := by exact_mod_cast h
      rw [CharP.cast_eq_zero_iff K' r] at this
      exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp this)
    have hF4 : 4 ≤ Nat.card K' := by rw [hK']; exact hq4
    set t := e'.symm (negDiagPSL3 K') with ht
    set L := (leviPSL3 K').map e'.symm.toMonoidHom with hLdef
    have : Group.IsPerfect (leviPSL3 K') := isPerfect_leviPSL3 hF4
    have hLp : Group.IsPerfect L := Group.IsPerfect.map _
    have hLcard : Nat.card L = Nat.card K' * (Nat.card K' ^ 2 - 1) := by
      rw [← card_leviPSL3]
      exact (Nat.card_congr ((leviPSL3 K').equivMapOfInjective _
        e'.symm.injective).toEquiv).symm
    have hL : L ≠ ⊥ := by
      intro h
      have h1 : Nat.card L = 1 := by rw [h]; exact Subgroup.card_bot
      rw [hLcard] at h1
      have : 4 * (4 ^ 2 - 1) ≤ Nat.card K' * (Nat.card K' ^ 2 - 1) := Nat.mul_le_mul hF4
        (Nat.sub_le_sub_right (Nat.pow_le_pow_left hF4 2) 1)
      omega
    have ht2 : t ^ 2 = 1 := by rw [ht, ← map_pow, negDiagPSL3_sq, map_one]
    have ht1 : t ≠ 1 := fun h =>
      negDiagPSL3_ne_one hF2 (e'.symm.injective (by rw [← ht, h, map_one]))
    have hLt : ∀ x ∈ L, x * t = t * x := by
      rintro _ ⟨y, hy, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, ht, ← map_mul, leviPSL3_commute y hy]
    have hcard := card_perfect_of_le_centralizer_K hp2 hK hdet hZ ht2 ht1 L hL hLt
    rw [hLcard] at hcard
    have hq : Nat.card K' = 5 ∨ Nat.card K' = p ∨ Nat.card K' = p ^ 2 :=
      eq_of_card_perfect_cases hF4 hp.one_lt.le hcard
    have hS : Nat.card (H ⧸ Subgroup.center H) =
        Nat.card (ProjectiveSpecialLinearGroup (Fin 3) K') := Nat.card_congr e'.toEquiv
    have hpsl := card_psl3_mul_gcd (K := K')
    have hHdvd := card_dvd_of_qctx hK hctx
    rw [card_eq_quotient_mul H] at hHdvd
    rcases hq with h5 | hqp | hqp2
    · obtain ⟨s, g, hs5, hs1, hg⟩ := exists_rational_five_psl3 (F := K') h5
      exact hK5 (five_eq_zero_of_rational_five hdet hZ3 (s := e'.symm s) (g := e'.symm g)
        (by rw [← map_pow, hs5, map_one]) (fun h => hs1 (e'.symm.injective (by rw [h, map_one])))
        (by rw [← map_inv, ← map_mul, ← map_mul, hg, map_pow]))
    · rw [hqp] at hpsl
      exact false_of_psl3_card_p (by omega) (Nat.gcd_dvd_left 3 _) (by rw [hS]; exact hpsl) hHdvd
    · rw [hqp2] at hpsl
      exact false_of_card_p_six (by omega) (Nat.gcd_dvd_left 3 _) hZ (by rw [hS]; exact hpsl)
        hHdvd
  · obtain ⟨rfl, rfl⟩ := eq_three_of_pow_lt_four' hr hr2 hf (by omega)
    exact false_of_psl33 hK3 hdet hZ3 (by exact_mod_cast CharP.cast_eq_zero K' 3) e'

end CFSG.Quasithin.A312U3
