module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNoTransv.Defs
public import CFSG.Open.Defs
import all CFSG.Timmesfeld.Orders.Distinct

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.NoTransv

open CFSG.Open
open CFSG.Timmesfeld

private theorem pow_add_one_le {q n : ℕ} (hq : 2 ≤ q) : q ^ n + 1 ≤ q ^ (n + 1) := by
  have h1 : 1 ≤ q ^ n := Nat.one_le_pow _ _ (by omega)
  have h2 : q ^ n + 1 ≤ q ^ n * 2 := by
    calc q ^ n + 1 ≤ q ^ n + q ^ n := Nat.add_le_add_left h1 _
      _ = q ^ n * 2 := by ring
  calc q ^ n + 1 ≤ q ^ n * 2 := h2
    _ ≤ q ^ n * q := Nat.mul_le_mul_left _ hq
    _ = q ^ (n + 1) := by ring

private theorem ordA_one_lt {q : ℕ} (hq : 2 ≤ q) : ordA 1 q < q ^ 3 := by
  rw [show ordA 1 q = q * (q ^ 2 - 1) / Nat.gcd 2 (q - 1) from by
    rw [ordA, Finset.Icc_self, Finset.prod_singleton] <;> norm_num]
  calc q * (q ^ 2 - 1) / Nat.gcd 2 (q - 1) ≤ q * (q ^ 2 - 1) := Nat.div_le_self _ _
    _ < q * q ^ 2 := by
        refine Nat.mul_lt_mul_of_pos_left ?_ (by omega)
        exact Nat.sub_lt (by positivity) one_pos
    _ = q ^ 3 := by ring

private theorem ordA_two_lt {q : ℕ} (hq : 2 ≤ q) : ordA 2 q < q ^ 9 := by
  rw [show ordA 2 q = q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) / Nat.gcd 3 (q - 1) from by
    rw [ordA, Finset.prod_Icc_succ_top (by norm_num : 2 ≤ 2 + 1), Finset.Icc_self,
      Finset.prod_singleton] <;> norm_num]
  calc q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) / Nat.gcd 3 (q - 1)
      ≤ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) := Nat.div_le_self _ _
    _ ≤ q ^ 3 * (q ^ 2 * q ^ 3) :=
        Nat.mul_le_mul (le_refl _) (Nat.mul_le_mul (Nat.sub_le _ _) (Nat.sub_le _ _))
    _ = q ^ 8 := by ring
    _ < q ^ 9 := Nat.pow_lt_pow_right (by omega) (by norm_num)

private theorem ordA_three_lt {q : ℕ} (hq : 2 ≤ q) : ordA 3 q < q ^ 18 := by
  rw [show ordA 3 q = q ^ 6 * (((q ^ 2 - 1) * (q ^ 3 - 1)) * (q ^ 4 - 1)) /
      Nat.gcd 4 (q - 1) from by
    rw [ordA, Finset.prod_Icc_succ_top (by norm_num : 2 ≤ 3 + 1),
      Finset.prod_Icc_succ_top (by norm_num : 2 ≤ 2 + 1), Finset.Icc_self,
      Finset.prod_singleton] <;> norm_num]
  calc q ^ 6 * (((q ^ 2 - 1) * (q ^ 3 - 1)) * (q ^ 4 - 1)) / Nat.gcd 4 (q - 1)
      ≤ q ^ 6 * (((q ^ 2 - 1) * (q ^ 3 - 1)) * (q ^ 4 - 1)) := Nat.div_le_self _ _
    _ ≤ q ^ 6 * ((q ^ 2 * q ^ 3) * q ^ 4) :=
        Nat.mul_le_mul (le_refl _) (Nat.mul_le_mul (Nat.mul_le_mul (Nat.sub_le _ _)
          (Nat.sub_le _ _)) (Nat.sub_le _ _))
    _ = q ^ 15 := by ring
    _ < q ^ 18 := Nat.pow_lt_pow_right (by omega) (by norm_num)

private theorem ordBC_two_lt {q : ℕ} (hq : 2 ≤ q) : ordBC 2 q < q ^ 12 := by
  rw [show ordBC 2 q = q ^ 4 * ((q ^ 2 - 1) * (q ^ 4 - 1)) / Nat.gcd 2 (q - 1) from by
    rw [ordBC, Finset.prod_Icc_succ_top (by norm_num : 1 ≤ 1 + 1), Finset.Icc_self,
      Finset.prod_singleton] <;> norm_num]
  calc q ^ 4 * ((q ^ 2 - 1) * (q ^ 4 - 1)) / Nat.gcd 2 (q - 1)
      ≤ q ^ 4 * ((q ^ 2 - 1) * (q ^ 4 - 1)) := Nat.div_le_self _ _
    _ ≤ q ^ 4 * (q ^ 2 * q ^ 4) :=
        Nat.mul_le_mul (le_refl _) (Nat.mul_le_mul (Nat.sub_le _ _) (Nat.sub_le _ _))
    _ = q ^ 10 := by ring
    _ < q ^ 12 := Nat.pow_lt_pow_right (by omega) (by norm_num)

private theorem ordBC_three_lt {q : ℕ} (hq : 2 ≤ q) : ordBC 3 q < q ^ 27 := by
  rw [show ordBC 3 q = q ^ 9 * (((q ^ 2 - 1) * (q ^ 4 - 1)) * (q ^ 6 - 1)) /
      Nat.gcd 2 (q - 1) from by
    rw [ordBC, Finset.prod_Icc_succ_top (by norm_num : 1 ≤ 2 + 1),
      Finset.prod_Icc_succ_top (by norm_num : 1 ≤ 1 + 1), Finset.Icc_self,
      Finset.prod_singleton] <;> norm_num]
  calc q ^ 9 * (((q ^ 2 - 1) * (q ^ 4 - 1)) * (q ^ 6 - 1)) / Nat.gcd 2 (q - 1)
      ≤ q ^ 9 * (((q ^ 2 - 1) * (q ^ 4 - 1)) * (q ^ 6 - 1)) := Nat.div_le_self _ _
    _ ≤ q ^ 9 * ((q ^ 2 * q ^ 4) * q ^ 6) :=
        Nat.mul_le_mul (le_refl _) (Nat.mul_le_mul (Nat.mul_le_mul (Nat.sub_le _ _)
          (Nat.sub_le _ _)) (Nat.sub_le _ _))
    _ = q ^ 21 := by ring
    _ < q ^ 27 := Nat.pow_lt_pow_right (by omega) (by norm_num)

private theorem ordTwistedA_three_lt {q : ℕ} (hq : 2 ≤ q) : ordTwistedA 3 q < q ^ 18 := by
  rw [show ordTwistedA 3 q = q ^ 6 * (((q ^ 2 - 1) * (q ^ 3 + 1)) * (q ^ 4 - 1)) /
      Nat.gcd 4 (q + 1) from by
    rw [ordTwistedA, Finset.prod_Icc_succ_top (by norm_num : 2 ≤ 3 + 1),
      Finset.prod_Icc_succ_top (by norm_num : 2 ≤ 2 + 1), Finset.Icc_self,
      Finset.prod_singleton,
      Orders.toNat_pow_sub_neg_one_pow_of_even (i := 2) (by omega) (by decide),
      Orders.toNat_pow_sub_neg_one_pow_of_odd (i := 3) (by decide),
      Orders.toNat_pow_sub_neg_one_pow_of_even (i := 4) (by omega) (by decide)] <;> norm_num]
  calc q ^ 6 * (((q ^ 2 - 1) * (q ^ 3 + 1)) * (q ^ 4 - 1)) / Nat.gcd 4 (q + 1)
      ≤ q ^ 6 * (((q ^ 2 - 1) * (q ^ 3 + 1)) * (q ^ 4 - 1)) := Nat.div_le_self _ _
    _ ≤ q ^ 6 * ((q ^ 2 * q ^ 4) * q ^ 4) :=
        Nat.mul_le_mul (le_refl _) (Nat.mul_le_mul (Nat.mul_le_mul (Nat.sub_le _ _)
          (pow_add_one_le hq)) (Nat.sub_le _ _))
    _ = q ^ 16 := by ring
    _ < q ^ 18 := Nat.pow_lt_pow_right (by omega) (by norm_num)

private theorem ordTwistedD_four_lt {q : ℕ} (hq : 2 ≤ q) : ordTwistedD 4 q < q ^ 36 := by
  rw [show ordTwistedD 4 q = q ^ 12 * (q ^ 4 + 1) * (((q ^ 2 - 1) * (q ^ 4 - 1)) *
      (q ^ 6 - 1)) / Nat.gcd 4 (q ^ 4 + 1) from by
    rw [ordTwistedD, Finset.prod_Icc_succ_top (by norm_num : 1 ≤ 2 + 1),
      Finset.prod_Icc_succ_top (by norm_num : 1 ≤ 1 + 1), Finset.Icc_self,
      Finset.prod_singleton] <;> norm_num]
  calc q ^ 12 * (q ^ 4 + 1) * (((q ^ 2 - 1) * (q ^ 4 - 1)) * (q ^ 6 - 1)) /
        Nat.gcd 4 (q ^ 4 + 1)
      ≤ q ^ 12 * (q ^ 4 + 1) * (((q ^ 2 - 1) * (q ^ 4 - 1)) * (q ^ 6 - 1)) :=
        Nat.div_le_self _ _
    _ ≤ q ^ 12 * q ^ 5 * ((q ^ 2 * q ^ 4) * q ^ 6) :=
        Nat.mul_le_mul (Nat.mul_le_mul (le_refl _) (pow_add_one_le hq))
          (Nat.mul_le_mul (Nat.mul_le_mul (Nat.sub_le _ _) (Nat.sub_le _ _))
            (Nat.sub_le _ _))
    _ = q ^ 29 := by ring
    _ < q ^ 36 := Nat.pow_lt_pow_right (by omega) (by norm_num)

theorem ordData_ordA_one {k : ℕ} (hk : 4 ≤ k) : OrdData (ordA 1 (2 ^ k)) := by
  have hP := Orders.profile_ordA (n := 1) (f := k) le_rfl (by omega)
  have hN : k * (1 * (1 + 1) / 2) = k := by
    rw [show 1 * (1 + 1) / 2 = 1 by norm_num, mul_one]
  obtain ⟨p, hp⟩ := CFSG.Timmesfeld.exists_isPrimitivePrimeDivisor (k := 2 * k)
    (by omega) (by omega)
  have hz : Orders.zA 1 k (2 * k) := ⟨2, by simp, ⟨1, by ring⟩⟩
  refine ⟨k * (1 * (1 + 1) / 2), 2 * k, p, hP.two, by omega, hp,
    (hP.prim p (2 * k) hp (by omega)).mpr hz, by rw [hN]; omega, by rw [hN]; omega, ?_⟩
  rw [hN, show 3 * k = k * 3 by ring, pow_mul]
  exact ordA_one_lt (Nat.succ_le_of_lt (Nat.one_lt_two_pow (n := k) (by omega)))

theorem ordA_one_two_pow_three : ordA 1 (2 ^ 3) = 504 := by
  rw [show ordA 1 (2 ^ 3) = (2 ^ 3) * ((2 ^ 3) ^ 2 - 1) / Nat.gcd 2 (2 ^ 3 - 1) from by
    rw [ordA, Finset.Icc_self, Finset.prod_singleton] <;> norm_num]
  norm_num

theorem ordData_ordA_two {k : ℕ} (hk : 3 ≤ k) : OrdData (ordA 2 (2 ^ k)) := by
  have hP := Orders.profile_ordA (n := 2) (f := k) (by omega) (by omega)
  have hN : k * (2 * (2 + 1) / 2) = 3 * k := by
    rw [show 2 * (2 + 1) / 2 = 3 by norm_num]
    ring
  obtain ⟨p, hp⟩ := CFSG.Timmesfeld.exists_isPrimitivePrimeDivisor (k := 3 * k)
    (by omega) (by omega)
  have hz : Orders.zA 2 k (3 * k) := ⟨3, by simp, ⟨1, by ring⟩⟩
  refine ⟨k * (2 * (2 + 1) / 2), 3 * k, p, hP.two, by omega, hp,
    (hP.prim p (3 * k) hp (by omega)).mpr hz, by rw [hN]; omega, by rw [hN]; omega, ?_⟩
  rw [hN, show 3 * (3 * k) = k * 9 by ring, pow_mul]
  exact ordA_two_lt (Nat.succ_le_of_lt (Nat.one_lt_two_pow (n := k) (by omega)))

theorem ordData_ordA_three {k : ℕ} (hk : 3 ≤ k) : OrdData (ordA 3 (2 ^ k)) := by
  have hP := Orders.profile_ordA (n := 3) (f := k) (by omega) (by omega)
  have hN : k * (3 * (3 + 1) / 2) = 6 * k := by
    rw [show 3 * (3 + 1) / 2 = 6 by norm_num]
    ring
  obtain ⟨p, hp⟩ := CFSG.Timmesfeld.exists_isPrimitivePrimeDivisor (k := 4 * k)
    (by omega) (by omega)
  have hz : Orders.zA 3 k (4 * k) := ⟨4, by simp, ⟨1, by ring⟩⟩
  refine ⟨k * (3 * (3 + 1) / 2), 4 * k, p, hP.two, by omega, hp,
    (hP.prim p (4 * k) hp (by omega)).mpr hz, by rw [hN]; omega,
    by rw [hN]; omega, ?_⟩
  rw [hN, show 3 * (6 * k) = k * 18 by ring, pow_mul]
  exact ordA_three_lt (Nat.succ_le_of_lt (Nat.one_lt_two_pow (n := k) (by omega)))

theorem ordData_ordBC_two {k : ℕ} (hk : 2 ≤ k) : OrdData (ordBC 2 (2 ^ k)) := by
  have hP := Orders.profile_ordBC (n := 2) (f := k) (by omega)
  have hN : k * (2 * 2) = 4 * k := by
    rw [show 2 * 2 = 4 by norm_num]
    ring
  obtain ⟨p, hp⟩ := CFSG.Timmesfeld.exists_isPrimitivePrimeDivisor (k := 4 * k)
    (by omega) (by omega)
  have hz : Orders.zBC 2 k (4 * k) := ⟨2, by simp, ⟨1, by ring⟩⟩
  refine ⟨k * (2 * 2), 4 * k, p, hP.two, by omega, hp,
    (hP.prim p (4 * k) hp (by omega)).mpr hz, by rw [hN]; omega, by rw [hN]; omega, ?_⟩
  rw [hN, show 3 * (4 * k) = k * 12 by ring, pow_mul]
  exact ordBC_two_lt (Nat.succ_le_of_lt (Nat.one_lt_two_pow (n := k) (by omega)))

theorem ordData_ordBC_three {k : ℕ} (hk : 2 ≤ k) : OrdData (ordBC 3 (2 ^ k)) := by
  have hP := Orders.profile_ordBC (n := 3) (f := k) (by omega)
  have hN : k * (3 * 3) = 9 * k := by
    rw [show 3 * 3 = 9 by norm_num]
    ring
  obtain ⟨p, hp⟩ := CFSG.Timmesfeld.exists_isPrimitivePrimeDivisor (k := 6 * k)
    (by omega) (by omega)
  have hz : Orders.zBC 3 k (6 * k) := ⟨3, by simp, ⟨1, by ring⟩⟩
  refine ⟨k * (3 * 3), 6 * k, p, hP.two, by omega, hp,
    (hP.prim p (6 * k) hp (by omega)).mpr hz, by rw [hN]; omega,
    by rw [hN]; omega, ?_⟩
  rw [hN, show 3 * (9 * k) = k * 27 by ring, pow_mul]
  exact ordBC_three_lt (Nat.succ_le_of_lt (Nat.one_lt_two_pow (n := k) (by omega)))

theorem ordData_ordTwistedA_three {k : ℕ} (hk : 2 ≤ k) :
    OrdData (ordTwistedA 3 (2 ^ k)) := by
  have hP := Orders.profile_ordTwistedA (n := 3) (g := k) (by omega) (by omega)
  have hN : k * (3 * (3 + 1) / 2) = 6 * k := by
    rw [show 3 * (3 + 1) / 2 = 6 by norm_num]
    ring
  obtain ⟨p, hp⟩ := CFSG.Timmesfeld.exists_isPrimitivePrimeDivisor (k := 6 * k)
    (by omega) (by omega)
  have hz : Orders.zU 3 k (6 * k) :=
    ⟨3, by simp, Or.inr ⟨by decide, ⟨1, by ring⟩, fun h => by
      have := Nat.le_of_dvd (by omega : 0 < k * 3) h
      omega⟩⟩
  refine ⟨k * (3 * (3 + 1) / 2), 6 * k, p, hP.two, by omega, hp,
    (hP.prim p (6 * k) hp (by omega)).mpr hz, by rw [hN]; omega,
    by rw [hN]; omega, ?_⟩
  rw [hN, show 3 * (6 * k) = k * 18 by ring, pow_mul]
  exact ordTwistedA_three_lt (Nat.succ_le_of_lt (Nat.one_lt_two_pow (n := k) (by omega)))

theorem ordData_ordTwistedD_four {k : ℕ} (hk : 2 ≤ k) :
    OrdData (ordTwistedD 4 (2 ^ k)) := by
  have hP := Orders.profile_ordTwistedD (n := 4) (f := k) (by omega) (by omega)
  have hN : k * (4 * (4 - 1)) = 12 * k := by
    rw [show 4 * (4 - 1) = 12 by norm_num]
    ring
  obtain ⟨p, hp⟩ := CFSG.Timmesfeld.exists_isPrimitivePrimeDivisor (k := 8 * k)
    (by omega) (by omega)
  have hz : Orders.z2D 4 k (8 * k) :=
    Or.inl ⟨⟨1, by ring⟩, fun h => by
      have := Nat.le_of_dvd (by omega : 0 < k * 4) h
      omega⟩
  refine ⟨k * (4 * (4 - 1)), 8 * k, p, hP.two, by omega, hp,
    (hP.prim p (8 * k) hp (by omega)).mpr hz, by rw [hN]; omega,
    by rw [hN]; omega, ?_⟩
  rw [hN, show 3 * (12 * k) = k * 36 by ring, pow_mul]
  exact ordTwistedD_four_lt (Nat.succ_le_of_lt (Nat.one_lt_two_pow (n := k) (by omega)))

private theorem not_ordData_of_prime {m : ℕ} (hm : OrdData m) (hprime : m.Prime) : False := by
  obtain ⟨N, e, p, ⟨r, hr, hmr⟩, he, hp, hpdvd, -, -, hlt⟩ := hm
  have he0 : 0 < e := by omega
  have hmeq : p = m := (Nat.prime_dvd_prime_iff_eq hp.prime hprime).mp hpdvd
  have hm2 : m ≠ 2 := by
    rw [← hmeq]
    exact hp.ne_two he0
  have hodd : Odd m := hprime.odd_of_ne_two hm2
  have h2dvd : 2 ^ N ∣ m := ⟨r, hmr⟩
  have hN0 : N = 0 := by
    rcases Nat.eq_zero_or_pos N with h | h
    · exact h
    · exfalso
      have h2 : 2 ∣ 2 ^ N := by
        rw [show N = (N - 1) + 1 by omega, pow_succ]
        exact dvd_mul_left 2 _
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr (h2.trans h2dvd))
  rw [hN0] at hlt
  have h2le : 2 ≤ m := hprime.two_le
  omega

theorem exists_mul_ne_of_ordData {S : Type*} [Group S] [Finite S] [IsSimpleGroup S]
    (hS : OrdData (Nat.card S) ∨ Nat.card S = 504) : ∃ a b : S, a * b ≠ b * a := by
  by_contra h
  simp only [not_exists, not_not] at h
  haveI : IsMulCommutative S := { is_comm := ⟨h⟩ }
  have hprime : (Nat.card S).Prime := Group.is_simple_iff_prime_card.mp inferInstance
  rcases hS with hS | hS
  · exact not_ordData_of_prime hS hprime
  · rw [hS] at hprime
    rcases hprime.eq_one_or_self_of_dvd 8 (by norm_num) with h | h <;> omega

end CFSG.LocalAnalysis.UniquenessCase.UC22.NoTransv
