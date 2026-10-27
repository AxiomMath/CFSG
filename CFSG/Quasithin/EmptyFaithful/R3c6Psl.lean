module

public import CFSG.Quasithin.EmptyFaithful.R3c6Ord
public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.Timmesfeld.Orders.ClassicalLinear
public import CFSG.LieType.Simplicity.Classical

public section

namespace CFSG.Quasithin.R3c6

open CFSG.Open CFSG.Quasithin CFSG.Assembly.LowTwoRank

theorem psl3Data {X : Type} [Group X] {r e : ℕ} (h : IsPSL 3 r e X) :
    Finite X ∧ IsSimpleGroup X ∧ r.Prime ∧ 1 ≤ e ∧
      Nat.card X * Nat.gcd 3 (r ^ e - 1) =
        (r ^ e) ^ 3 * (((r ^ e) ^ 2 - 1) * ((r ^ e) ^ 3 - 1)) := by
  have hfin : Finite X := CFSG.LieType.Simplicity.finite_of_statedClassicalModel h
  have hsimp : IsSimpleGroup X := (CFSG.LieType.Simplicity.fam_PSL_simplicity X 3 r e h).2
  obtain ⟨⟨hr, he, -⟩, K, _, _, hK, ⟨φ⟩⟩ := h
  refine ⟨hfin, hsimp, hr, he, ?_⟩
  have hc := CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (K := K) (n := 3)
    (by norm_num)
  rw [hK] at hc
  rw [Nat.card_congr φ.toEquiv, hc]
  have hI : Finset.Icc 2 3 = ({2, 3} : Finset ℕ) := by decide
  rw [hI, Finset.prod_pair (by norm_num)]
  have hd1 : Nat.gcd 3 (r ^ e - 1) ∣ r ^ e - 1 := Nat.gcd_dvd_right _ _
  have hd2 : r ^ e - 1 ∣ (r ^ e) ^ 3 - 1 := by
    have := Nat.sub_dvd_pow_sub_pow (r ^ e) 1 3
    rwa [one_pow] at this
  have hdvd : Nat.gcd 3 (r ^ e - 1) ∣
      (r ^ e) ^ (3 * (3 - 1) / 2) * (((r ^ e) ^ 2 - 1) * ((r ^ e) ^ 3 - 1)) :=
    Dvd.dvd.mul_left (Dvd.dvd.mul_left (hd1.trans hd2) _) _
  rw [Nat.div_mul_cancel hdvd]

theorem psu3Data {X : Type} [Group X] {r e : ℕ} (h : IsPSU 3 r e X) :
    Finite X ∧ IsSimpleGroup X ∧ r.Prime ∧ 1 ≤ e ∧
      Nat.card X * Nat.gcd 3 (r ^ e + 1) =
        (r ^ e) ^ 3 * (((r ^ e) ^ 2 - 1) * ((r ^ e) ^ 3 + 1)) := by
  have hfin : Finite X := CFSG.LieType.Simplicity.finite_of_statedClassicalModel h
  have hsimp : IsSimpleGroup X := (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity X 3 r e h).2
  obtain ⟨⟨hr, he, -⟩, K, _, _, hK, ⟨φ⟩⟩ := h
  refine ⟨hfin, hsimp, hr, he, ?_⟩
  have hc := CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU (K := K) (n := 3) hr he hK
    (by norm_num)
  rw [Nat.card_congr φ.toEquiv, hc]
  have hI : Finset.Icc 2 3 = ({2, 3} : Finset ℕ) := by decide
  rw [hI, Finset.prod_pair (by norm_num)]
  have hQ : 1 ≤ r ^ e := Nat.one_le_pow _ _ hr.pos
  have e2 : (((r ^ e : ℕ) : ℤ) ^ 2 - (-1) ^ 2).toNat = (r ^ e) ^ 2 - 1 := by
    have h1 : 1 ≤ (r ^ e) ^ 2 := Nat.one_le_pow _ _ hQ
    have h2 : (((r ^ e : ℕ) : ℤ) ^ 2 - (-1) ^ 2) = (((r ^ e) ^ 2 - 1 : ℕ) : ℤ) := by
      push_cast [Nat.cast_sub h1]
      ring
    rw [h2, Int.toNat_natCast]
  have e3 : (((r ^ e : ℕ) : ℤ) ^ 3 - (-1) ^ 3).toNat = (r ^ e) ^ 3 + 1 := by
    have h2 : (((r ^ e : ℕ) : ℤ) ^ 3 - (-1) ^ 3) = (((r ^ e) ^ 3 + 1 : ℕ) : ℤ) := by
      push_cast
      ring
    rw [h2, Int.toNat_natCast]
  rw [e2, e3]
  have hd1 : Nat.gcd 3 (r ^ e + 1) ∣ r ^ e + 1 := Nat.gcd_dvd_right _ _
  have hd2 : r ^ e + 1 ∣ (r ^ e) ^ 3 + 1 := by
    have := Odd.nat_add_dvd_pow_add_pow (r ^ e) 1 (by decide : Odd 3)
    rwa [one_pow] at this
  have hdvd : Nat.gcd 3 (r ^ e + 1) ∣
      (r ^ e) ^ (3 * (3 - 1) / 2) * (((r ^ e) ^ 2 - 1) * ((r ^ e) ^ 3 + 1)) :=
    Dvd.dvd.mul_left (Dvd.dvd.mul_left (hd1.trans hd2) _) _
  rw [Nat.div_mul_cancel hdvd]

theorem psl2Data {X : Type} [Group X] {r e : ℕ} (h : IsPSL 2 r e X) :
    Finite X ∧ r.Prime ∧ 1 ≤ e ∧
      Nat.card X * Nat.gcd 2 (r ^ e - 1) = r ^ e * ((r ^ e) ^ 2 - 1) := by
  have hfin : Finite X := CFSG.LieType.Simplicity.finite_of_statedClassicalModel h
  obtain ⟨⟨hr, he, -⟩, K, _, _, hK, ⟨φ⟩⟩ := h
  refine ⟨hfin, hr, he, ?_⟩
  have hc := CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (K := K) (n := 2)
    (by norm_num)
  rw [hK] at hc
  rw [Nat.card_congr φ.toEquiv, hc]
  have hI : Finset.Icc 2 2 = ({2} : Finset ℕ) := by decide
  rw [hI, Finset.prod_singleton]
  have hd1 : Nat.gcd 2 (r ^ e - 1) ∣ r ^ e - 1 := Nat.gcd_dvd_right _ _
  have hd2 : r ^ e - 1 ∣ (r ^ e) ^ 2 - 1 := by
    have := Nat.sub_dvd_pow_sub_pow (r ^ e) 1 2
    rwa [one_pow] at this
  have hdvd : Nat.gcd 2 (r ^ e - 1) ∣ (r ^ e) ^ (2 * (2 - 1) / 2) * ((r ^ e) ^ 2 - 1) :=
    Dvd.dvd.mul_left (hd1.trans hd2) _
  rw [Nat.div_mul_cancel hdvd]
  simp

theorem isOddOrder_of_isPSLEps3 {s : Bool} {p e : ℕ} (hp2 : p ≠ 2)
    (hmod : Int.ModEq 3 ((p ^ e : ℕ) : ℤ) (if s then 1 else -1)) {X : Type} [Group X]
    (h : IsPSLEps3 s p e X) : IsOddOrder (Nat.card X) := by
  cases s
  · obtain ⟨-, -, hp, he, hN⟩ := psu3Data h
    refine ⟨false, p, e, hp, hp2, he, hmod, ?_⟩
    have h3 : Nat.gcd 3 (p ^ e + 1) = 3 := by
      apply Nat.gcd_eq_left
      simp only [Bool.false_eq_true, ite_false] at hmod
      unfold Int.ModEq at hmod
      generalize p ^ e = Q at *
      omega
    rw [h3] at hN
    rw [hN]
    unfold ord3Num
    simp only [Bool.false_eq_true, ite_false]
  · obtain ⟨-, -, hp, he, hN⟩ := psl3Data h
    refine ⟨true, p, e, hp, hp2, he, hmod, ?_⟩
    have h3 : Nat.gcd 3 (p ^ e - 1) = 3 := by
      apply Nat.gcd_eq_left
      simp only [ite_true] at hmod
      have hQ : 1 ≤ p ^ e := Nat.one_le_pow _ _ hp.pos
      unfold Int.ModEq at hmod
      generalize p ^ e = Q at *
      omega
    rw [h3] at hN
    rw [hN]
    unfold ord3Num
    simp only [ite_true]

end CFSG.Quasithin.R3c6
