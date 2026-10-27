module

public import CFSG.Quasithin.Vol2.Ch10SecQ1Base
public import CFSG.Timmesfeld.Orders.ClassicalLinear

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecA

namespace C10P01

open CFSG.Assembly.LowTwoRank

theorem card_psu3 {K : Type} [Field K] {a : ℕ} (ha : 1 ≤ a) (hK : Nat.card K = (2 ^ a) ^ 2) :
    Nat.card (StatedProj (StatedSU 3 (2 ^ a) K)) =
      (2 ^ a) ^ 3 * (((2 ^ a) ^ 2 - 1) * ((2 ^ a) ^ 3 + 1) / Nat.gcd 3 (2 ^ a + 1)) := by
  rw [CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU Nat.prime_two ha hK (by norm_num)]
  set q := 2 ^ a with hq
  have hq1 : 1 ≤ q := Nat.one_le_two_pow
  have hI : Finset.Icc 2 3 = {2, 3} := by decide
  have h2 : (((q : ℕ) : ℤ) ^ 2 - (-1) ^ 2).toNat = q ^ 2 - 1 := by
    have h : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq1
    rw [show ((q : ℕ) : ℤ) ^ 2 - (-1) ^ 2 = ((q ^ 2 - 1 : ℕ) : ℤ) by push_cast [h]; ring,
      Int.toNat_natCast]
  have h3 : (((q : ℕ) : ℤ) ^ 3 - (-1) ^ 3).toNat = q ^ 3 + 1 := by
    rw [show ((q : ℕ) : ℤ) ^ 3 - (-1) ^ 3 = ((q ^ 3 + 1 : ℕ) : ℤ) by push_cast; ring,
      Int.toNat_natCast]
  have hd : Nat.gcd 3 (q + 1) ∣ (q ^ 2 - 1) * (q ^ 3 + 1) := by
    refine (Nat.gcd_dvd_right 3 (q + 1)).trans (dvd_mul_of_dvd_right ?_ _)
    simpa using Odd.nat_add_dvd_pow_add_pow q 1 (by decide : Odd 3)
  rw [hI, Finset.prod_pair (by norm_num), h2, h3, show 3 * (3 - 1) / 2 = 3 by norm_num,
    Nat.mul_div_assoc _ hd]

theorem psu3_lt {q : ℕ} (hq : 2 ≤ q) : (q ^ 2 - 1) * (q ^ 3 + 1) < q ^ 5 := by
  have h1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h2 : q ^ 2 ≤ q ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
  zify [h1]
  nlinarith

theorem not_shapeCard_psu3 {a : ℕ} (ha : 2 ≤ a) :
    ¬ ShapeCard
      ((2 ^ a) ^ 3 * (((2 ^ a) ^ 2 - 1) * ((2 ^ a) ^ 3 + 1) / Nat.gcd 3 (2 ^ a + 1))) := by
  have hq2 : (2 ^ a) ^ 2 = 2 ^ (2 * a) := by rw [← pow_mul, mul_comm]
  have hq3 : (2 ^ a) ^ 3 = 2 ^ (3 * a) := by rw [← pow_mul, mul_comm]
  have hq5 : (2 ^ a) ^ 5 = 2 ^ (5 * a) := by rw [← pow_mul, mul_comm]
  have hqge : 2 ≤ 2 ^ a :=
    (show (2 : ℕ) = 2 ^ 1 by norm_num) ▸ Nat.pow_le_pow_right (by norm_num) (by omega)
  set q := 2 ^ a with hq
  set M := (q ^ 2 - 1) * (q ^ 3 + 1) with hM
  set d := Nat.gcd 3 (q + 1) with hd
  have hq1dvd : q + 1 ∣ q ^ 3 + 1 := by
    simpa using Odd.nat_add_dvd_pow_add_pow q 1 (by decide : Odd 3)
  have hdM : d ∣ M := (Nat.gcd_dvd_right 3 (q + 1)).trans (dvd_mul_of_dvd_right hq1dvd _)
  have hoddM : Odd M := by
    refine Odd.mul ?_ ?_
    · rw [hq2]
      exact odd_two_pow_sub_one (by omega)
    · rw [hq3]
      exact (Nat.even_pow.mpr ⟨even_two, by omega⟩).add_one
  have hb : Odd (M / d) := by
    have h := hoddM
    rw [← Nat.mul_div_cancel' hdM] at h
    exact (Nat.odd_mul.mp h).2
  have h3q2 : 3 ∣ q ^ 2 - 1 := by
    rw [hq2]
    exact three_dvd_two_pow_two_mul_sub_one a
  have h3b : 3 ∣ M / d := by
    rcases Nat.prime_three.eq_one_or_self_of_dvd d (Nat.gcd_dvd_left 3 (q + 1)) with hd1 | hd3
    · rw [hd1, Nat.div_one]
      exact dvd_mul_of_dvd_left h3q2 _
    · have h3q1 : 3 ∣ q + 1 := hd3 ▸ Nat.gcd_dvd_right 3 (q + 1)
      have h9 : 3 * 3 ∣ M := mul_dvd_mul h3q2 (h3q1.trans hq1dvd)
      rw [hd3]
      exact Nat.dvd_div_of_mul_dvd h9
  have hlt : M / d < 2 ^ (5 * a) := by
    rw [← hq5]
    exact lt_of_le_of_lt (Nat.div_le_self _ _) (psu3_lt hqge)
  rw [hq3]
  exact not_shapeCard_of hb h3b (fun _ => ne_four_pow_sub_one_of_lt hlt (by omega))
    (fun h => by omega)

theorem statedScalars_su3_comm {K : Type} [Field K] (q : ℕ) :
    ∀ x ∈ (StatedScalars (Fin 3) K).subgroupOf (StatedSU 3 q K),
      ∀ y ∈ (StatedScalars (Fin 3) K).subgroupOf (StatedSU 3 q K), x * y = y * x := by
  intro x hx y _
  have hc : (x : GL (Fin 3) K) ∈ Subgroup.center (GL (Fin 3) K) := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact hx
  exact Subtype.ext (Subgroup.mem_center_iff.mp hc (y : GL (Fin 3) K)).symm

end C10P01

open C10P01 CFSG.Assembly.LowTwoRank

theorem factB4aSU3_holds :
    FactB4aSU3 := by
  intro K _ _ a hK X _ hX π hπ
  have ha : 1 ≤ a := by
    rcases Nat.eq_zero_or_pos a with rfl | h
    · have := Finite.one_lt_card (α := K)
      rw [hK] at this
      norm_num at this
    · exact h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZ := statedScalars_su3_comm (K := K) (2 ^ a)
  have : ((StatedScalars (Fin 3) K).subgroupOf (StatedSU 3 (2 ^ a) K)).Normal :=
    Subgroup.Normal.subgroupOf (StatedScalars.normal (Fin 3) K) _
  rcases Nat.lt_or_ge a 2 with ha2 | ha2
  ·
    obtain ⟨φ, hφ⟩ := exists_quotient_surjective hX _ hZ π hπ
    have hcard : Nat.card (StatedProj (StatedSU 3 (2 ^ a) K)) = 72 := by
      rw [card_psu3 ha hK, show a = 1 by omega]
      norm_num
    have hdvd : Nat.card X ∣ 72 := by
      rw [← hcard, ← Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφ).toEquiv]
      exact Subgroup.card_quotient_dvd_card _
    exact false_of_shapeCard_dvd_72 (shapeCard_of_isShapeGroup hX) hdvd
  ·
    have hsimple : IsSimpleGroup (StatedProj (StatedSU 3 (2 ^ a) K)) :=
      CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU K 2 a hK 3 le_rfl
        (fun h => by
          have h2 : 2 ^ a = 2 := congrArg Prod.snd h
          have h4 : 4 ≤ 2 ^ a :=
            (show (4 : ℕ) = 2 ^ 2 by norm_num) ▸ Nat.pow_le_pow_right (by norm_num) ha2
          omega)
    obtain ⟨e⟩ := nonempty_mulEquiv_quotient_of_isShapeGroup hX _ hZ hsimple π hπ
    apply not_shapeCard_psu3 ha2
    rw [← card_psu3 ha hK, Nat.card_congr e.toEquiv]
    exact shapeCard_of_isShapeGroup hX

end CFSG.Quasithin.Vol2.Ch10.SecA
