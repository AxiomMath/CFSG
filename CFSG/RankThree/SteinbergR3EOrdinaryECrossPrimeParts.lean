module

public import CFSG.Timmesfeld.Orders.ExceptionalUntwisted

public section

namespace CFSG.RankThree.OrdinaryECrossPrime

open CFSG.Blueprint.Chevalley CFSG.Timmesfeld.ExceptionalOrders CFSG.Open

theorem ordProj_list_prod (p : ℕ) :
    ∀ L : List ℕ, (∀ x ∈ L, x ≠ 0) → ordProj[p] L.prod = (L.map fun x => ordProj[p] x).prod
  | [], _ => by simp
  | x :: L, h => by
    rw [List.prod_cons, Nat.ordProj_mul p (h x List.mem_cons_self)
      (List.prod_ne_zero fun h0 => h 0 (List.mem_cons_of_mem x h0) rfl),
      ordProj_list_prod p L fun y hy => h y (List.mem_cons_of_mem x hy), List.map_cons,
      List.prod_cons]

theorem ordProj_div_of_not_dvd {p N e : ℕ} (hN : N ≠ 0) (he : e ∣ N) (hpe : ¬ p ∣ e) :
    ordProj[p] (N / e) = ordProj[p] N := by
  obtain ⟨m, rfl⟩ := he
  have he0 : e ≠ 0 := by
    rintro rfl
    simp at hN
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp at hN
  rw [Nat.mul_div_cancel_left m (Nat.pos_of_ne_zero he0), Nat.ordProj_mul p he0 hm0,
    Nat.factorization_eq_zero_of_not_dvd hpe, pow_zero, one_mul]

theorem prod_pow_sub_one_ne_zero {q : ℕ} (hq : 2 ≤ q) (D : List ℕ) (hD : ∀ d ∈ D, 0 < d) :
    ∀ x ∈ D.map fun d => q ^ d - 1, x ≠ 0 := by
  intro x hx
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hx
  have : 1 < q ^ d := Nat.one_lt_pow (hD d hd).ne' (by omega)
  omega

theorem ordProj_pow_mul_prod {p q : ℕ} (hp : p.Prime) (hpq : ¬ p ∣ q) (hq : 2 ≤ q) (N : ℕ)
    (D : List ℕ) (hD : ∀ d ∈ D, 0 < d) :
    ordProj[p] (q ^ N * (D.map fun d => q ^ d - 1).prod) =
      (D.map fun d => ordProj[p] (q ^ d - 1)).prod := by
  have hne := prod_pow_sub_one_ne_zero hq D hD
  rw [Nat.ordProj_mul p (pow_ne_zero N (by omega)) (List.prod_ne_zero fun h0 => hne 0 h0 rfl),
    ordProj_list_prod p _ hne, List.map_map,
    Nat.factorization_eq_zero_of_not_dvd fun h => hpq (hp.dvd_of_dvd_pow h), pow_zero, one_mul]
  rfl

theorem ordinary_E_exact_cross_prime_order_parts {K : Type} [Field K] [Finite K] {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) (hpq : ¬ p ∣ Nat.card K) :
    ordProj[p] (Nat.card (adjointGroup .E6 K)) =
        (([2, 5, 6, 8, 9, 12] : List ℕ).map fun d => ordProj[p] (Nat.card K ^ d - 1)).prod ∧
      ordProj[p] (Nat.card (adjointGroup .E7 K)) =
        (([2, 6, 8, 10, 12, 14, 18] : List ℕ).map fun d =>
          ordProj[p] (Nat.card K ^ d - 1)).prod ∧
      ordProj[p] (Nat.card (adjointGroup .E8 K)) =
        (([2, 8, 12, 14, 18, 20, 24, 30] : List ℕ).map fun d =>
          ordProj[p] (Nat.card K ^ d - 1)).prod := by
  have hq : 2 ≤ Nat.card K := Finite.one_lt_card
  set q := Nat.card K
  have hq0 : q ^ 36 ≠ 0 ∧ q ^ 63 ≠ 0 := ⟨pow_ne_zero _ (by omega), pow_ne_zero _ (by omega)⟩
  have hq2 : q - 1 ∣ q ^ 2 - 1 := by simpa only [one_pow] using Nat.sub_dvd_pow_sub_pow q 1 2
  have hgcd : ∀ e : ℕ, 0 < e → e ≤ 3 → ¬ p ∣ Nat.gcd e (q - 1) := fun e he0 he h => by
    have := Nat.le_of_dvd he0 (h.trans (Nat.gcd_dvd_left e (q - 1)))
    omega
  refine ⟨?_, ?_, ?_⟩
  ·
    have hD : ∀ d ∈ ([2, 5, 6, 8, 9, 12] : List ℕ), 0 < d := by decide
    have hE6 : Nat.card (adjointGroup .E6 K) =
        q ^ 36 * (([2, 5, 6, 8, 9, 12] : List ℕ).map fun d => q ^ d - 1).prod /
          Nat.gcd 3 (q - 1) := by
      rw [card_adjointGroup_E6, ordE6]
      congr 1
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
      ring
    have hdvd : Nat.gcd 3 (q - 1) ∣
        q ^ 36 * (([2, 5, 6, 8, 9, 12] : List ℕ).map fun d => q ^ d - 1).prod :=
      (Nat.gcd_dvd_right 3 (q - 1)).trans (dvd_mul_of_dvd_right (hq2.trans
        (List.dvd_prod (List.mem_map.mpr ⟨2, by simp, rfl⟩))) _)
    have hN := mul_ne_zero hq0.1
      (List.prod_ne_zero fun h0 => prod_pow_sub_one_ne_zero hq _ hD 0 h0 rfl)
    rw [hE6, ordProj_div_of_not_dvd hN hdvd (hgcd 3 (by norm_num) le_rfl),
      ordProj_pow_mul_prod hp hpq hq 36 _ hD]
  ·
    have hD : ∀ d ∈ ([2, 6, 8, 10, 12, 14, 18] : List ℕ), 0 < d := by decide
    have hE7 : Nat.card (adjointGroup .E7 K) =
        q ^ 63 * (([2, 6, 8, 10, 12, 14, 18] : List ℕ).map fun d => q ^ d - 1).prod /
          Nat.gcd 2 (q - 1) := by
      rw [card_adjointGroup_E7, ordE7]
      congr 1
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
      ring
    have hdvd : Nat.gcd 2 (q - 1) ∣
        q ^ 63 * (([2, 6, 8, 10, 12, 14, 18] : List ℕ).map fun d => q ^ d - 1).prod :=
      (Nat.gcd_dvd_right 2 (q - 1)).trans (dvd_mul_of_dvd_right (hq2.trans
        (List.dvd_prod (List.mem_map.mpr ⟨2, by simp, rfl⟩))) _)
    have hN := mul_ne_zero hq0.2
      (List.prod_ne_zero fun h0 => prod_pow_sub_one_ne_zero hq _ hD 0 h0 rfl)
    rw [hE7, ordProj_div_of_not_dvd hN hdvd (hgcd 2 (by norm_num) (by norm_num)),
      ordProj_pow_mul_prod hp hpq hq 63 _ hD]
  ·
    have hD : ∀ d ∈ ([2, 8, 12, 14, 18, 20, 24, 30] : List ℕ), 0 < d := by decide
    have hE8 : Nat.card (adjointGroup .E8 K) =
        q ^ 120 * (([2, 8, 12, 14, 18, 20, 24, 30] : List ℕ).map fun d => q ^ d - 1).prod := by
      rw [card_adjointGroup_E8, ordE8]
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
      ring
    rw [hE8, ordProj_pow_mul_prod hp hpq hq 120 _ hD]

end CFSG.RankThree.OrdinaryECrossPrime
