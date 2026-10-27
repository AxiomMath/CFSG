module

public import CFSG.Timmesfeld.Orders.ExceptionalUntwisted

public section

namespace CFSG.RankThree.PartOne.N143X

open CFSG CFSG.Assembly.LowTwoRank

theorem no_cube_dvd_m1 {q : ℕ} (hq : 2 ≤ q) : ¬ q ^ 3 ∣ 7 ^ 2 * 31 := by
  intro h
  have : q ^ 3 ≤ 7 ^ 2 * 31 := Nat.le_of_dvd (by norm_num) h
  have hq11 : q ≤ 11 := by
    by_contra hc
    have : 12 ^ 3 ≤ q ^ 3 := Nat.pow_le_pow_left (by omega) 3
    omega
  interval_cases q <;> omega

theorem no_cube_dvd_m2 {q : ℕ} (hq : 2 ≤ q) : ¬ q ^ 3 ∣ 7 ^ 2 * 31 * 127 := by
  intro h
  have : q ^ 3 ≤ 7 ^ 2 * 31 * 127 := Nat.le_of_dvd (by norm_num) h
  have hq57 : q ≤ 57 := by
    by_contra hc
    have : 58 ^ 3 ≤ q ^ 3 := Nat.pow_le_pow_left (by omega) 3
    omega
  interval_cases q <;> omega

theorem no_cube_dvd_m3 {q : ℕ} (hq : 2 ≤ q) : ¬ q ^ 3 ∣ 7 ^ 2 * 11 * 13 * 17 * 31 := by
  intro h
  have : q ^ 3 ≤ 7 ^ 2 * 11 * 13 * 17 * 31 := Nat.le_of_dvd (by norm_num) h
  have hq154 : q ≤ 154 := by
    by_contra hc
    have : 155 ^ 3 ≤ q ^ 3 := Nat.pow_le_pow_left (by omega) 3
    omega
  interval_cases q <;> omega

theorem no_cube_dvd_m4 {q : ℕ} (hq : 2 ≤ q) : ¬ q ^ 3 ∣ 7 ^ 2 * 13 * 17 := by
  intro h
  have : q ^ 3 ≤ 7 ^ 2 * 13 * 17 := Nat.le_of_dvd (by norm_num) h
  have hq22 : q ≤ 22 := by
    by_contra hc
    have : 23 ^ 3 ≤ q ^ 3 := Nat.pow_le_pow_left (by omega) 3
    omega
  interval_cases q <;> omega

theorem pow_three_dvd_of_dvd_mul {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) {a b c m N : ℕ}
    (hN : N ∣ 2 ^ a * 3 ^ b * 5 ^ c * m) (h : p ^ 3 ∣ N) : p ^ 3 ∣ m := by
  have h1 : p ^ 3 ∣ 2 ^ a * 3 ^ b * 5 ^ c * m := h.trans hN
  have hcop : Nat.Coprime (p ^ 3) (2 ^ a * 3 ^ b * 5 ^ c) := by
    refine Nat.Coprime.mul_right (Nat.Coprime.mul_right ?_ ?_) ?_ <;>
      exact Nat.Coprime.pow _ _ ((Nat.coprime_primes hp (by norm_num)).2 (by omega))
  exact hcop.dvd_of_dvd_mul_left h1

theorem card_dvd_card_GL_of_stated {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    (M : Subgroup (GL ι K)) {T : Type} [Group T] (e : T ≃* StatedProj M) :
    Nat.card T ∣ Nat.card (GL ι K) := by
  rw [Nat.card_congr e.toEquiv]
  exact (Subgroup.card_quotient_dvd_card _).trans (Subgroup.card_subgroup_dvd_card M)

theorem false_of_pow_three_psl_two {T : Type} [Group T] {n : ℕ} (hn : n = 6 ∨ n = 7)
    (hmod : StatedClassicalModel T .PSL n 2 1) {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p)
    {E : Subgroup T} (hcard : Nat.card E = p ^ 3) : False := by
  obtain ⟨hadm, K, _, _, hK, ⟨e⟩⟩ := hmod
  have : Fintype K := Fintype.ofFinite K
  have hK2 : Fintype.card K = 2 := by rw [Fintype.card_eq_nat_card, hK]; norm_num
  have hdvd : p ^ 3 ∣ Nat.card (GL (Fin n) K) := by
    rw [← hcard]
    exact (Subgroup.card_subgroup_dvd_card E).trans (card_dvd_card_GL_of_stated _ e)
  rw [Matrix.card_GL_field, hK2] at hdvd
  rcases hn with rfl | rfl
  · have : (∏ i : Fin 6, (2 ^ 6 - 2 ^ (i : ℕ))) = 2 ^ 15 * 3 ^ 4 * 5 ^ 1 * (7 ^ 2 * 31) := by
      simp [Fin.prod_univ_succ]
    rw [this] at hdvd
    exact no_cube_dvd_m1 hp.two_le (pow_three_dvd_of_dvd_mul hp hp7 dvd_rfl hdvd)
  · have : (∏ i : Fin 7, (2 ^ 7 - 2 ^ (i : ℕ))) =
        2 ^ 21 * 3 ^ 4 * 5 ^ 1 * (7 ^ 2 * 31 * 127) := by
      simp [Fin.prod_univ_succ]
    rw [this] at hdvd
    exact no_cube_dvd_m2 hp.two_le (pow_three_dvd_of_dvd_mul hp hp7 dvd_rfl hdvd)

theorem false_of_pow_three_psu_six_two {T : Type} [Group T]
    (hmod : StatedClassicalModel T .PSU 6 2 1) {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p)
    {E : Subgroup T} (hcard : Nat.card E = p ^ 3) : False := by
  obtain ⟨hadm, K, _, _, hK, ⟨e⟩⟩ := hmod
  have : Fintype K := Fintype.ofFinite K
  have hK2 : Fintype.card K = 4 := by rw [Fintype.card_eq_nat_card, hK]; norm_num
  have hdvd : p ^ 3 ∣ Nat.card (GL (Fin 6) K) := by
    rw [← hcard]
    exact (Subgroup.card_subgroup_dvd_card E).trans (card_dvd_card_GL_of_stated _ e)
  rw [Matrix.card_GL_field, hK2] at hdvd
  have : (∏ i : Fin 6, (4 ^ 6 - 4 ^ (i : ℕ))) =
      2 ^ 30 * 3 ^ 8 * 5 ^ 3 * (7 ^ 2 * 11 * 13 * 17 * 31) := by
    simp [Fin.prod_univ_succ]
  rw [this] at hdvd
  exact no_cube_dvd_m3 hp.two_le (pow_three_dvd_of_dvd_mul hp hp7 dvd_rfl hdvd)

theorem false_of_pow_three_F4_two
    {T : Type} [Group T] (hmod : CFSG.Blueprint.UntwistedChevalleyModel T .F4 2) {p : ℕ}
    (hp : p.Prime) (hp7 : 7 ≤ p) {E : Subgroup T} (hcard : Nat.card E = p ^ 3) : False := by
  have hT := CFSG.Timmesfeld.ExceptionalOrders.card_of_untwistedChevalleyModel_F4 hmod
  have hdvd : p ^ 3 ∣ CFSG.Open.ordF4 2 := by
    rw [← hT, ← hcard]
    exact Subgroup.card_subgroup_dvd_card E
  have : CFSG.Open.ordF4 2 = 2 ^ 24 * 3 ^ 6 * 5 ^ 2 * (7 ^ 2 * 13 * 17) := by
    simp [CFSG.Open.ordF4]
  rw [this] at hdvd
  exact no_cube_dvd_m4 hp.two_le (pow_three_dvd_of_dvd_mul hp hp7 dvd_rfl hdvd)

end CFSG.RankThree.PartOne.N143X
