module

public import CFSG.RankThree.PartTwo.Sec20.SimsAsc1411Order

import Mathlib.GroupTheory.NoncommCoprod

public section

namespace CFSG.RankThree.PartTwo.Sec20

private theorem false_of_dvd_heis_sum {k cz cb : ℕ} (hk : k ≤ 12) (hcz : cz < k) (hcb : cb < k)
    (h1 : 5 ∣ 2 ^ (k - cz) - 1) (h2 : 5 ∣ 2 ^ (k - cb) - 1)
    (h : 25 ∣ 2 ^ k + 4 * 2 ^ cz + 20 * 2 ^ cb) : False := by
  interval_cases k <;> interval_cases cz <;> interval_cases cb <;> omega

private theorem sum_ite_prod_five {P Z : Type*} [One P] [One Z] [Fintype P] [Fintype Z]
    [DecidableEq P] [DecidableEq Z] (hP : Fintype.card P = 5) (hZ : Fintype.card Z = 5)
    (A B C : ℕ) :
    ∑ g : P × Z, (if g.1 = 1 then (if g.2 = 1 then A else B) else C) = A + 4 * B + 20 * C := by
  have h1 : ∑ y : Z, (if y = 1 then A else B) = A + 4 * B := by
    rw [Fintype.sum_eq_add_sum_compl (1 : Z), if_pos rfl,
      Finset.sum_congr rfl (g := fun _ => B) fun y hy => if_neg (by simpa using hy),
      Finset.sum_const, Finset.card_compl, Finset.card_singleton, hZ, smul_eq_mul]
  have h2 : ∀ x : P, x ≠ 1 →
      ∑ y : Z, (if x = 1 then (if y = 1 then A else B) else C) = 5 * C := by
    intro x hx
    simp only [if_neg hx, Finset.sum_const, Finset.card_univ, hZ, smul_eq_mul]
  rw [Fintype.sum_prod_type, Fintype.sum_eq_add_sum_compl (1 : P),
    Finset.sum_congr rfl fun x hx => h2 x (by simpa using hx), Finset.sum_const,
    Finset.card_compl, Finset.card_singleton, hP, smul_eq_mul]
  simp only [if_true, h1]
  ring

section Fixed

variable {U : Type*} [Group U]

private theorem card_fixed_pow {σ : MulAut U} (hσ : σ ^ 5 = 1) {m : ℕ} (hm : ¬ 5 ∣ m) :
    Nat.card {u : U // (σ ^ m) u = u} = Nat.card {u : U // σ u = u} := by
  have hfix : ∀ (u : U) (τ : MulAut U) (n : ℕ), τ u = u → (τ ^ n) u = u := by
    intro u τ n h
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, MulAut.mul_apply, h, ih]
  obtain ⟨t, -, ht⟩ := Nat.exists_mul_mod_eq_one_of_coprime (k := 5) (n := m)
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_five).2 hm).symm (by norm_num)
  have hσt : σ = (σ ^ m) ^ t := by
    rw [← pow_mul, pow_eq_pow_mod _ hσ, ht, pow_one]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun u => ⟨fun h => ?_, hfix u σ m⟩)
  rw [hσt]
  exact hfix u _ t h

private theorem card_fixed_conj (c σ : MulAut U) :
    Nat.card {u : U // (c * σ * c⁻¹) u = u} = Nat.card {u : U // σ u = u} :=
  Nat.card_congr (Equiv.subtypeEquiv c.toEquiv fun u => by
    simp [MulAut.mul_apply]).symm

private theorem exists_sum_card_fixed {G : Type*} [Group G] [Fintype G] [Finite U]
    (φ : G →* MulAut U) :
    ∃ n : ℕ, ∑ g : G, Nat.card {u : U // φ g u = u} = n * Fintype.card G := by
  classical
  letI : MulAction G U := MulAction.compHom U φ
  have : Fintype U := Fintype.ofFinite U
  have : Fintype (Quotient (MulAction.orbitRel G U)) := Fintype.ofFinite _
  refine ⟨Fintype.card (Quotient (MulAction.orbitRel G U)), ?_⟩
  rw [← MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group G U]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [Fintype.card_eq_nat_card]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun u => Iff.rfl)

private theorem not_dvd_of_pow_ne_one {σ x : MulAut U} (hσ : σ ^ 5 = 1) {m : ℕ} (hm : σ ^ m = x)
    (hx : x ≠ 1) : ¬ 5 ∣ m := by
  rintro ⟨c, rfl⟩
  exact hx (by rw [← hm, pow_mul, hσ, one_pow])

end Fixed

section Commutators

variable {H : Type*} [Group H] {a b z : H}

private theorem heis_conj_pow (hz : z = a * b * a⁻¹ * b⁻¹) (hza : Commute z a)
    (hzb : Commute z b) (j : ℕ) : a ^ j * b * (a ^ j)⁻¹ = b * z ^ j := by
  have h1 : a * b * a⁻¹ = b * z := by
    calc a * b * a⁻¹ = z * b := by rw [hz]; group
      _ = b * z := hzb.eq
  have h3 : ∀ n : ℕ, a * z ^ n * a⁻¹ = z ^ n := fun n => by
    rw [mul_inv_eq_iff_eq_mul]
    exact (hza.symm.pow_right n).eq
  induction j with
  | zero => simp
  | succ n ih =>
    calc a ^ (n + 1) * b * (a ^ (n + 1))⁻¹ = a * (a ^ n * b * (a ^ n)⁻¹) * a⁻¹ := by
          rw [pow_succ']; group
      _ = (a * b * a⁻¹) * (a * z ^ n * a⁻¹) := by rw [ih]; group
      _ = b * z ^ (n + 1) := by rw [h1, h3, mul_assoc, ← pow_succ']

private theorem heis_pow_five (hz : z = a * b * a⁻¹ * b⁻¹) (hzb : Commute z b) (hb : b ^ 5 = 1) :
    z ^ 5 = 1 := by
  have h1 : a * b * a⁻¹ = z * b := by rw [hz]; group
  have h2 : (z * b) ^ 5 = 1 := by rw [← h1, conj_pow, hb]; group
  rwa [hzb.mul_pow, hb, mul_one] at h2

end Commutators

private theorem card_fixed_pow_mul_pow {U : Type*} [Group U] {a b z : MulAut U}
    (hz : z = a * b * a⁻¹ * b⁻¹) (hza : Commute z a) (hzb : Commute z b) (hb : b ^ 5 = 1)
    (hz5 : z ^ 5 = 1) {m : ℕ} (hm : ¬ 5 ∣ m) (i : ℕ) :
    Nat.card {u : U // (b ^ m * z ^ i) u = u} = Nat.card {u : U // b u = u} := by
  obtain ⟨t, -, ht⟩ := Nat.exists_mul_mod_eq_one_of_coprime (k := 5) (n := m)
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_five).2 hm).symm (by norm_num)
  have hzi : z ^ i = (z ^ (i * t)) ^ m := by
    rw [← pow_mul, show i * t * m = (m * t) * i by ring, pow_mul, pow_eq_pow_mod (m * t) hz5,
      ht, pow_one]
  have hσ : b * z ^ (i * t) = a ^ (i * t) * b * (a ^ (i * t))⁻¹ :=
    (heis_conj_pow hz hza hzb _).symm
  have hσ5 : (b * z ^ (i * t)) ^ 5 = 1 := by
    rw [hσ, conj_pow, hb]; group
  rw [hzi, ← (hzb.symm.pow_right (i * t)).mul_pow, card_fixed_pow hσ5 hm, hσ, card_fixed_conj]

theorem false_of_heisenberg_five_mulAut {U : Type*} [Group U] [Finite U] {k : ℕ}
    (hU : Nat.card U = 2 ^ k) (hk : k ≤ 12) {a b : MulAut U} (hb : b ^ 5 = 1)
    (hz : a * b * a⁻¹ * b⁻¹ ≠ 1) (hza : Commute (a * b * a⁻¹ * b⁻¹) a)
    (hzb : Commute (a * b * a⁻¹ * b⁻¹) b) : False := by
  classical
  generalize hzdef : a * b * a⁻¹ * b⁻¹ = z at hz hza hzb
  replace hzdef : z = a * b * a⁻¹ * b⁻¹ := hzdef.symm
  have hz5 : z ^ 5 = 1 := heis_pow_five hzdef hzb hb
  have hb1 : b ≠ 1 := fun h => hz (by rw [hzdef, h]; group)
  have hordz : orderOf z = 5 := orderOf_eq_prime (hp := ⟨Nat.prime_five⟩) hz5 hz
  have hordb : orderOf b = 5 := orderOf_eq_prime (hp := ⟨Nat.prime_five⟩) hb hb1
  obtain ⟨cz, hczk, hcz, hcz5⟩ :=
    exists_card_fixed_of_orderOf_eq_prime hU z Nat.prime_five (by norm_num) hordz
  obtain ⟨cb, hcbk, hcb, hcb5⟩ :=
    exists_card_fixed_of_orderOf_eq_prime hU b Nat.prime_five (by norm_num) hordb
  haveI : Finite (MulAut U) :=
    Finite.of_injective (fun σ : MulAut U => (σ : U → U)) fun x y h => MulEquiv.ext (congrFun h)
  have hcomm : ∀ (x : Subgroup.zpowers b) (y : Subgroup.zpowers z),
      Commute ((Subgroup.zpowers b).subtype x) ((Subgroup.zpowers z).subtype y) := by
    intro x y
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 x.2
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 y.2
    simp only [Subgroup.subtype_apply]
    rw [← hm, ← hn]
    exact hzb.symm.zpow_zpow m n
  let φ : Subgroup.zpowers b × Subgroup.zpowers z →* MulAut U :=
    (Subgroup.zpowers b).subtype.noncommCoprod (Subgroup.zpowers z).subtype hcomm
  letI : Fintype (Subgroup.zpowers b) := Fintype.ofFinite _
  letI : Fintype (Subgroup.zpowers z) := Fintype.ofFinite _
  have hPc : Fintype.card (Subgroup.zpowers b) = 5 := by
    rw [Fintype.card_eq_nat_card, Nat.card_zpowers, hordb]
  have hZc : Fintype.card (Subgroup.zpowers z) = 5 := by
    rw [Fintype.card_eq_nat_card, Nat.card_zpowers, hordz]
  have hfix : ∀ (x : Subgroup.zpowers b) (y : Subgroup.zpowers z),
      Nat.card {u : U // φ (x, y) u = u} =
        if x = 1 then (if y = 1 then 2 ^ k else 2 ^ cz) else 2 ^ cb := by
    intro x y
    have hφ : φ (x, y) = (x : MulAut U) * (y : MulAut U) := rfl
    obtain ⟨m, hm⟩ := (Submonoid.mem_powers_iff _ _).1 (mem_powers_iff_mem_zpowers.2 x.2)
    obtain ⟨i, hi⟩ := (Submonoid.mem_powers_iff _ _).1 (mem_powers_iff_mem_zpowers.2 y.2)
    by_cases hx : x = 1
    · have hx' : (x : MulAut U) = 1 := by simp [hx]
      by_cases hy : y = 1
      · have hy' : (y : MulAut U) = 1 := by simp [hy]
        rw [if_pos hx, if_pos hy, hφ, hx', hy', mul_one, ← hU]
        exact Nat.card_congr (Equiv.subtypeUnivEquiv fun u => rfl)
      · have hy' : (y : MulAut U) ≠ 1 := fun h => hy (Subtype.ext h)
        rw [if_pos hx, if_neg hy, hφ, hx', one_mul, ← hi, ← hcz]
        exact card_fixed_pow hz5 (not_dvd_of_pow_ne_one hz5 hi hy')
    · have hx' : (x : MulAut U) ≠ 1 := fun h => hx (Subtype.ext h)
      rw [if_neg hx, hφ, ← hm, ← hi, card_fixed_pow_mul_pow hzdef hza hzb hb hz5
        (not_dvd_of_pow_ne_one hb hm hx') i, hcb]
  obtain ⟨n, hn⟩ := exists_sum_card_fixed φ
  have hcard : Fintype.card (Subgroup.zpowers b × Subgroup.zpowers z) = 25 := by
    rw [Fintype.card_prod, hPc, hZc]
  rw [hcard, (Finset.sum_congr rfl fun g _ => hfix g.1 g.2).trans
    (sum_ite_prod_five hPc hZc _ _ _)] at hn
  exact false_of_dvd_heis_sum hk hczk hcbk hcz5 hcb5 ⟨n, by omega⟩

end CFSG.RankThree.PartTwo.Sec20
