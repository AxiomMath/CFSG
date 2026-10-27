module

public import CFSG.Sporadic.HNSchreier.ThreeBRels
public import Mathlib.GroupTheory.Sylow
public import Mathlib.Data.ZMod.QuotientGroup

public section

namespace CFSG.Sporadic.HNSchreier.ThreeBGroup

open ThreeBRels Subgroup

variable {C : Type*} [Group C] {z : C}

theorem pow_mod_of {x : C} {k : ℕ} (hx : x ^ k = 1) (n : ℕ) : x ^ n = x ^ (n % k) := by
  conv_lhs => rw [← Nat.div_add_mod n k, pow_add, pow_mul, hx, one_pow, one_mul]

theorem pow3_of {x : C} (h : x * x * x = 1) : x ^ 3 = 1 := by
  rw [pow_succ, pow_two, h]

section Central

variable (hz : ∀ g : C, g * z = z * g)
include hz

theorem zpow_comm (k : ℕ) (g : C) : g * z ^ k = z ^ k * g := by
  have hc : Commute g z := hz g
  exact (hc.pow_right k).eq

theorem zl (k : ℕ) (g h : C) : g * (z ^ k * h) = z ^ k * (g * h) := by
  rw [← mul_assoc g (z ^ k) h, zpow_comm hz k g, mul_assoc]

omit hz in
theorem zz (j k : ℕ) (h : C) : z ^ j * (z ^ k * h) = z ^ (j + k) * h := by
  rw [← mul_assoc, ← pow_add]

theorem v_pow {u v : C} {m : ℕ} (huv : v * u = z ^ m * (u * v)) :
    ∀ n : ℕ, v * u ^ n = z ^ (m * n) * (u ^ n * v)
  | 0 => by simp
  | n + 1 => by
    calc v * u ^ (n + 1) = (v * u ^ n) * u := by rw [pow_succ, mul_assoc]
      _ = z ^ (m * n) * (u ^ n * (v * u)) := by rw [v_pow huv n]; simp only [mul_assoc]
      _ = z ^ (m * n) * (z ^ m * (u ^ n * (u * v))) := by rw [huv, zl hz m (u ^ n)]
      _ = z ^ (m * (n + 1)) * (u ^ (n + 1) * v) := by
        rw [zz, pow_succ, Nat.mul_succ]; simp only [mul_assoc]

theorem pp {u v : C} {m : ℕ} (huv : v * u = z ^ m * (u * v)) (n : ℕ) (h : C) :
    v * (u ^ n * h) = z ^ (m * n) * (u ^ n * (v * h)) := by
  rw [← mul_assoc v (u ^ n) h, v_pow hz huv n, mul_assoc (z ^ (m * n)) (u ^ n * v) h,
    mul_assoc (u ^ n) v h]

theorem cmul {v w1 w2 : C} {e1 e2 : ℕ} (h1 : v * w1 = z ^ e1 * (w1 * v))
    (h2 : v * w2 = z ^ e2 * (w2 * v)) : v * (w1 * w2) = z ^ (e1 + e2) * (w1 * w2 * v) := by
  calc v * (w1 * w2) = (v * w1) * w2 := (mul_assoc _ _ _).symm
    _ = z ^ e1 * (w1 * (v * w2)) := by rw [h1]; simp only [mul_assoc]
    _ = z ^ e1 * (z ^ e2 * (w1 * (w2 * v))) := by rw [h2, zl hz e2 w1]
    _ = z ^ (e1 + e2) * (w1 * w2 * v) := by rw [zz]; simp only [mul_assoc]

theorem rev {u v : C} {m : ℕ} (hz3 : z ^ 3 = 1) (h : v * u = z ^ m * (u * v)) :
    u * v = z ^ (2 * m) * (v * u) := by
  have e : 2 * m + m = 3 * m := by ring
  rw [h, ← mul_assoc, ← pow_add, e, pow_mul, hz3, one_pow, one_mul]

theorem conj_of {v x : C} {e : ℕ} (hz3 : z ^ 3 = 1) (h : v * x = z ^ e * (x * v)) :
    x * v * x⁻¹ = z ^ (2 * e) * v := by
  have e3 : 2 * e + e = 3 * e := by ring
  rw [mul_inv_eq_iff_eq_mul, mul_assoc, h, zz, e3, pow_mul, hz3,
    one_pow, one_mul]

end Central

@[expose] def nf (z : C) (c : ℕ → C) (a b0 b1 b2 b3 : ℕ) : C :=
  z ^ a * (xs c 0 ^ b0 * (xs c 1 ^ b1 * (xs c 2 ^ b2 * xs c 3 ^ b3)))

@[expose] def rR (c : ℕ → C) : Subgroup C := closure {xs c 0, xs c 1, xs c 2, xs c 3}

section NF

variable {y : C} {c : ℕ → C} (hz : ∀ g : C, g * z = z * g) (h : Rels z y c)
include hz h

omit hz in
theorem z3 : z ^ 3 = 1 := pow3_of h.z_cube

omit hz in
theorem ord_z : orderOf z = 3 := orderOf_eq_prime (z3 h) h.z_ne

omit hz in
theorem x3 {i : ℕ} (hi : i < 4) : xs c i ^ 3 = 1 := pow3_of (h.x_cube i hi)

omit hz in
theorem c01 : xs c 0 * xs c 1 = z ^ 0 * (xs c 1 * xs c 0) := by rw [pow_zero, one_mul]; exact h.x12
omit hz in
theorem c02 : xs c 0 * xs c 2 = z ^ 1 * (xs c 2 * xs c 0) := by rw [pow_one]; exact h.x13
omit hz in
theorem c03 : xs c 0 * xs c 3 = z ^ 1 * (xs c 3 * xs c 0) := by rw [pow_one]; exact h.x14
omit hz in
theorem c12 : xs c 1 * xs c 2 = z ^ 0 * (xs c 2 * xs c 1) := by rw [pow_zero, one_mul]; exact h.x23
omit hz in
theorem c13 : xs c 1 * xs c 3 = z ^ 1 * (xs c 3 * xs c 1) := by rw [pow_one]; exact h.x24
omit hz in
theorem c23 : xs c 2 * xs c 3 = z ^ 2 * (xs c 3 * xs c 2) := by rw [pow_two]; exact h.x34
omit hz h in
theorem cii (i : ℕ) : xs c i * xs c i = z ^ 0 * (xs c i * xs c i) := by rw [pow_zero, one_mul]

theorem c10 : xs c 1 * xs c 0 = z ^ (2 * 0) * (xs c 0 * xs c 1) := rev hz (z3 h) (c01 h)
theorem c20 : xs c 2 * xs c 0 = z ^ (2 * 1) * (xs c 0 * xs c 2) := rev hz (z3 h) (c02 h)
theorem c30 : xs c 3 * xs c 0 = z ^ (2 * 1) * (xs c 0 * xs c 3) := rev hz (z3 h) (c03 h)
theorem c21 : xs c 2 * xs c 1 = z ^ (2 * 0) * (xs c 1 * xs c 2) := rev hz (z3 h) (c12 h)
theorem c31 : xs c 3 * xs c 1 = z ^ (2 * 1) * (xs c 1 * xs c 3) := rev hz (z3 h) (c13 h)
theorem c32 : xs c 3 * xs c 2 = z ^ (2 * 2) * (xs c 2 * xs c 3) := rev hz (z3 h) (c23 h)

omit h in
theorem v_nf {v : C} {m0 m1 m2 m3 : ℕ} (h0 : v * xs c 0 = z ^ m0 * (xs c 0 * v))
    (h1 : v * xs c 1 = z ^ m1 * (xs c 1 * v)) (h2 : v * xs c 2 = z ^ m2 * (xs c 2 * v))
    (h3 : v * xs c 3 = z ^ m3 * (xs c 3 * v)) (a b0 b1 b2 b3 : ℕ) :
    v * nf z c a b0 b1 b2 b3 =
      z ^ (m0 * b0 + (m1 * b1 + (m2 * b2 + m3 * b3))) * (nf z c a b0 b1 b2 b3 * v) := by
  have ha : v * z ^ a = z ^ 0 * (z ^ a * v) := by rw [pow_zero, one_mul, zpow_comm hz]
  have := cmul hz ha (cmul hz (v_pow hz h0 b0) (cmul hz (v_pow hz h1 b1)
    (cmul hz (v_pow hz h2 b2) (v_pow hz h3 b3))))
  rw [zero_add] at this
  exact this

theorem x_nf {j : ℕ} (hj : j < 4) (a b0 b1 b2 b3 : ℕ) : ∃ w : ℕ,
    xs c j * nf z c a b0 b1 b2 b3 = z ^ w * (nf z c a b0 b1 b2 b3 * xs c j) ∧
      w % 3 = [b2 + b3, b3, 2 * b0 + 2 * b3, 2 * b0 + 2 * b1 + b2].getD j 0 % 3 := by
  interval_cases j
  · exact ⟨_, v_nf hz (cii 0) (c01 h) (c02 h) (c03 h) a b0 b1 b2 b3, by simp <;> omega⟩
  · exact ⟨_, v_nf hz (c10 hz h) (cii 1) (c12 h) (c13 h) a b0 b1 b2 b3, by simp <;> omega⟩
  · exact ⟨_, v_nf hz (c20 hz h) (c21 hz h) (cii 2) (c23 h) a b0 b1 b2 b3, by simp <;> omega⟩
  · exact ⟨_, v_nf hz (c30 hz h) (c31 hz h) (c32 hz h) (cii 3) a b0 b1 b2 b3, by simp <;> omega⟩

theorem x_mul_nf {j : ℕ} (hj : j < 4) (a b0 b1 b2 b3 : ℕ) :
    ∃ a' b0' b1' b2' b3', xs c j * nf z c a b0 b1 b2 b3 = nf z c a' b0' b1' b2' b3' := by
  have xl : ∀ (i n k : ℕ) (g : C), xs c i ^ n * (z ^ k * g) = z ^ k * (xs c i ^ n * g) :=
    fun i n k g => zl hz k _ g
  unfold nf
  interval_cases j
  · rw [zl hz a (xs c 0), ← mul_assoc (xs c 0) (xs c 0 ^ b0), ← pow_succ']
    exact ⟨_, _, _, _, _, rfl⟩
  · rw [zl hz a (xs c 1), pp hz (c10 hz h) b0, ← mul_assoc (xs c 1) (xs c 1 ^ b1), ← pow_succ',
      zz]
    exact ⟨_, _, _, _, _, rfl⟩
  · rw [zl hz a (xs c 2), pp hz (c20 hz h) b0, pp hz (c21 hz h) b1,
      ← mul_assoc (xs c 2) (xs c 2 ^ b2), ← pow_succ']
    simp only [xl, zz]
    exact ⟨_, _, _, _, _, rfl⟩
  · rw [zl hz a (xs c 3), pp hz (c30 hz h) b0, pp hz (c31 hz h) b1, pp hz (c32 hz h) b2,
      ← pow_succ']
    simp only [xl, zz]
    exact ⟨_, _, _, _, _, rfl⟩

omit hz in
theorem z_mem : z ∈ rR c := by
  have e : z = xs c 0 * xs c 2 * (xs c 0)⁻¹ * (xs c 2)⁻¹ := by
    rw [h.x13]; group
  rw [e]
  have h0 : xs c 0 ∈ rR c := subset_closure (by simp)
  have h2 : xs c 2 ∈ rR c := subset_closure (by simp)
  exact mul_mem (mul_mem (mul_mem h0 h2) (inv_mem h0)) (inv_mem h2)

omit hz h in
theorem x_mem {i : ℕ} (hi : i < 4) : xs c i ∈ rR c := by
  apply subset_closure
  interval_cases i <;> simp

omit hz in
theorem nf_mem (a b0 b1 b2 b3 : ℕ) : nf z c a b0 b1 b2 b3 ∈ rR c := by
  unfold nf
  have hx : ∀ i < 4, ∀ n : ℕ, xs c i ^ n ∈ rR c := fun i hi n => pow_mem (x_mem hi) n
  exact mul_mem (pow_mem (z_mem h) a) (mul_mem (hx 0 (by norm_num) b0) (mul_mem
    (hx 1 (by norm_num) b1) (mul_mem (hx 2 (by norm_num) b2) (hx 3 (by norm_num) b3))))

omit hz in
theorem nf_mod (a b0 b1 b2 b3 : ℕ) :
    nf z c a b0 b1 b2 b3 = nf z c (a % 3) (b0 % 3) (b1 % 3) (b2 % 3) (b3 % 3) := by
  unfold nf
  rw [← pow_mod_of (z3 h), ← pow_mod_of (x3 h (i := 0) (by norm_num)),
    ← pow_mod_of (x3 h (i := 1) (by norm_num)), ← pow_mod_of (x3 h (i := 2) (by norm_num)),
    ← pow_mod_of (x3 h (i := 3) (by norm_num))]

theorem mem_R_iff {g : C} :
    g ∈ rR c ↔ ∃ a b0 b1 b2 b3 : ℕ, g = nf z c a b0 b1 b2 b3 := by
  constructor
  · intro hg
    have step : ∀ x ∈ ({xs c 0, xs c 1, xs c 2, xs c 3} : Set C), ∀ g : C,
        (∃ a b0 b1 b2 b3 : ℕ, g = nf z c a b0 b1 b2 b3) →
          ∃ a b0 b1 b2 b3 : ℕ, x * g = nf z c a b0 b1 b2 b3 := by
      intro x hx g ⟨a, b0, b1, b2, b3, hg⟩
      subst hg
      have hj : ∃ j < 4, x = xs c j := by
        rcases hx with rfl | rfl | rfl | rfl
        exacts [⟨0, by norm_num, rfl⟩, ⟨1, by norm_num, rfl⟩, ⟨2, by norm_num, rfl⟩,
          ⟨3, by norm_num, rfl⟩]
      obtain ⟨j, hj, rfl⟩ := hj
      exact x_mul_nf hz h hj a b0 b1 b2 b3
    induction hg using closure_induction_left with
    | one => exact ⟨0, 0, 0, 0, 0, by simp [nf]⟩
    | mul_left x hx g _ ih => exact step x hx g ih
    | inv_mul_cancel x hx g _ ih =>
      have hinv : x⁻¹ = x * x := by
        rcases hx with rfl | rfl | rfl | rfl
        all_goals
          refine inv_eq_of_mul_eq_one_right ?_
          rw [← mul_assoc]
        exacts [h.x_cube 0 (by norm_num), h.x_cube 1 (by norm_num), h.x_cube 2 (by norm_num),
          h.x_cube 3 (by norm_num)]
      rw [hinv, mul_assoc]
      exact step x hx _ (step x hx g ih)
  · rintro ⟨a, b0, b1, b2, b3, rfl⟩
    exact nf_mem h a b0 b1 b2 b3

theorem nf_inj {a b0 b1 b2 b3 a' b0' b1' b2' b3' : ℕ} (ha : a < 3) (h0 : b0 < 3) (h1 : b1 < 3)
    (h2 : b2 < 3) (h3 : b3 < 3) (ha' : a' < 3) (h0' : b0' < 3) (h1' : b1' < 3) (h2' : b2' < 3)
    (h3' : b3' < 3) (e : nf z c a b0 b1 b2 b3 = nf z c a' b0' b1' b2' b3') :
    a = a' ∧ b0 = b0' ∧ b1 = b1' ∧ b2 = b2' ∧ b3 = b3' := by
  have key : ∀ j < 4, [b2 + b3, b3, 2 * b0 + 2 * b3, 2 * b0 + 2 * b1 + b2].getD j 0 % 3 =
      [b2' + b3', b3', 2 * b0' + 2 * b3', 2 * b0' + 2 * b1' + b2'].getD j 0 % 3 := by
    intro j hj
    obtain ⟨w, hw, hw3⟩ := x_nf hz h hj a b0 b1 b2 b3
    obtain ⟨w', hw', hw3'⟩ := x_nf hz h hj a' b0' b1' b2' b3'
    rw [e] at hw
    rw [hw] at hw'
    have hzw : z ^ w = z ^ w' := mul_right_cancel hw'
    rw [pow_eq_pow_iff_modEq, ord_z h] at hzw
    rw [← hw3, ← hw3']
    exact hzw
  have k0 := key 0 (by norm_num)
  have k1 := key 1 (by norm_num)
  have k2 := key 2 (by norm_num)
  have k3 := key 3 (by norm_num)
  simp only [List.getD_cons_zero, List.getD_cons_succ] at k0 k1 k2 k3
  have hb : b0 = b0' ∧ b1 = b1' ∧ b2 = b2' ∧ b3 = b3' := by omega
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hb
  refine ⟨?_, rfl, rfl, rfl, rfl⟩
  unfold nf at e
  have hza : z ^ a = z ^ a' := mul_right_cancel e
  rw [pow_eq_pow_iff_modEq, ord_z h] at hza
  unfold Nat.ModEq at hza
  omega

theorem card_R : Nat.card (rR c) = 243 := by
  let f : Fin 3 × Fin 3 × Fin 3 × Fin 3 × Fin 3 → rR c := fun p =>
    ⟨nf z c p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2, nf_mem h _ _ _ _ _⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨a, b0, b1, b2, b3⟩ ⟨a', b0', b1', b2', b3'⟩ e
      have e' := congrArg Subtype.val e
      obtain ⟨h1, h2, h3, h4, h5⟩ := nf_inj hz h a.2 b0.2 b1.2 b2.2 b3.2 a'.2 b0'.2 b1'.2 b2'.2
        b3'.2 e'
      simp only [Prod.mk.injEq, Fin.ext_iff]
      exact ⟨h1, h2, h3, h4, h5⟩
    · rintro ⟨g, hg⟩
      obtain ⟨a, b0, b1, b2, b3, rfl⟩ := (mem_R_iff hz h).1 hg
      refine ⟨(⟨a % 3, Nat.mod_lt _ (by norm_num)⟩, ⟨b0 % 3, Nat.mod_lt _ (by norm_num)⟩,
        ⟨b1 % 3, Nat.mod_lt _ (by norm_num)⟩, ⟨b2 % 3, Nat.mod_lt _ (by norm_num)⟩,
        ⟨b3 % 3, Nat.mod_lt _ (by norm_num)⟩), ?_⟩
      exact Subtype.ext (nf_mod h a b0 b1 b2 b3).symm
  rw [← Nat.card_congr (Equiv.ofBijective f hf)]
  simp [Nat.card_prod]

theorem center_R {g : C} (hg : g ∈ rR c) (hc : ∀ j < 4, xs c j * g = g * xs c j) :
    ∃ a : ℕ, g = z ^ a := by
  obtain ⟨a, b0, b1, b2, b3, rfl⟩ := (mem_R_iff hz h).1 hg
  rw [nf_mod h]
  have key : ∀ j < 4,
      [b2 % 3 + b3 % 3, b3 % 3, 2 * (b0 % 3) + 2 * (b3 % 3),
        2 * (b0 % 3) + 2 * (b1 % 3) + b2 % 3].getD j 0 % 3 = 0 := by
    intro j hj
    obtain ⟨w, hw, hw3⟩ := x_nf hz h hj (a % 3) (b0 % 3) (b1 % 3) (b2 % 3) (b3 % 3)
    rw [← nf_mod h, hc j hj, nf_mod h] at hw
    have hzw : z ^ w = 1 := by
      have h2 : z ^ w * (nf z c (a % 3) (b0 % 3) (b1 % 3) (b2 % 3) (b3 % 3) * xs c j) =
          1 * (nf z c (a % 3) (b0 % 3) (b1 % 3) (b2 % 3) (b3 % 3) * xs c j) := by
        rw [one_mul]
        exact hw.symm
      exact mul_right_cancel h2
    rw [← hw3, ← Nat.dvd_iff_mod_eq_zero, ← ord_z h]
    exact orderOf_dvd_of_pow_eq_one hzw
  have k0 := key 0 (by norm_num)
  have k1 := key 1 (by norm_num)
  have k2 := key 2 (by norm_num)
  have k3 := key 3 (by norm_num)
  simp only [List.getD_cons_zero, List.getD_cons_succ] at k0 k1 k2 k3
  have hb : b0 % 3 = 0 ∧ b1 % 3 = 0 ∧ b2 % 3 = 0 ∧ b3 % 3 = 0 := by omega
  obtain ⟨e0, e1, e2, e3⟩ := hb
  refine ⟨a % 3, ?_⟩
  simp [nf, e0, e1, e2, e3]

theorem conj_x0 {g : C} (hg : g ∈ rR c) : ∃ k : ℕ, g * xs c 0 * g⁻¹ = z ^ k * xs c 0 := by
  obtain ⟨a, b0, b1, b2, b3, rfl⟩ := (mem_R_iff hz h).1 hg
  obtain ⟨w, hw, -⟩ := x_nf hz h (j := 0) (by norm_num) a b0 b1 b2 b3
  exact ⟨_, conj_of hz (z3 h) hw⟩

theorem nf_ne (m m' : ℕ) : z ^ m * xs c 0 ≠ z ^ m' * (xs c 0 * (xs c 2 * xs c 2)) := by
  intro e
  have e1 : z ^ m * xs c 0 = nf z c m 1 0 0 0 := by simp [nf]
  have e2 : z ^ m' * (xs c 0 * (xs c 2 * xs c 2)) = nf z c m' 1 0 2 0 := by
    simp [nf, pow_two]
  rw [e1, e2, nf_mod h, nf_mod h m'] at e
  have := nf_inj hz h (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num))
    (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num))
    (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num))
    (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num)) e
  omega

omit hz in
theorem c0_x0 : c 0 * xs c 0 * (c 0)⁻¹ = z * (xs c 0 * (xs c 2 * xs c 2)) := by
  have := h.conj (0, 0, [0, 2, 7]) (by decide)
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at this
  rw [mul_inv_eq_iff_eq_mul, this]
  rfl

theorem c0_bad {j : ℕ} (hj : j % 3 ≠ 0) (k : ℕ) :
    c 0 ^ j * xs c 0 * (c 0 ^ j)⁻¹ ≠ z ^ k * xs c 0 := by
  have hc3 : c 0 ^ 3 = 1 := pow3_of h.c0_cube
  rw [pow_mod_of hc3 j]
  have hj' : j % 3 = 1 ∨ j % 3 = 2 := by omega
  rcases hj' with hj' | hj' <;> rw [hj'] <;> intro e
  · rw [pow_one, c0_x0 h] at e
    exact nf_ne hz h k 1 (by rw [← e, pow_one])
  · have e' : c 0 * (c 0 ^ 2 * xs c 0 * (c 0 ^ 2)⁻¹) * (c 0)⁻¹ = xs c 0 := by
      have : c 0 * (c 0 ^ 2 * xs c 0 * (c 0 ^ 2)⁻¹) * (c 0)⁻¹ =
          c 0 ^ 3 * xs c 0 * (c 0 ^ 3)⁻¹ := by group
      rw [this, hc3]; group
    have ez : c 0 * (z ^ k * xs c 0) * (c 0)⁻¹ = z ^ k * (c 0 * xs c 0 * (c 0)⁻¹) := by
      rw [← mul_assoc, zpow_comm hz k (c 0)]
      group
    rw [e, ez, c0_x0 h] at e'
    exact nf_ne hz h 0 (k + 1) (by
      rw [pow_zero, one_mul, pow_succ, mul_assoc]; exact e'.symm)

end NF

section Quat

variable {a b : C} (a4 : a * a * (a * a) = 1) (ane : a * a ≠ 1) (bsq : b * b = a * a)
  (aba : a * b * a = b)

include a4 in
theorem a_pow4 : a ^ 4 = 1 := by
  rw [← a4]
  simp only [pow_succ, pow_zero, one_mul, mul_assoc]

include a4 ane in
theorem ord_a : orderOf a = 4 := by
  have := orderOf_eq_prime_pow (p := 2) (n := 1) (x := a) (by rw [pow_one, pow_two]; exact ane)
    (by rw [← a_pow4 a4]; norm_num)
  rw [this]
  norm_num

include a4 aba in
theorem b_mul_pow : ∀ i : ℕ, b * a ^ i = a ^ (3 * i) * b
  | 0 => by simp
  | i + 1 => by
    have hba : b * a = a ^ 3 * b := by
      have e : a ^ 3 * (a * b * a) = a ^ 4 * (b * a) := by group
      rw [aba, a_pow4 a4, one_mul] at e
      exact e.symm
    rw [pow_succ, ← mul_assoc, b_mul_pow i, mul_assoc, hba, ← mul_assoc, ← pow_add]
    ring_nf

include aba ane in
theorem pow_ne_pow_mul (i j : ℕ) : a ^ i ≠ a ^ j * b := by
  intro e
  have hb : b = (a ^ j)⁻¹ * a ^ i := by rw [e]; group
  have hc : Commute a b := by
    rw [hb]
    exact ((Commute.refl a).pow_right j).inv_right.mul_right ((Commute.refl a).pow_right i)
  apply ane
  have e2 : b * (a * a) = b * 1 := by rw [mul_one, ← mul_assoc, ← hc.eq, aba]
  exact mul_left_cancel e2

include a4 bsq aba in
theorem mem_H {g : C} (hg : g ∈ closure ({a, b} : Set C)) :
    ∃ i : ℕ, g = a ^ i ∨ g = a ^ i * b := by
  have step : ∀ x ∈ ({a, b} : Set C), ∀ g : C, (∃ i : ℕ, g = a ^ i ∨ g = a ^ i * b) →
      ∃ i : ℕ, x * g = a ^ i ∨ x * g = a ^ i * b := by
    rintro x (rfl | rfl) g ⟨i, rfl | rfl⟩
    · exact ⟨i + 1, Or.inl (pow_succ' x i).symm⟩
    · exact ⟨i + 1, Or.inr (by rw [← mul_assoc, ← pow_succ'])⟩
    · exact ⟨3 * i, Or.inr (b_mul_pow a4 aba i)⟩
    · refine ⟨3 * i + 2, Or.inl ?_⟩
      rw [← mul_assoc, b_mul_pow a4 aba i, mul_assoc, bsq, pow_add, pow_two]
  induction hg using closure_induction_left with
  | one => exact ⟨0, Or.inl (pow_zero a).symm⟩
  | mul_left x hx g _ ih => exact step x hx g ih
  | inv_mul_cancel x hx g _ ih =>
    have hinv : x⁻¹ = x * (x * x) := by
      refine inv_eq_of_mul_eq_one_right ?_
      rcases hx with rfl | rfl
      · rw [← a4]; group
      · rw [← a4, ← bsq]; group
    rw [hinv, mul_assoc, mul_assoc]
    exact step x hx _ (step x hx _ (step x hx g ih))

include a4 ane bsq aba in
theorem card_H : Nat.card (closure ({a, b} : Set C)) = 8 := by
  have hA : ∀ i : ℕ, a ^ i ∈ closure ({a, b} : Set C) := fun i =>
    pow_mem (subset_closure (by simp)) i
  have hB : b ∈ closure ({a, b} : Set C) := subset_closure (by simp)
  let f : Fin 4 × Bool → closure ({a, b} : Set C) := fun p =>
    if p.2 then ⟨a ^ (p.1 : ℕ) * b, mul_mem (hA _) hB⟩ else ⟨a ^ (p.1 : ℕ), hA _⟩
  have hpow : ∀ i j : Fin 4, a ^ (i : ℕ) = a ^ (j : ℕ) → i = j := by
    intro i j e
    rw [pow_eq_pow_iff_modEq, ord_a a4 ane] at e
    unfold Nat.ModEq at e
    exact Fin.ext (by omega)
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨i, _ | _⟩ ⟨j, _ | _⟩ e <;> have e' := congrArg Subtype.val e <;>
        simp only [f, Bool.false_eq_true, ↓reduceIte] at e'
      · rw [hpow i j e']
      · exact absurd e' (pow_ne_pow_mul ane aba _ _)
      · exact absurd e'.symm (pow_ne_pow_mul ane aba _ _)
      · rw [hpow i j (mul_right_cancel e')]
    · rintro ⟨g, hg⟩
      have hmod : ∀ i : ℕ, a ^ i = a ^ (i % 4) := pow_mod_of (a_pow4 a4)
      obtain ⟨i, rfl | rfl⟩ := mem_H a4 bsq aba hg
      · exact ⟨(⟨i % 4, Nat.mod_lt _ (by norm_num)⟩, false), Subtype.ext (hmod i).symm⟩
      · exact ⟨(⟨i % 4, Nat.mod_lt _ (by norm_num)⟩, true),
          Subtype.ext (by simp only [f, ↓reduceIte]; rw [← hmod i])⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf)]
  simp [Nat.card_prod]

include a4 ane bsq aba in
theorem invol_H {t : C} (ht : t ∈ closure ({a, b} : Set C)) (htt : t * t = 1) (ht1 : t ≠ 1) :
    t = a * a := by
  obtain ⟨i, rfl | rfl⟩ := mem_H a4 bsq aba ht
  · rw [← pow_add] at htt
    have hd := orderOf_dvd_of_pow_eq_one htt
    rw [ord_a a4 ane] at hd
    rw [pow_mod_of (a_pow4 a4)] at ht1 ⊢
    have hi : i % 4 = 0 ∨ i % 4 = 2 := by omega
    rcases hi with hi | hi <;> rw [hi] at ht1 ⊢
    · exact absurd (pow_zero a) ht1
    · exact pow_two a
  · exfalso
    apply ane
    rw [← htt, ← mul_assoc, mul_assoc (a ^ i), b_mul_pow a4 aba i, ← mul_assoc, ← pow_add,
      mul_assoc, bsq]
    have e : i + 3 * i = 4 * i := by ring
    rw [e, pow_mul, a_pow4 a4, one_pow, one_mul]

end Quat

theorem fact29160 : (29160 : ℕ).factorization 2 = 3 ∧ (29160 : ℕ).factorization 3 = 6 ∧
    (29160 : ℕ).factorization 5 = 1 := by
  have e : (29160 : ℕ) = 2 ^ 3 * 3 ^ 6 * 5 := by norm_num
  rw [e, Nat.factorization_mul (by norm_num) (by norm_num),
    Nat.factorization_mul (by norm_num) (by norm_num), Nat.factorization_pow,
    Nat.factorization_pow, Nat.prime_two.factorization, Nat.prime_three.factorization,
    Nat.prime_five.factorization]
  simp [Finsupp.single_apply]

open scoped Pointwise in
theorem conj_into [Finite C] {p : ℕ} [Fact p.Prime] {Q : Subgroup C}
    (hQ : Nat.card Q = p ^ (Nat.card C).factorization p) {g : C} {k : ℕ}
    (hg : orderOf g = p ^ k) : ∃ x : C, x * g * x⁻¹ ∈ Q := by
  have hP : IsPGroup p (zpowers g) := IsPGroup.of_card (by rw [Nat.card_zpowers, hg])
  obtain ⟨P, hP'⟩ := hP.exists_le_sylow
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq C P (Sylow.ofCard Q hQ)
  refine ⟨x, ?_⟩
  have hm : MulAut.conj x • g ∈ MulAut.conj x • (P : Subgroup C) :=
    smul_mem_pointwise_smul g _ _ (hP' (mem_zpowers g))
  rw [← Sylow.coe_subgroup_smul, hx, Sylow.coe_ofCard] at hm
  simpa [MulAut.smul_def] using hm

@[expose] def sS (c : ℕ → C) : Subgroup C := closure (insert (c 0) (rR c : Set C))

@[expose] def kK (c : ℕ → C) : Subgroup C := closure {g | ∃ l < 7, c l = g}

section Core

variable {y : C} {c : ℕ → C} (hz : ∀ g : C, g * z = z * g) (h : Rels z y c)
include hz h

omit hz in
theorem pw_mem (j : ℕ) : pw z c j ∈ rR c := by
  have hz' := z_mem h
  have hx : ∀ i < 4, xs c i ∈ rR c := fun i hi => x_mem hi
  rcases j with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | j
  · exact hz'
  · exact mul_mem hz' hz'
  · exact hx 0 (by norm_num)
  · exact mul_mem (hx 0 (by norm_num)) (hx 0 (by norm_num))
  · exact hx 1 (by norm_num)
  · exact mul_mem (hx 1 (by norm_num)) (hx 1 (by norm_num))
  · exact hx 2 (by norm_num)
  · exact mul_mem (hx 2 (by norm_num)) (hx 2 (by norm_num))
  · exact hx 3 (by norm_num)
  · exact mul_mem (hx 3 (by norm_num)) (hx 3 (by norm_num))
  · have e : pw z c (j + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) = 1 := by simp [pw]
    rw [e]
    exact one_mem _

omit hz in
theorem row_mem {r : ℕ × ℕ × List ℕ} (hr : r ∈ nRows) :
    c r.1 * xs c r.2.1 * (c r.1)⁻¹ ∈ rR c := by
  rw [mul_inv_eq_of_eq_mul (h.conj r hr)]
  refine list_prod_mem (fun x hx => ?_)
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx
  exact pw_mem h j

omit hz h in
theorem norm_of [Finite C] {g : C} (hg : ∀ i < 4, g * xs c i * g⁻¹ ∈ rR c) :
    g ∈ normalizer (rR c : Set C) := by
  have hle : rR c ≤ (rR c).comap (MulAut.conj g).toMonoidHom := by
    refine (closure_le _).2 ?_
    rintro x (rfl | rfl | rfl | rfl)
    exacts [hg 0 (by norm_num), hg 1 (by norm_num), hg 2 (by norm_num), hg 3 (by norm_num)]
  exact mem_normalizer_fintype (fun n hn => hle hn)

omit hz in
theorem c_norm [Finite C] {l : ℕ} (hl : l < 7) : c l ∈ normalizer (rR c : Set C) := by
  by_cases h35 : l = 3 ∨ l = 5
  · rcases h35 with rfl | rfl
    · exact le_normalizer (x_mem (c := c) (i := 0) (by norm_num))
    · exact le_normalizer (x_mem (c := c) (i := 1) (by norm_num))
  · apply norm_of
    intro i hi
    have key : ∀ l < 7, ¬(l = 3 ∨ l = 5) → ∀ i < 4, ∃ r ∈ nRows, r.1 = l ∧ r.2.1 = i := by
      decide
    obtain ⟨r, hr, rfl, rfl⟩ := key l hl h35 i hi
    exact row_mem h hr

omit hz h in
theorem c_memK {l : ℕ} (hl : l < 7) : c l ∈ kK c := subset_closure ⟨l, hl, rfl⟩

omit hz h in
theorem R_le_K : rR c ≤ kK c := by
  have g : ∀ l < 7, c l ∈ kK c := fun l hl => c_memK hl
  refine (closure_le _).2 ?_
  rintro x (rfl | rfl | rfl | rfl)
  · exact g 3 (by norm_num)
  · exact g 5 (by norm_num)
  · exact mul_mem (mul_mem (g 1 (by norm_num)) (g 0 (by norm_num))) (g 0 (by norm_num))
  · exact mul_mem (mul_mem (mul_mem (mul_mem (g 6 (by norm_num)) (g 1 (by norm_num)))
      (g 6 (by norm_num))) (g 4 (by norm_num))) (g 0 (by norm_num))

theorem mem_S [Finite C] {g : C} (hg : g ∈ sS c) :
    ∃ r ∈ rR c, ∃ k : ℕ, g = r * c 0 ^ k := by
  have step : ∀ x ∈ insert (c 0) (rR c : Set C), ∀ g : C, (∃ r ∈ rR c, ∃ k : ℕ, g = r * c 0 ^ k) →
      ∃ r ∈ rR c, ∃ k : ℕ, x * g = r * c 0 ^ k := by
    rintro x (hx | hx) g ⟨r, hr, k, rfl⟩
    · subst hx
      refine ⟨c 0 * r * (c 0)⁻¹, (mem_normalizer_iff.1 (c_norm h (l := 0) (by norm_num)) r).1 hr,
        k + 1, ?_⟩
      rw [pow_succ']
      group
    · exact ⟨x * r, mul_mem hx hr, k, (mul_assoc _ _ _).symm⟩
  induction hg using closure_induction_left with
  | one => exact ⟨1, one_mem _, 0, by simp⟩
  | mul_left x hx g _ ih => exact step x hx g ih
  | inv_mul_cancel x hx g _ ih =>
    rcases hx with rfl | hx
    · have hinv : (c 0)⁻¹ = c 0 * c 0 := by
        refine inv_eq_of_mul_eq_one_right ?_
        rw [← mul_assoc]
        exact h.c0_cube
      rw [hinv, mul_assoc]
      exact step _ (Set.mem_insert _ _) _ (step _ (Set.mem_insert _ _) g ih)
    · exact step _ (Set.mem_insert_of_mem _ (inv_mem hx)) g ih

theorem c0pow_mem {j : ℕ} (hj : c 0 ^ j ∈ rR c) : j % 3 = 0 := by
  by_contra hj3
  obtain ⟨k, hk⟩ := conj_x0 hz h hj
  exact c0_bad hz h hj3 k hk

theorem card_S [Finite C] : Nat.card (sS c) = 729 := by
  have hc3 : c 0 ^ 3 = 1 := pow3_of h.c0_cube
  have hR : ∀ r ∈ rR c, r ∈ sS c := fun r hr => subset_closure (Set.mem_insert_of_mem _ hr)
  have hc : c 0 ∈ sS c := subset_closure (Set.mem_insert _ _)
  let f : rR c × Fin 3 → sS c := fun p =>
    ⟨p.1 * c 0 ^ (p.2 : ℕ), mul_mem (hR _ p.1.2) (pow_mem hc _)⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨⟨r, hr⟩, k⟩ ⟨⟨r', hr'⟩, k'⟩ e
      have e1 : r * c 0 ^ (k : ℕ) = r' * c 0 ^ (k' : ℕ) := congrArg Subtype.val e
      have hinv : (c 0 ^ (k : ℕ))⁻¹ = c 0 ^ (2 * (k : ℕ)) := by
        refine inv_eq_of_mul_eq_one_right ?_
        have e3 : (k : ℕ) + 2 * k = 3 * k := by ring
        rw [← pow_add, e3, pow_mul, hc3, one_pow]
      have e2 : r'⁻¹ * r = c 0 ^ ((k' : ℕ) + 2 * k) := by
        rw [pow_add, ← hinv, inv_mul_eq_iff_eq_mul, ← mul_assoc, ← e1, mul_assoc,
          mul_inv_cancel, mul_one]
      have hm := c0pow_mem hz h (e2 ▸ mul_mem (inv_mem hr') hr)
      have hk : k = k' := Fin.ext (by omega)
      subst hk
      have hr : r = r' := mul_right_cancel e1
      subst hr
      rfl
    · rintro ⟨g, hg⟩
      obtain ⟨r, hr, k, rfl⟩ := mem_S hz h hg
      exact ⟨(⟨r, hr⟩, ⟨k % 3, Nat.mod_lt _ (by norm_num)⟩),
        Subtype.ext (by simp only [f]; rw [← pow_mod_of hc3])⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf)]
  simp [Nat.card_prod, card_R hz h]

theorem normal_R [Finite C] (hC : Nat.card C = 29160) (hy : y = c 6 * c 0 * c 0)
    (hy5 : orderOf y = 5) : (rR c).Normal := by
  have g : ∀ l < 7, c l ∈ kK c := fun l hl => c_memK hl
  have hH : closure ({qa c, qb c} : Set C) ≤ kK c := by
    refine (closure_le _).2 ?_
    rintro x (rfl | rfl)
    · exact mul_mem (mul_mem (g 6 (by norm_num)) (g 3 (by norm_num))) (g 0 (by norm_num))
    · refine list_prod_mem (fun x hx => ?_)
      obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hx
      exact g l (by simp at hl; omega)
  have hS : sS c ≤ kK c := by
    refine (closure_le _).2 ?_
    rintro x (rfl | hx)
    · exact g 0 (by norm_num)
    · exact R_le_K hx
  have hyK : y ∈ kK c := by
    rw [hy]
    exact mul_mem (mul_mem (g 6 (by norm_num)) (g 0 (by norm_num))) (g 0 (by norm_num))
  have h8 : 8 ∣ Nat.card (kK c) := by
    rw [← card_H h.a_four h.a_sq_ne h.b_sq h.aba]
    exact card_dvd_of_le hH
  have h5 : 5 ∣ Nat.card (kK c) := by
    rw [← hy5]
    exact Subgroup.orderOf_dvd_natCard _ hyK
  have h729 : 729 ∣ Nat.card (kK c) := by
    rw [← card_S hz h]
    exact card_dvd_of_le hS
  have hall : 8 * 5 * 729 ∣ Nat.card (kK c) :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num)
      (Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h8 h5) h729
  have hd : Nat.card (kK c) ∣ 29160 := hC ▸ card_subgroup_dvd_card (kK c)
  have htop : kK c = ⊤ := eq_top_of_card_eq _ (by rw [hC]; exact Nat.dvd_antisymm hd hall)
  have hle : kK c ≤ normalizer (rR c : Set C) := by
    refine (closure_le _).2 ?_
    rintro _ ⟨l, hl, rfl⟩
    exact c_norm h hl
  rw [htop, top_le_iff, normalizer_eq_top_iff] at hle
  exact hle

theorem threeB_core [Finite C] (hC : Nat.card C = 29160) (hy : y = c 6 * c 0 * c 0)
    (hy5 : orderOf y = 5) :
    Nat.card (rR c) = 243 ∧ (rR c).Normal ∧ centralizer (rR c : Set C) ≤ rR c := by
  obtain ⟨f2, f3, f5⟩ := fact29160
  have hN : (rR c).Normal := normal_R hz h hC hy hy5
  refine ⟨card_R hz h, hN, ?_⟩
  have hK0 : ∀ g ∈ centralizer (rR c : Set C), ∀ k : C,
      k * g * k⁻¹ ∈ centralizer (rR c : Set C) := by
    intro g hg k
    rw [mem_centralizer_iff]
    intro x hx
    have hx' : k⁻¹ * x * k⁻¹⁻¹ ∈ rR c := hN.conj_mem x hx k⁻¹
    rw [inv_inv] at hx'
    have e := (mem_centralizer_iff.1 hg) _ hx'
    calc x * (k * g * k⁻¹) = k * ((k⁻¹ * x * k) * g) * k⁻¹ := by group
      _ = k * (g * (k⁻¹ * x * k)) * k⁻¹ := by rw [e]
      _ = k * g * k⁻¹ * x := by group
  have hX : ∀ g ∈ centralizer (rR c : Set C), ∀ i < 4, xs c i * g = g * xs c i :=
    fun g hg i hi => (mem_centralizer_iff.1 hg) _ (x_mem hi)
  have no2 : ∀ t ∈ centralizer (rR c : Set C), orderOf t = 2 → False := by
    intro t ht ht2
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := conj_into (Q := closure ({qa c, qb c} : Set C))
      (by rw [card_H h.a_four h.a_sq_ne h.b_sq h.aba, hC, f2]; norm_num) (k := 1)
      (by rw [ht2, pow_one])
    have htt : t * t = 1 := by rw [← pow_two, ← ht2, pow_orderOf_eq_one]
    have hs := invol_H h.a_four h.a_sq_ne h.b_sq h.aba hk
      (by
        have e : k * t * k⁻¹ * (k * t * k⁻¹) = k * (t * t) * k⁻¹ := by group
        rw [e, htt, mul_one, mul_inv_cancel])
      (by
        intro e
        have e' : t = 1 := by simpa using e
        rw [e', orderOf_one] at ht2
        exact absurd ht2 (by norm_num))
    apply h.a_sq_x
    rw [← hs]
    exact (hX _ (hK0 t ht k) 0 (by norm_num)).symm
  have no5 : ∀ u ∈ centralizer (rR c : Set C), orderOf u = 5 → False := by
    intro u hu hu5
    have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    obtain ⟨k, hk⟩ := conj_into (Q := zpowers u)
      (by rw [Nat.card_zpowers, hu5, hC, f5, pow_one]) (k := 1) (by rw [hy5, pow_one])
    have hyc : k * y * k⁻¹ ∈ centralizer (rR c : Set C) := (zpowers_le.2 hu) hk
    have hy' := hK0 _ hyc k⁻¹
    have e : k⁻¹ * (k * y * k⁻¹) * k⁻¹⁻¹ = y := by group
    rw [e] at hy'
    exact h.y_x (hX y hy' 0 (by norm_num)).symm
  have p3 : ∀ g ∈ centralizer (rR c : Set C), ∀ e : ℕ, orderOf g = 3 ^ e → g ∈ rR c := by
    intro g hg e he
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨k, hk⟩ := conj_into (Q := sS c) (by rw [card_S hz h, hC, f3]; norm_num) he
    obtain ⟨r, hr, j, hj⟩ := mem_S hz h hk
    have hs := hK0 g hg k
    have hc3 : c 0 ^ 3 = 1 := pow3_of h.c0_cube
    by_cases hj3 : j % 3 = 0
    · have hsR : k * g * k⁻¹ ∈ rR c := by
        rw [hj, pow_mod_of hc3, hj3, pow_zero, mul_one]
        exact hr
      obtain ⟨a, ha⟩ := center_R hz h hsR (hX _ hs)
      have e : g = k⁻¹ * (k * g * k⁻¹) * k := by group
      rw [ha, mul_assoc, ← zpow_comm hz a k, ← mul_assoc, inv_mul_cancel, one_mul] at e
      rw [e]
      exact pow_mem (z_mem h) a
    · exfalso
      have hsx := hX _ hs 0 (by norm_num)
      rw [hj] at hsx
      obtain ⟨m, hm⟩ := conj_x0 hz h (inv_mem hr)
      apply c0_bad hz h hj3 m
      rw [← hm, inv_inv, mul_inv_eq_iff_eq_mul]
      have e : c 0 ^ j * xs c 0 = r⁻¹ * (r * c 0 ^ j * xs c 0) := by group
      rw [e, ← hsx]
      group
  intro g hg
  have hn : orderOf g ≠ 0 := (orderOf_pos g).ne'
  by_cases h2 : 2 ∣ orderOf g
  · exact (no2 _ (pow_mem hg _) (orderOf_pow_orderOf_div hn h2)).elim
  by_cases h5 : 5 ∣ orderOf g
  · exact (no5 _ (pow_mem hg _) (orderOf_pow_orderOf_div hn h5)).elim
  have hd : orderOf g ∣ 3 ^ 6 := by
    have h1 : orderOf g ∣ 3 ^ 6 * (2 ^ 3 * 5) := by
      have := orderOf_dvd_natCard g
      rw [hC] at this
      exact this
    have hc : Nat.Coprime (orderOf g) (2 ^ 3 * 5) :=
      Nat.Coprime.mul_right
        (Nat.Coprime.pow_right 3 (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd
          Nat.prime_two).2 h2)))
        (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_five).2 h5))
    exact hc.dvd_of_dvd_mul_right h1
  obtain ⟨e, -, he⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hd
  exact p3 g hg e he

end Core

section Transfer

variable {G : Type*} [Group G]

theorem rels_congr {y : C} {c d : ℕ → C} (hcd : ∀ l < 7, c l = d l) (h : Rels z y c) :
    Rels z y d := by
  have hx : xs c = xs d := by
    funext i
    simp only [xs, hcd 0 (by norm_num), hcd 1 (by norm_num), hcd 3 (by norm_num),
      hcd 4 (by norm_num), hcd 5 (by norm_num), hcd 6 (by norm_num)]
  have hqa : qa c = qa d := by
    simp only [qa, hcd 0 (by norm_num), hcd 3 (by norm_num), hcd 6 (by norm_num)]
  have hqb : qb c = qb d := by
    simp only [qb, List.map_cons, List.map_nil, hcd 0 (by norm_num), hcd 1 (by norm_num),
      hcd 2 (by norm_num), hcd 3 (by norm_num), hcd 6 (by norm_num)]
  have hpw : pw z c = pw z d := by
    funext j
    simp only [pw, hx]
  have hr : ∀ r ∈ nRows, r.1 < 7 := by decide
  refine ⟨h.z_cube, h.z_ne, hx ▸ h.x_cube, hx ▸ h.x13, hx ▸ h.x14, hx ▸ h.x24, hx ▸ h.x34,
    hx ▸ h.x12, hx ▸ h.x23, ?_, hqa ▸ h.a_four, hqa ▸ h.a_sq_ne, hqa ▸ hqb ▸ h.b_sq,
    hqa ▸ hqb ▸ h.aba, hqa ▸ hx ▸ h.a_sq_x, hcd 0 (by norm_num) ▸ h.c0_cube, hx ▸ h.y_x⟩
  intro r hr'
  rw [← hx, ← hpw, ← hcd r.1 (hr r hr')]
  exact h.conj r hr'

theorem xs_map (f : C →* G) (c : ℕ → C) (i : ℕ) : f (xs c i) = xs (f ∘ c) i := by
  rcases i with _ | _ | _ | _ | i <;> simp [xs]

theorem pw_map (f : C →* G) (c : ℕ → C) (j : ℕ) : f (pw z c j) = pw (f z) (f ∘ c) j := by
  rcases j with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | j <;> simp [pw, xs_map]

theorem rels_of_map {y : C} {c : ℕ → C} (f : C →* G) (hf : Function.Injective f)
    (h : Rels (f z) (f y) (f ∘ c)) : Rels z y c := by
  have hqa : f (qa c) = qa (f ∘ c) := by simp [qa]
  have hqb : f (qb c) = qb (f ∘ c) := by simp [qb, map_list_prod]
  have hpw : (⇑f ∘ pw z c) = pw (f z) (⇑f ∘ c) := funext (pw_map f c)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hf (by simpa using h.z_cube)
  · intro e
    exact h.z_ne (by rw [e, map_one])
  · intro i hi
    exact hf (by simpa [xs_map] using h.x_cube i hi)
  · exact hf (by simpa [xs_map] using h.x13)
  · exact hf (by simpa [xs_map] using h.x14)
  · exact hf (by simpa [xs_map] using h.x24)
  · exact hf (by simpa [xs_map] using h.x34)
  · exact hf (by simpa [xs_map] using h.x12)
  · exact hf (by simpa [xs_map] using h.x23)
  · intro r hr
    exact hf (by simpa [xs_map, map_list_prod, hpw] using h.conj r hr)
  · exact hf (by simpa [hqa] using h.a_four)
  · intro e
    exact h.a_sq_ne (by rw [← hqa, ← map_mul, e, map_one])
  · exact hf (by simpa [hqa, hqb] using h.b_sq)
  · exact hf (by simpa [hqa, hqb] using h.aba)
  · intro e
    exact h.a_sq_x (by simpa [hqa, xs_map] using congrArg f e)
  · exact hf (by simpa using h.c0_cube)
  · intro e
    exact h.y_x (by simpa [xs_map] using congrArg f e)

theorem threeB {z y : G} {c : ℕ → G} {K : Subgroup G} (hK : Nat.card K = 29160)
    (hzK : K ≤ centralizer {z}) (hz : z ∈ K) (hc : ∀ l < 7, c l ∈ K)
    (hy : y = c 6 * c 0 * c 0) (hy5 : orderOf y = 5) (h : Rels z y c) :
    ∃ R : Subgroup G, R ≤ K ∧ Nat.card R = 243 ∧ (∀ g ∈ K, ∀ r ∈ R, g * r * g⁻¹ ∈ R) ∧
      K ⊓ centralizer (R : Set G) ≤ R := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  let c' : ℕ → K := fun l => if hl : l < 7 then ⟨c l, hc l hl⟩ else 1
  have hyK : y ∈ K := by
    rw [hy]
    exact mul_mem (mul_mem (hc 6 (by norm_num)) (hc 0 (by norm_num))) (hc 0 (by norm_num))
  let z' : K := ⟨z, hz⟩
  let y' : K := ⟨y, hyK⟩
  have h' : Rels z' y' c' := by
    refine rels_of_map K.subtype K.subtype_injective (rels_congr ?_ h)
    intro l hl
    simp [c', hl]
  have hz' : ∀ g : K, g * z' = z' * g := fun g =>
    Subtype.ext (mem_centralizer_singleton_iff.1 (hzK g.2))
  have hy' : y' = c' 6 * c' 0 * c' 0 := Subtype.ext (by simp [c', y', hy])
  have hy5' : orderOf y' = 5 := by
    rw [← Subgroup.orderOf_coe]
    exact hy5
  obtain ⟨hcard, hN, hcen⟩ := threeB_core hz' h' hK hy' hy5'
  refine ⟨(rR c').map K.subtype, map_subtype_le _, ?_, ?_, ?_⟩
  · rw [card_map_of_injective K.subtype_injective, hcard]
  · rintro g hg _ ⟨r, hr, rfl⟩
    exact ⟨⟨g, hg⟩ * r * ⟨g, hg⟩⁻¹, hN.conj_mem r hr _, rfl⟩
  · rintro g ⟨hg, hgc⟩
    refine ⟨⟨g, hg⟩, hcen ?_, rfl⟩
    have hgc' : g ∈ centralizer ((rR c').map K.subtype : Set G) := hgc
    rw [mem_centralizer_iff] at hgc' ⊢
    intro r hr
    exact Subtype.ext (hgc' r ⟨r, hr, rfl⟩)

end Transfer

end CFSG.Sporadic.HNSchreier.ThreeBGroup

end
