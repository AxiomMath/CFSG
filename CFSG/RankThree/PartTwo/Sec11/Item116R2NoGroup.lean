module

public import CFSG.RankThree.PartTwo.Sec11.Item116R2NoLin
public import CFSG.RankThree.PartTwo.Sec11.Item116R2NoPow
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.RankThree.PartTwo.Sec11.R2No

theorem exists_normal_form_mul {G : Type*} [Group G] {x s r : G} {u u' : ℕ}
    (hzc : x * s = s * x) (hrx : r * x * r⁻¹ = x ^ u) (hrs : r * s * r⁻¹ = s ^ u') {a b : G}
    (ha : ∃ i t j : ℕ, a = x ^ i * s ^ t * r ^ j) (hb : ∃ i t j : ℕ, b = x ^ i * s ^ t * r ^ j) :
    ∃ i t j : ℕ, a * b = x ^ i * s ^ t * r ^ j := by
  obtain ⟨i, t, j, rfl⟩ := ha
  obtain ⟨i', t', j', rfl⟩ := hb
  exact ⟨i + i' * u ^ j, t + t' * u' ^ j, j + j', mul_normal_form hzc hrx hrs i t j i' t' j'⟩

theorem exists_normal_form_pow {G : Type*} [Group G] {x s r : G} {u u' : ℕ}
    (hzc : x * s = s * x) (hrx : r * x * r⁻¹ = x ^ u) (hrs : r * s * r⁻¹ = s ^ u') {a : G}
    (ha : ∃ i t j : ℕ, a = x ^ i * s ^ t * r ^ j) (n : ℕ) :
    ∃ i t j : ℕ, a ^ n = x ^ i * s ^ t * r ^ j := by
  induction n with
  | zero => exact ⟨0, 0, 0, by simp⟩
  | succ n ih =>
    rw [pow_succ]
    exact exists_normal_form_mul hzc hrx hrs ih ha

theorem exists_normal_form_inv {G : Type*} [Group G] [Finite G] {x s r : G} {u u' : ℕ}
    (hzc : x * s = s * x) (hrx : r * x * r⁻¹ = x ^ u) (hrs : r * s * r⁻¹ = s ^ u') {a : G}
    (ha : ∃ i t j : ℕ, a = x ^ i * s ^ t * r ^ j) :
    ∃ i t j : ℕ, a⁻¹ = x ^ i * s ^ t * r ^ j := by
  have hpos : 0 < orderOf a := orderOf_pos a
  have h1 : 1 ≤ orderOf a := by omega
  have e : a⁻¹ = a ^ (orderOf a - 1) := by
    apply inv_eq_of_mul_eq_one_right
    rw [← pow_succ', Nat.sub_add_cancel h1, pow_orderOf_eq_one]
  rw [e]
  exact exists_normal_form_pow hzc hrx hrs ha _

theorem exists_normal_form {G : Type*} [Group G] [Finite G] {x s r : G} {u u' : ℕ}
    (hzc : x * s = s * x) (hrx : r * x * r⁻¹ = x ^ u) (hrs : r * s * r⁻¹ = s ^ u') :
    ∀ y ∈ Subgroup.closure ({r, x, s} : Set G), ∃ i t j : ℕ, y = x ^ i * s ^ t * r ^ j := by
  intro y hy
  induction hy using Subgroup.closure_induction with
  | mem a ha =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with h | h | h
    · exact ⟨0, 0, 1, by simp [h]⟩
    · exact ⟨1, 0, 0, by simp [h]⟩
    · exact ⟨0, 1, 0, by simp [h]⟩
  | one => exact ⟨0, 0, 0, by simp⟩
  | mul a b _ _ iha ihb => exact exists_normal_form_mul hzc hrx hrs iha ihb
  | inv a _ iha => exact exists_normal_form_inv hzc hrx hrs iha

theorem exists_nat_pow_conj {G : Type*} [Group G] {r x : G} {e : ℤ}
    (hx : ∃ v : ℕ, x ^ 3 ^ v = 1) (hr : ∃ k : ℕ, r ^ 3 ^ k = 1) (h : r * x * r⁻¹ = x ^ e) :
    ∃ u : ℕ, u % 3 = 1 ∧ r * x * r⁻¹ = x ^ u := by
  obtain ⟨v, hv⟩ := hx
  obtain ⟨k, hk⟩ := hr
  by_cases hx1 : x = 1
  · refine ⟨1, by norm_num, ?_⟩
    rw [hx1]
    simp
  have hord_dvd : orderOf x ∣ 3 ^ v := orderOf_dvd_of_pow_eq_one hv
  obtain ⟨w, -, hw⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hord_dvd
  have hw0 : w ≠ 0 := by
    rintro rfl
    exact hx1 (orderOf_eq_one_iff.1 (by simpa using hw))
  have h3 : (3 : ℕ) ∣ orderOf x := by
    rw [hw]
    exact dvd_pow_self 3 hw0
  have hpos : 0 < orderOf x := by
    rw [hw]
    positivity
  have key : ∀ j : ℕ, r ^ j * x * (r ^ j)⁻¹ = x ^ (e ^ j) := by
    intro j
    induction j with
    | zero => simp
    | succ n ih =>
      calc r ^ (n + 1) * x * (r ^ (n + 1))⁻¹
          = r * (r ^ n * x * (r ^ n)⁻¹) * r⁻¹ := by
            simp only [pow_succ', mul_inv_rev, mul_assoc]
        _ = r * x ^ (e ^ n) * r⁻¹ := by rw [ih]
        _ = (r * x * r⁻¹) ^ (e ^ n) := by rw [conj_zpow]
        _ = (x ^ e) ^ (e ^ n) := by rw [h]
        _ = x ^ (e * e ^ n) := (zpow_mul x e (e ^ n)).symm
        _ = x ^ (e ^ (n + 1)) := by rw [pow_succ, mul_comm]
  have hfix : x = x ^ (e ^ (3 ^ k)) := by
    have := key (3 ^ k)
    rw [hk, one_mul, inv_one, mul_one] at this
    exact this
  have hdvd : (orderOf x : ℤ) ∣ e ^ (3 ^ k) - 1 := by
    apply orderOf_dvd_iff_zpow_eq_one.2
    rw [zpow_sub, zpow_one, ← hfix]
    simp
  have h3z : (3 : ℤ) ∣ (orderOf x : ℤ) := by exact_mod_cast h3
  have h3' : (3 : ℤ) ∣ e ^ (3 ^ k) - 1 := dvd_trans h3z hdvd
  have hodd : Odd (3 ^ k) := Odd.pow (by decide : Odd (3 : ℕ))
  have hne : 3 ^ k ≠ 0 := by positivity
  have he1 : e % 3 = 1 := by
    rcases (by omega : e % 3 = 0 ∨ e % 3 = 1 ∨ e % 3 = 2) with h0 | h1 | h2
    · exfalso
      have h3e : (3 : ℤ) ∣ e := by omega
      have h3p : (3 : ℤ) ∣ e ^ (3 ^ k) := dvd_pow h3e hne
      generalize e ^ (3 ^ k) = P at h3p h3'
      omega
    · exact h1
    · exfalso
      have h3e : (3 : ℤ) ∣ e + 1 := by omega
      have h4 : e + 1 ∣ e ^ (3 ^ k) + 1 ^ (3 ^ k) := Odd.add_dvd_pow_add_pow e 1 hodd
      rw [one_pow] at h4
      have h3p : (3 : ℤ) ∣ e ^ (3 ^ k) + 1 := dvd_trans h3e h4
      generalize e ^ (3 ^ k) = P at h3p h3'
      omega
  have hNz : (0 : ℤ) < (orderOf x : ℤ) := by exact_mod_cast hpos
  have hm0 : 0 ≤ e % (orderOf x : ℤ) := Int.emod_nonneg e hNz.ne'
  have hm1 : e % (orderOf x : ℤ) % 3 = 1 := by
    rw [Int.emod_emod_of_dvd e h3z, he1]
  have hu : (((e % (orderOf x : ℤ)).toNat : ℕ) : ℤ) = e % (orderOf x : ℤ) :=
    Int.toNat_of_nonneg hm0
  refine ⟨(e % (orderOf x : ℤ)).toNat, ?_, ?_⟩
  · omega
  · rw [h, ← zpow_natCast, hu, zpow_mod_orderOf]

theorem pow_three_pow_eq_one_of_le {H : Type*} [Monoid H] {x : H} {a b : ℕ}
    (h : x ^ 3 ^ a = 1) (hab : a ≤ b) : x ^ 3 ^ b = 1 := by
  obtain ⟨c, rfl⟩ : ∃ c, b = a + c := ⟨b - a, by omega⟩
  rw [pow_add (3 : ℕ) a c, pow_mul, h, one_pow]

theorem exists_exponent_three {G : Type*} [Group G] [Finite G] {R : Subgroup G}
    (hR3 : IsPGroup 3 R) {y0 : G} (hy0 : y0 ∈ R) (hy1 : y0 ≠ 1) :
    ∃ m : ℕ, (∀ y ∈ R, y ^ 3 ^ (m + 1) = 1) ∧ ∃ y ∈ R, y ^ 3 ^ m ≠ 1 := by
  classical
  have hex : ∃ k : ℕ, ∀ y ∈ R, y ^ 3 ^ k = 1 := by
    haveI : Fintype R := Fintype.ofFinite R
    choose f hf using (hR3 : ∀ g : R, ∃ k : ℕ, g ^ 3 ^ k = 1)
    have hall : ∀ z : R, z ^ 3 ^ (Finset.sup (Finset.univ : Finset R) f) = 1 := fun z =>
      pow_three_pow_eq_one_of_le (hf z) (Finset.le_sup (f := f) (Finset.mem_univ z))
    refine ⟨Finset.sup (Finset.univ : Finset R) f, fun y hy => ?_⟩
    simpa using congrArg Subtype.val (hall ⟨y, hy⟩)
  obtain ⟨k0, hk0, hmin⟩ : ∃ k : ℕ, (∀ y ∈ R, y ^ 3 ^ k = 1) ∧
      ∀ j < k, ¬ ∀ y ∈ R, y ^ 3 ^ j = 1 :=
    ⟨Nat.find hex, Nat.find_spec hex, fun j hj => Nat.find_min hex hj⟩
  have hk0ne : k0 ≠ 0 := by
    rintro rfl
    have h1 := hk0 y0 hy0
    simp only [pow_zero, pow_one] at h1
    exact hy1 h1
  refine ⟨k0 - 1, ?_, ?_⟩
  · have hk : k0 - 1 + 1 = k0 := by omega
    rw [hk]
    exact hk0
  · by_contra hcon
    refine hmin (k0 - 1) (by omega) (fun y hy => ?_)
    by_contra hne
    exact hcon ⟨y, hy, hne⟩

theorem conj_pow_fix_aux {G : Type*} [Group G] {c w : G} (hwc : w * c * w⁻¹ = c) (i : ℕ) :
    w * c ^ i * w⁻¹ = c ^ i := by
  induction i with
  | zero => simp
  | succ n ih =>
    calc w * c ^ (n + 1) * w⁻¹ = (w * c ^ n * w⁻¹) * (w * c * w⁻¹) := by
          simp only [pow_succ, mul_assoc, inv_mul_cancel_left]
      _ = c ^ (n + 1) := by rw [ih, hwc, pow_succ]

theorem pow_conj_aux {G : Type*} [Group G] {a c w : G} (hwc : w * c * w⁻¹ = c)
    (hwa : w * a * w⁻¹ = a * c) (i : ℕ) :
    w ^ i * a * (w ^ i)⁻¹ = a * c ^ i := by
  induction i with
  | zero => simp
  | succ n ih =>
    calc w ^ (n + 1) * a * (w ^ (n + 1))⁻¹ = w * (w ^ n * a * (w ^ n)⁻¹) * w⁻¹ := by
          simp only [pow_succ', mul_inv_rev, mul_assoc]
      _ = w * (a * c ^ n) * w⁻¹ := by rw [ih]
      _ = (w * a * w⁻¹) * (w * c ^ n * w⁻¹) := by
          simp only [mul_assoc, inv_mul_cancel_left]
      _ = a * c ^ (n + 1) := by
          rw [hwa, conj_pow_fix_aux hwc n, pow_succ', mul_assoc]

theorem exists_three_element_moving {G : Type*} [Group G] [Finite G] {a c w : G}
    (hc3 : orderOf c = 3) (hwc : w * c * w⁻¹ = c) (hwa : w * a * w⁻¹ = a * c) :
    ∃ j : ℕ, (∃ k : ℕ, (w ^ j) ^ 3 ^ k = 1) ∧ w ^ j * a * (w ^ j)⁻¹ ≠ a := by
  have hN : orderOf w ≠ 0 := (orderOf_pos w).ne'
  obtain ⟨e, m, hm, hNm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN 3 (by norm_num)
  refine ⟨m, ⟨e, ?_⟩, ?_⟩
  · rw [← pow_mul, mul_comm, ← hNm, pow_orderOf_eq_one]
  · intro h
    rw [pow_conj_aux hwc hwa m] at h
    have h1 : a * c ^ m = a * 1 := by rw [mul_one]; exact h
    have h2 : c ^ m = 1 := mul_left_cancel h1
    have h3 : orderOf c ∣ m := orderOf_dvd_of_pow_eq_one h2
    rw [hc3] at h3
    exact hm h3

theorem power_map_central {G : Type*} [Group G] {A R : Subgroup G} {m : ℕ}
    (hAc : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u)
    (hmul : ∀ y ∈ R, ∀ y' ∈ R, (y * y') ^ 3 ^ m = y ^ 3 ^ m * y' ^ 3 ^ m)
    (hA : ∀ y ∈ R, y ^ 3 ^ m ∈ A) :
    ∀ y ∈ R, ∀ y' ∈ R, y' * y ^ 3 ^ m * y'⁻¹ = y ^ 3 ^ m := by
  intro y hy y' hy'
  have hinv : y'⁻¹ ∈ R := R.inv_mem hy'
  have hinvp : y'⁻¹ ^ 3 ^ m = (y' ^ 3 ^ m)⁻¹ := by
    have h1 : y' ^ 3 ^ m * y'⁻¹ ^ 3 ^ m = 1 := by
      rw [← hmul y' hy' y'⁻¹ hinv, mul_inv_cancel, one_pow]
    exact eq_inv_of_mul_eq_one_right h1
  have hconj : y' * y ^ 3 ^ m * y'⁻¹ = (y' * y * y'⁻¹) ^ 3 ^ m := by
    rw [conj_pow]
  have hyy : y' * y ∈ R := R.mul_mem hy' hy
  have hsplit : (y' * y * y'⁻¹) ^ 3 ^ m = y' ^ 3 ^ m * y ^ 3 ^ m * y'⁻¹ ^ 3 ^ m := by
    rw [hmul (y' * y) hyy y'⁻¹ hinv, hmul y' hy' y hy]
  have hcomm : y' ^ 3 ^ m * y ^ 3 ^ m = y ^ 3 ^ m * y' ^ 3 ^ m :=
    hAc _ (hA y' hy') _ (hA y hy)
  rw [hconj, hsplit, hinvp, hcomm]
  exact mul_inv_cancel_right _ _

theorem centralizer_le_B {G : Type*} [Group G] {A B R : Subgroup G} {a c d : G}
    (hAc : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u) (hA3 : ∀ u ∈ A, u ^ 3 = 1)
    (hBdef : B = Subgroup.closure ({c, d} : Set G)) (hcA : c ∈ A) (hdA : d ∈ A) (haA : a ∈ A)
    (hAgen : ∀ t ∈ A, ∃ i j k : ℕ, t = c ^ i * d ^ j * a ^ k)
    (hRcB : ∀ y ∈ R, ∀ b ∈ B, y * b * y⁻¹ = b)
    (hRAB : ∀ y ∈ R, a⁻¹ * (y * a * y⁻¹) ∈ B)
    (hact : ∃ y ∈ R, y * a * y⁻¹ ≠ a) :
    ∀ t ∈ A, (∀ y ∈ R, y * t * y⁻¹ = t) → t ∈ B := by
  obtain ⟨y0, hy0R, hy0a⟩ := hact
  have hcB : c ∈ B := by
    rw [hBdef]
    exact Subgroup.subset_closure (Set.mem_insert c {d})
  have hdB : d ∈ B := by
    rw [hBdef]
    exact Subgroup.subset_closure (Set.mem_insert_of_mem c (Set.mem_singleton d))
  have hBA : B ≤ A := by
    rw [hBdef, Subgroup.closure_le]
    exact Set.insert_subset_iff.mpr ⟨hcA, Set.singleton_subset_iff.mpr hdA⟩
  obtain ⟨b, hb_def⟩ : ∃ b : G, b = a⁻¹ * (y0 * a * y0⁻¹) := ⟨_, rfl⟩
  have hbB : b ∈ B := by
    rw [hb_def]
    exact hRAB y0 hy0R
  have hbA : b ∈ A := hBA hbB
  have hb1 : b ≠ 1 := by
    intro h
    apply hy0a
    rw [hb_def] at h
    exact (inv_mul_eq_one.mp h).symm
  have ha3 : a ^ 3 = 1 := hA3 a haA
  have hb3 : b ^ 3 = 1 := hA3 b hbA
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf b = 3 := orderOf_eq_prime hb3 hb1
  have hyab : y0 * a * y0⁻¹ = a * b := by
    rw [hb_def, mul_inv_cancel_left]
  have hcomm : Commute a b := hAc a haA b hbA
  have hconj_pow : ∀ (g x : G) (n : ℕ), g * x ^ n * g⁻¹ = (g * x * g⁻¹) ^ n := by
    intro g x n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, pow_succ, ← ih]
      group
  intro t htA hfix
  obtain ⟨i, j, k, rfl⟩ := hAgen t htA
  have hfix0 : y0 * (c ^ i * d ^ j * a ^ k) * y0⁻¹ = c ^ i * d ^ j * a ^ k :=
    hfix y0 hy0R
  have hc0 : y0 * c * y0⁻¹ = c := hRcB y0 hy0R c hcB
  have hd0 : y0 * d * y0⁻¹ = d := hRcB y0 hy0R d hdB
  have hconj : y0 * (c ^ i * d ^ j * a ^ k) * y0⁻¹
      = c ^ i * d ^ j * (y0 * a * y0⁻¹) ^ k := by
    calc y0 * (c ^ i * d ^ j * a ^ k) * y0⁻¹
        = (y0 * c ^ i * y0⁻¹) * (y0 * d ^ j * y0⁻¹) * (y0 * a ^ k * y0⁻¹) := by group
      _ = (y0 * c * y0⁻¹) ^ i * (y0 * d * y0⁻¹) ^ j * (y0 * a * y0⁻¹) ^ k := by
          rw [hconj_pow, hconj_pow, hconj_pow]
      _ = c ^ i * d ^ j * (y0 * a * y0⁻¹) ^ k := by rw [hc0, hd0]
  have hk : b ^ k = 1 := by
    have h1 : c ^ i * d ^ j * (a ^ k * b ^ k) = c ^ i * d ^ j * (a ^ k * 1) := by
      rw [mul_one, ← hcomm.mul_pow, ← hyab, ← hconj, hfix0]
    exact mul_left_cancel (mul_left_cancel h1)
  have h3k : 3 ∣ k := by
    have h := orderOf_dvd_of_pow_eq_one hk
    rwa [hord] at h
  obtain ⟨m, hm⟩ := h3k
  have hak : a ^ k = 1 := by
    rw [hm, pow_mul, ha3, one_pow]
  rw [hak, mul_one]
  exact mul_mem (pow_mem hcB i) (pow_mem hdB j)

theorem beta_mul {G : Type*} [Group G] {B R : Subgroup G} {a : G}
    (hRcB : ∀ y ∈ R, ∀ b ∈ B, y * b * y⁻¹ = b) {y y' : G} (hy : y ∈ R)
    (hb' : a⁻¹ * (y' * a * y'⁻¹) ∈ B) :
    a⁻¹ * ((y * y') * a * (y * y')⁻¹) =
      (a⁻¹ * (y * a * y⁻¹)) * (a⁻¹ * (y' * a * y'⁻¹)) := by
  have hb : y * (a⁻¹ * (y' * a * y'⁻¹)) * y⁻¹ = a⁻¹ * (y' * a * y'⁻¹) :=
    hRcB y hy _ hb'
  have key : (y * y') * a * (y * y')⁻¹ =
      (y * a * y⁻¹) * (y * (a⁻¹ * (y' * a * y'⁻¹)) * y⁻¹) := by
    group
  rw [key, hb]
  group

theorem beta_conj {G : Type*} [Group G] {A B R : Subgroup G} {a n b0 y : G}
    (hAc : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u) (haA : a ∈ A) (hBA : B ≤ A)
    (hRcB : ∀ y ∈ R, ∀ b ∈ B, y * b * y⁻¹ = b) (hy : y ∈ R) (hy' : n * y * n⁻¹ ∈ R)
    (hβy : a⁻¹ * (y * a * y⁻¹) ∈ B)
    (hβy' : a⁻¹ * ((n * y * n⁻¹) * a * (n * y * n⁻¹)⁻¹) ∈ B)
    (hnB : ∀ b ∈ B, n * b * n⁻¹ ∈ B) (hb0 : b0 ∈ B) (hna : n * a * n⁻¹ = a⁻¹ * b0) :
    a⁻¹ * ((n * y * n⁻¹) * a * (n * y * n⁻¹)⁻¹) =
      (n * (a⁻¹ * (y * a * y⁻¹)) * n⁻¹)⁻¹ := by
  obtain ⟨y', hy'def⟩ : ∃ y', y' = n * y * n⁻¹ := ⟨_, rfl⟩
  rw [← hy'def] at hy' hβy' ⊢
  obtain ⟨b, hbdef⟩ : ∃ b, b = a⁻¹ * (y * a * y⁻¹) := ⟨_, rfl⟩
  rw [← hbdef] at ⊢
  obtain ⟨b', hb'def⟩ : ∃ b', b' = a⁻¹ * (y' * a * y'⁻¹) := ⟨_, rfl⟩
  rw [← hb'def] at hβy' ⊢
  have hab : a * b = y * a * y⁻¹ := by
    rw [hbdef]; group
  have hab' : a * b' = y' * a * y'⁻¹ := by
    rw [hb'def]; group
  have hE1 : y' * (a⁻¹ * b0) * y'⁻¹ = (a⁻¹ * b0) * (n * b * n⁻¹) := by
    calc y' * (a⁻¹ * b0) * y'⁻¹ = y' * (n * a * n⁻¹) * y'⁻¹ := by rw [hna]
      _ = n * (y * a * y⁻¹) * n⁻¹ := by rw [hy'def]; group
      _ = n * (a * b) * n⁻¹ := by rw [hab]
      _ = (n * a * n⁻¹) * (n * b * n⁻¹) := by group
      _ = (a⁻¹ * b0) * (n * b * n⁻¹) := by rw [hna]
  have hYb0 : y' * b0 * y'⁻¹ = b0 := hRcB y' hy' b0 hb0
  have hE2 : y' * (a⁻¹ * b0) * y'⁻¹ = b'⁻¹ * (a⁻¹ * b0) := by
    calc y' * (a⁻¹ * b0) * y'⁻¹ = (y' * a * y'⁻¹)⁻¹ * (y' * b0 * y'⁻¹) := by group
      _ = (a * b')⁻¹ * b0 := by rw [hab', hYb0]
      _ = b'⁻¹ * (a⁻¹ * b0) := by group
  have hb0A : b0 ∈ A := hBA hb0
  have hXA : a⁻¹ * b0 ∈ A := A.mul_mem (A.inv_mem haA) hb0A
  have hb'A : b' ∈ A := hBA hβy'
  have hcomm : (a⁻¹ * b0) * b'⁻¹ = b'⁻¹ * (a⁻¹ * b0) :=
    hAc (a⁻¹ * b0) hXA b'⁻¹ (A.inv_mem hb'A)
  have h2 : (a⁻¹ * b0) * b'⁻¹ = (a⁻¹ * b0) * (n * b * n⁻¹) :=
    hcomm.trans (hE2.symm.trans hE1)
  have h3 : b'⁻¹ = n * b * n⁻¹ := mul_left_cancel h2
  exact inv_eq_iff_eq_inv.mp h3

theorem closure_pair_nf {G : Type*} [Group G] [Finite G] {c d : G} (hcd : c * d = d * c) :
    ∀ b ∈ Subgroup.closure ({c, d} : Set G), ∃ i j : ℕ, b = c ^ i * d ^ j := by
  intro b hb
  have hb' : b ∈ Subgroup.closure ({1, c, d} : Set G) := by
    refine Subgroup.closure_mono ?_ hb
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢
    tauto
  obtain ⟨i, t, j, h⟩ := exists_normal_form (x := c) (s := d) (r := 1) (u := 1) (u' := 1) hcd
    (by simp) (by simp) b hb'
  exact ⟨i, t, by simpa using h⟩

theorem core_group {G : Type} [Group G] [Finite G] {A B R : Subgroup G} {a c d x s r n : G}
    (hAc : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u) (hA3 : ∀ u ∈ A, u ^ 3 = 1)
    (hBdef : B = Subgroup.closure ({c, d} : Set G)) (haA : a ∈ A) (hcA : c ∈ A) (hdA : d ∈ A)
    (hc1 : c ≠ 1) (hdc : d ∉ Subgroup.zpowers c)
    (hAgen : ∀ t ∈ A, ∃ i j k : ℕ, t = c ^ i * d ^ j * a ^ k)
    (hΩ : ∀ z ∈ R, z ^ 3 = 1 → z ∈ A)
    (hR3 : IsPGroup 3 R)
    (hRcB : ∀ y ∈ R, ∀ b ∈ B, y * b * y⁻¹ = b)
    (hRAB : ∀ y ∈ R, a⁻¹ * (y * a * y⁻¹) ∈ B)
    (hRgen : R = Subgroup.closure ({r, x, s} : Set G)) (hsx : x * s = s * x)
    (hrx : ∃ e : ℤ, r * x * r⁻¹ = x ^ e) (hrs : ∃ e : ℤ, r * s * r⁻¹ = s ^ e)
    (hact : ∃ y ∈ R, y * a * y⁻¹ ≠ a)
    (hnR : ∀ y ∈ R, n * y * n⁻¹ ∈ R) (hnB : ∀ b ∈ B, n * b * n⁻¹ ∈ B)
    (hna : ∃ b0 ∈ B, n * a * n⁻¹ = a⁻¹ * b0)
    (hn2c : n ^ 2 * c * (n ^ 2)⁻¹ ∈ Subgroup.zpowers d)
    (hn2d : n ^ 2 * d * (n ^ 2)⁻¹ ∈ Subgroup.zpowers c) : False := by
  classical
  have hcB : c ∈ B := hBdef ▸ Subgroup.subset_closure (by simp)
  have hdB : d ∈ B := hBdef ▸ Subgroup.subset_closure (by simp)
  have hBA : B ≤ A := by
    rw [hBdef, Subgroup.closure_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact hcA
    · exact hdA
  have hrR : r ∈ R := hRgen ▸ Subgroup.subset_closure (by simp)
  have hxR : x ∈ R := hRgen ▸ Subgroup.subset_closure (by simp)
  have hsR : s ∈ R := hRgen ▸ Subgroup.subset_closure (by simp)
  have h3elt : ∀ y ∈ R, ∃ k : ℕ, y ^ 3 ^ k = 1 := fun y hy => by
    obtain ⟨k, hk⟩ := hR3 ⟨y, hy⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  obtain ⟨e, he⟩ := hrx
  obtain ⟨u, hu, hrxu⟩ := exists_nat_pow_conj (h3elt x hxR) (h3elt r hrR) he
  obtain ⟨e', he'⟩ := hrs
  obtain ⟨u', hu', hrsu⟩ := exists_nat_pow_conj (h3elt s hsR) (h3elt r hrR) he'
  have hNF : ∀ y ∈ R, ∃ i t j : ℕ, y = x ^ i * s ^ t * r ^ j := by
    intro y hy
    rw [hRgen] at hy
    exact exists_normal_form hsx hrxu hrsu y hy
  obtain ⟨y0, hy0R, hy0a⟩ := hact
  have hy01 : y0 ≠ 1 := by
    rintro rfl
    apply hy0a
    simp
  obtain ⟨m, hexp, y1, hy1R, hy1⟩ := exists_exponent_three hR3 hy0R hy01
  have hmul : ∀ y ∈ R, ∀ y' ∈ R, (y * y') ^ 3 ^ m = y ^ 3 ^ m * y' ^ 3 ^ m := by
    intro y hy y' hy'
    obtain ⟨i, t, j, rfl⟩ := hNF y hy
    obtain ⟨i', t', j', rfl⟩ := hNF y' hy'
    exact power_map_mul hsx hrxu hrsu hu hu' (hexp x hxR) (hexp s hsR) i t j i' t' j'
  have hπA : ∀ y ∈ R, y ^ 3 ^ m ∈ A := by
    intro y hy
    apply hΩ _ (R.pow_mem hy _)
    rw [← pow_mul, ← pow_succ]
    exact hexp y hy
  have hπc := power_map_central hAc hmul hπA
  have hπB : ∀ y ∈ R, y ^ 3 ^ m ∈ B := fun y hy =>
    centralizer_le_B hAc hA3 hBdef hcA hdA haA hAgen hRcB hRAB ⟨y0, hy0R, hy0a⟩ _ (hπA y hy)
      (fun y' hy' => hπc y hy y' hy')
  have hBc : ∀ b1 b2 : B, b1 * b2 = b2 * b1 := fun b1 b2 =>
    Subtype.ext (hAc _ (hBA b1.2) _ (hBA b2.2))
  let π : R →* B :=
    { toFun := fun y => ⟨(y : G) ^ 3 ^ m, hπB y y.2⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun y y' => by
        apply Subtype.ext
        exact hmul y y.2 y' y'.2 }
  let β : R →* B :=
    { toFun := fun y => ⟨a⁻¹ * ((y : G) * a * (y : G)⁻¹), hRAB y y.2⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun y y' => by
        apply Subtype.ext
        exact beta_mul hRcB y.2 (hRAB y' y'.2) }
  let τ : B →* B :=
    { toFun := fun b => ⟨n * (b : G) * n⁻¹, hnB b b.2⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun b b' => by
        apply Subtype.ext
        show n * ((b : G) * b') * n⁻¹ = (n * b * n⁻¹) * (n * b' * n⁻¹)
        group }
  let σ : R → R := fun y => ⟨n * (y : G) * n⁻¹, hnR y y.2⟩
  obtain ⟨b0, hb0B, hnab0⟩ := hna
  have hc3 : c ^ 3 = 1 := hA3 c hcA
  have hd3 : d ^ 3 = 1 := hA3 d hdA
  have hcd : c * d = d * c := hAc c hcA d hdA
  have hd1 : d ≠ 1 := fun h => hdc (h ▸ Subgroup.one_mem _)
  refine core_false_abs (R := R) (B := B) hBc (c := ⟨c, hcB⟩) (d := ⟨d, hdB⟩) ?_ ?_ ?_ ?_ ?_ τ
    ?_ ?_ ?_ ?_ β π ?_ ?_ σ ?_ ?_ ?_
  · intro h
    exact hc1 (congrArg Subtype.val h)
  · apply Subtype.ext
    simpa using hc3
  · apply Subtype.ext
    simpa using hd3
  · intro h
    apply hdc
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, by simpa using congrArg Subtype.val hk⟩
  · intro b
    obtain ⟨i, j, hij⟩ := closure_pair_nf hcd b.1 (hBdef ▸ b.2)
    exact ⟨i, j, Subtype.ext (by simpa using hij)⟩
  · obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hn2c
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, Subtype.ext ?_⟩
    simp only [Subgroup.coe_zpow]
    show d ^ k = n * (n * c * n⁻¹) * n⁻¹
    rw [hk, pow_two]
    group
  · intro h
    have h1 : n * (n * c * n⁻¹) * n⁻¹ = 1 := congrArg Subtype.val h
    apply hc1
    calc c = (n * n)⁻¹ * (n * (n * c * n⁻¹) * n⁻¹) * (n * n) := by group
      _ = 1 := by rw [h1]; group
  · obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hn2d
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, Subtype.ext ?_⟩
    simp only [Subgroup.coe_zpow]
    show c ^ k = n * (n * d * n⁻¹) * n⁻¹
    rw [hk, pow_two]
    group
  · intro h
    have h1 : n * (n * d * n⁻¹) * n⁻¹ = 1 := congrArg Subtype.val h
    apply hd1
    calc d = (n * n)⁻¹ * (n * (n * d * n⁻¹) * n⁻¹) * (n * n) := by group
      _ = 1 := by rw [h1]; group
  · refine ⟨⟨y0, hy0R⟩, fun h => hy0a ?_⟩
    have h1 : a⁻¹ * (y0 * a * y0⁻¹) = 1 := congrArg Subtype.val h
    exact (inv_mul_eq_one.mp h1).symm
  · exact ⟨⟨y1, hy1R⟩, fun h => hy1 (congrArg Subtype.val h)⟩
  · intro y
    apply Subtype.ext
    show (n * (y : G) * n⁻¹) ^ 3 ^ m = n * (y : G) ^ 3 ^ m * n⁻¹
    rw [conj_pow]
  · intro y
    apply Subtype.ext
    show a⁻¹ * ((n * (y : G) * n⁻¹) * a * (n * (y : G) * n⁻¹)⁻¹) =
      (n * (a⁻¹ * ((y : G) * a * (y : G)⁻¹)) * n⁻¹)⁻¹
    exact beta_conj hAc haA hBA hRcB y.2 (hnR y y.2) (hRAB y y.2) (hRAB _ (hnR y y.2)) hnB hb0B
      hnab0
  · refine ⟨⟨x, hxR⟩, ⟨s, hsR⟩, ⟨r, hrR⟩, fun y => ?_⟩
    obtain ⟨i, t, j, h⟩ := hNF y.1 y.2
    exact ⟨i, t, j, Subtype.ext (by simpa using h)⟩

end CFSG.RankThree.PartTwo.Sec11.R2No
