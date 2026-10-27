module

public import CFSG.LocalAnalysis.UniquenessCase.Lie.Sp4Act

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open CFSG.LocalAnalysis.UniquenessCase.UC22

variable {K : Type} [Field K]

private theorem tali_pow_card [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n) (x : Kˣ) :
    x ^ 2 ^ n = x := by
  have h1 : x ^ (2 ^ n - 1) = 1 := by
    have := pow_card_eq_one' (G := Kˣ) (x := x)
    rwa [Nat.card_units, hK] at this
  calc x ^ 2 ^ n = x ^ (2 ^ n - 1) * x := by rw [← pow_succ, Nat.sub_add_cancel Nat.one_le_two_pow]
    _ = x := by rw [h1, one_mul]

private theorem tali_pow_two_pow_mul [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n) (x : Kˣ)
    (p : ℕ) : x ^ 2 ^ (n * p) = x := by
  induction p with
  | zero => simp
  | succ p ih => rw [Nat.mul_succ, pow_add, pow_mul, ih, tali_pow_card hK]

private theorem tali_sq_eq_one [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 1 ≤ n)
    {x : Kˣ} (h : x ^ 2 = 1) : x = 1 := by
  calc x = x ^ 2 ^ n := (tali_pow_card hK x).symm
    _ = (x ^ 2) ^ 2 ^ (n - 1) := by rw [← pow_mul, ← pow_succ', Nat.sub_add_cancel hn]
    _ = 1 := by rw [h, one_pow]

private theorem tali_inv_eq_self [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 1 ≤ n)
    {x : Kˣ} (h : x⁻¹ = x) : x = 1 :=
  tali_sq_eq_one hK hn (by rw [sq]; nth_rewrite 1 [← h]; exact inv_mul_cancel x)

private theorem tali_pow_two_pow_ne_one [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n)
    (hn : 1 ≤ n) {a : Kˣ} (ha : a ≠ 1) (l : ℕ) : a ^ 2 ^ l ≠ 1 := by
  induction l with
  | zero => simpa using ha
  | succ l ih =>
    intro h
    exact ih (tali_sq_eq_one hK hn (by rw [← pow_mul, ← pow_succ]; exact h))

private theorem tali_two_pow_ne_one [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n)
    (hn : 1 ≤ n) {a : Kˣ} (ha : a ≠ 1) (l : ℕ) : a ^ ((2 : ℤ) ^ l) ≠ 1 := by
  have e : a ^ ((2 : ℤ) ^ l) = a ^ 2 ^ l := by
    rw [← zpow_natCast]
    push_cast
    rfl
  rw [e]
  exact tali_pow_two_pow_ne_one hK hn ha l

private theorem tali_per [Finite K] {n l : ℕ} (hK : Nat.card K = 2 ^ n) (hl : n = 2 * l + 1)
    (a : Kˣ) : a ^ (2 * 2 ^ l * 2 ^ l - 1 : ℤ) = 1 := by
  have h1 : a ^ (2 ^ n - 1) = 1 := by
    have := pow_card_eq_one' (G := Kˣ) (x := a)
    rwa [Nat.card_units, hK] at this
  have h2 : (2 * 2 ^ l * 2 ^ l - 1 : ℤ) = ((2 ^ n - 1 : ℕ) : ℤ) := by
    rw [Nat.cast_sub Nat.one_le_two_pow, hl]
    push_cast
    ring
  rw [h2, zpow_natCast, h1]

private theorem tali_exists_orderOf [Finite K] {n ℓ : ℕ} (hK : Nat.card K = 2 ^ n)
    (hℓ : ℓ.Prime) (hd : ℓ ∣ 2 ^ n - 1) : ∃ a : Kˣ, orderOf a = ℓ := by
  have := Fact.mk hℓ
  exact exists_prime_orderOf_dvd_card' ℓ (by rwa [Nat.card_units, hK])

private theorem tali_orderOf_vec {ℓ : ℕ} (hℓ : ℓ.Prime) {a : Kˣ} (ha : orderOf a = ℓ)
    (p q : ℤ) (hne : a ^ p ≠ 1 ∨ a ^ q ≠ 1) : orderOf (![a ^ p, a ^ q] : Fin 2 → Kˣ) = ℓ := by
  have := Fact.mk hℓ
  have key : ∀ r : ℤ, (a ^ r) ^ ℓ = 1 := fun r => by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← ha, pow_orderOf_eq_one,
      one_zpow]
  apply orderOf_eq_prime
  · funext i
    fin_cases i
    · exact key p
    · exact key q
  · intro h
    rcases hne with h' | h'
    · exact h' (congrFun h 0)
    · exact h' (congrFun h 1)

private theorem tali_vec_inv_of {a : Kˣ} {N : ℤ} (ha : a ^ N = 1) {e₁ e₂ p q : ℤ}
    (h₁ : N ∣ e₁ + p) (h₂ : N ∣ e₂ + q) :
    (![a ^ e₁, a ^ e₂] : Fin 2 → Kˣ) = (![a ^ p, a ^ q])⁻¹ := by
  have key : ∀ e f : ℤ, N ∣ e + f → a ^ e = (a ^ f)⁻¹ := by
    rintro e f ⟨r, hr⟩
    apply eq_inv_of_mul_eq_one_left
    rw [← zpow_add, hr, zpow_mul, ha, one_zpow]
  funext i
  fin_cases i
  · exact key _ _ h₁
  · exact key _ _ h₂

private theorem tali_refl [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n)
    {φ : (Fin 2 → Kˣ) → (Fin 2 → Kˣ)} (hinv : ∀ t, φ (φ t) = t) (p q : ℤ)
    (hpq : ∀ a : Kˣ, φ ![a ^ p, a ^ q] = (![a ^ p, a ^ q])⁻¹)
    (hne : ∀ a : Kˣ, a ≠ 1 → a ^ p ≠ 1 ∨ a ^ q ≠ 1) :
    (∀ t, φ (φ t) = t) ∧ ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ 2 ^ n - 1 → ∃ t, orderOf t = ℓ ∧ φ t = t⁻¹ := by
  refine ⟨hinv, fun ℓ hℓ hd => ?_⟩
  obtain ⟨a, ha⟩ := tali_exists_orderOf hK hℓ hd
  have ha1 : a ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ha
    exact hℓ.one_lt.ne ha
  exact ⟨_, tali_orderOf_vec hℓ ha p q (hne a ha1), hpq a⟩

private def tali_sp (b : Bool) (ε δ : ℤ) (s : Fin 2 → Kˣ) : Fin 2 → Kˣ :=
  if b then ![s 1 ^ δ, s 0 ^ ε] else ![s 0 ^ ε, s 1 ^ δ]

private theorem tali_sp_one (s : Fin 2 → Kˣ) : tali_sp false 1 1 s = s := by
  funext i
  fin_cases i <;> simp [tali_sp]

private theorem tali_sp_comp (b b' : Bool) (ε δ ε' δ' : ℤ) (s : Fin 2 → Kˣ) :
    tali_sp b ε δ (tali_sp b' ε' δ' s) =
      if b' then tali_sp (!b) (ε' * δ) (δ' * ε) s else tali_sp b (ε' * ε) (δ' * δ) s := by
  cases b <;> cases b' <;> funext i <;> fin_cases i <;> simp [tali_sp, zpow_mul]

private theorem tali_sp_pow (b : Bool) (ε δ : ℤ) (s : Fin 2 → Kˣ) (N : ℕ) :
    tali_sp b ε δ s ^ N = tali_sp b ε δ (s ^ N) := by
  cases b <;> funext i <;> fin_cases i <;> simp [tali_sp, ← zpow_natCast, ← zpow_mul, mul_comm]

private theorem tali_sp_vec_false (ε δ : ℤ) (a : Kˣ) (p q : ℤ) :
    tali_sp false ε δ ![a ^ p, a ^ q] = ![a ^ (p * ε), a ^ (q * δ)] := by
  funext i
  fin_cases i <;> simp [tali_sp, zpow_mul]

private theorem tali_sp_vec_true (ε δ : ℤ) (a : Kˣ) (p q : ℤ) :
    tali_sp true ε δ ![a ^ p, a ^ q] = ![a ^ (q * δ), a ^ (p * ε)] := by
  funext i
  fin_cases i <;> simp [tali_sp, zpow_mul]

private theorem tali_sign_mul {ε δ : ℤ} (hε : ε = 1 ∨ ε = -1) (hδ : δ = 1 ∨ δ = -1) :
    ε * δ = 1 ∨ ε * δ = -1 := by
  rcases hε with rfl | rfl <;> rcases hδ with rfl | rfl <;> simp

private theorem tali_sp_comp_sign (b b' : Bool) {ε δ ε' δ' : ℤ} (hε : ε = 1 ∨ ε = -1)
    (hδ : δ = 1 ∨ δ = -1) (hε' : ε' = 1 ∨ ε' = -1) (hδ' : δ' = 1 ∨ δ' = -1) :
    ∃ (b'' : Bool) (ε'' δ'' : ℤ), (ε'' = 1 ∨ ε'' = -1) ∧ (δ'' = 1 ∨ δ'' = -1) ∧
      ∀ s : Fin 2 → Kˣ, tali_sp b ε δ (tali_sp b' ε' δ' s) = tali_sp b'' ε'' δ'' s := by
  cases b'
  · exact ⟨b, ε' * ε, δ' * δ, tali_sign_mul hε' hε, tali_sign_mul hδ' hδ,
      fun s => by simp [tali_sp_comp]⟩
  · exact ⟨!b, ε' * δ, δ' * ε, tali_sign_mul hε' hδ, tali_sign_mul hδ' hε,
      fun s => by simp [tali_sp_comp]⟩

private theorem tali_rho_apply (t : Fin 2 → Kˣ) :
    uc22pwI2Rho K t = ![t 0 * t 1, t 0 * (t 1)⁻¹] := rfl

private theorem tali_rho_diag (ε : ℤ) (s : Fin 2 → Kˣ) :
    uc22pwI2Rho K (tali_sp false ε ε s) = tali_sp false ε ε (uc22pwI2Rho K s) := by
  funext i
  fin_cases i <;> simp [tali_sp, tali_rho_apply, mul_zpow]

private theorem tali_rho_refl {ε δ : ℤ} (h : δ = -ε) (s : Fin 2 → Kˣ) :
    uc22pwI2Rho K (tali_sp false ε δ s) = tali_sp true ε ε (uc22pwI2Rho K s) := by
  subst h
  funext i
  fin_cases i <;> simp [tali_sp, tali_rho_apply, mul_zpow]

private theorem tali_rho_swap {ε δ δ' : ℤ} (h : δ = ε) (h' : δ' = -ε) (s : Fin 2 → Kˣ) :
    uc22pwI2Rho K (tali_sp true ε δ s) = tali_sp false ε δ' (uc22pwI2Rho K s) := by
  subst h h'
  funext i
  fin_cases i <;> simp [tali_sp, tali_rho_apply, mul_zpow, mul_comm]

private theorem tali_rho_rot {ε δ : ℤ} (h : δ = -ε) (s : Fin 2 → Kˣ) :
    uc22pwI2Rho K (tali_sp true ε δ s) = tali_sp true δ ε (uc22pwI2Rho K s) := by
  subst h
  funext i
  fin_cases i <;> simp [tali_sp, tali_rho_apply, mul_zpow, mul_comm]

private theorem tali_rho_sp (b : Bool) {ε δ : ℤ} (hε : ε = 1 ∨ ε = -1) (hδ : δ = 1 ∨ δ = -1) :
    ∃ (b' : Bool) (ε' δ' : ℤ), (ε' = 1 ∨ ε' = -1) ∧ (δ' = 1 ∨ δ' = -1) ∧
      ∀ s : Fin 2 → Kˣ, uc22pwI2Rho K (tali_sp b ε δ s) = tali_sp b' ε' δ' (uc22pwI2Rho K s) := by
  rcases hε with rfl | rfl <;> rcases hδ with rfl | rfl <;> cases b
  · exact ⟨false, 1, 1, by norm_num, by norm_num, tali_rho_diag 1⟩
  · exact ⟨false, 1, -1, by norm_num, by norm_num, tali_rho_swap rfl rfl⟩
  · exact ⟨true, 1, 1, by norm_num, by norm_num, tali_rho_refl rfl⟩
  · exact ⟨true, -1, 1, by norm_num, by norm_num, tali_rho_rot rfl⟩
  · exact ⟨true, -1, -1, by norm_num, by norm_num, tali_rho_refl (by norm_num)⟩
  · exact ⟨true, 1, -1, by norm_num, by norm_num, tali_rho_rot (by norm_num)⟩
  · exact ⟨false, -1, -1, by norm_num, by norm_num, tali_rho_diag (-1)⟩
  · exact ⟨false, -1, 1, by norm_num, by norm_num, tali_rho_swap rfl (by norm_num)⟩

private theorem tali_rho_iter_sp (k : ℕ) (b : Bool) {ε δ : ℤ} (hε : ε = 1 ∨ ε = -1)
    (hδ : δ = 1 ∨ δ = -1) :
    ∃ (b' : Bool) (ε' δ' : ℤ), (ε' = 1 ∨ ε' = -1) ∧ (δ' = 1 ∨ δ' = -1) ∧
      ∀ s : Fin 2 → Kˣ, (⇑(uc22pwI2Rho K))^[k] (tali_sp b ε δ s) =
        tali_sp b' ε' δ' ((⇑(uc22pwI2Rho K))^[k] s) := by
  induction k generalizing b ε δ with
  | zero => exact ⟨b, ε, δ, hε, hδ, fun s => rfl⟩
  | succ k ih =>
    obtain ⟨b₁, ε₁, δ₁, h₁, h₁', hr⟩ := tali_rho_sp (K := K) b hε hδ
    obtain ⟨b₂, ε₂, δ₂, h₂, h₂', hk⟩ := ih b₁ h₁ h₁'
    exact ⟨b₂, ε₂, δ₂, h₂, h₂', fun s => by
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, hr, hk]⟩

private theorem tali_iter {b : Bool} {ε δ : ℤ} (hε : ε = 1 ∨ ε = -1) (hδ : δ = 1 ∨ δ = -1)
    {k : ℕ} {φ : (Fin 2 → Kˣ) → (Fin 2 → Kˣ)}
    (hφ : ∀ t, φ t = tali_sp b ε δ ((⇑(uc22pwI2Rho K))^[k] t)) (N : ℕ) :
    ∃ (b' : Bool) (ε' δ' : ℤ), (ε' = 1 ∨ ε' = -1) ∧ (δ' = 1 ∨ δ' = -1) ∧
      ∀ t, φ^[N] t = tali_sp b' ε' δ' ((⇑(uc22pwI2Rho K))^[k * N] t) := by
  induction N with
  | zero => exact ⟨false, 1, 1, Or.inl rfl, Or.inl rfl, fun t => by simp [tali_sp_one]⟩
  | succ N ih =>
    obtain ⟨b₁, ε₁, δ₁, h₁, h₁', hN⟩ := ih
    obtain ⟨b₂, ε₂, δ₂, h₂, h₂', hk⟩ := tali_rho_iter_sp (K := K) k b₁ h₁ h₁'
    obtain ⟨b₃, ε₃, δ₃, h₃, h₃', hc⟩ := tali_sp_comp_sign (K := K) b b₂ hε hδ h₂ h₂'
    refine ⟨b₃, ε₃, δ₃, h₃, h₃', fun t => ?_⟩
    rw [Function.iterate_succ_apply', hN, hφ, hk, hc, Nat.mul_succ, Nat.add_comm (k * N) k,
      Function.iterate_add_apply]

private theorem tali_iter_eq (m : ℕ) (t : Fin 2 → Kˣ) :
    (⇑(uc22pwI2Rho K))^[m] t = ((uc22pwI2RhoE K) ^ m) t := by
  rw [Monoid.End.coe_pow]
  rfl

private theorem tali_pow_of_sp {b : Bool} {ε δ : ℤ} (hε : ε = 1 ∨ ε = -1) (r : ℕ)
    (h : ∀ t : Fin 2 → Kˣ, tali_sp b ε δ (t ^ 2 ^ r) = t) (x : Kˣ) : x ^ 2 ^ (2 * r) = x := by
  have h1 := congrFun (h ![x, 1]) 0
  have hx2 : (x ^ 2 ^ r) ^ 2 ^ r = x ^ 2 ^ (2 * r) := by rw [← pow_mul, ← pow_add, two_mul]
  cases b
  · rcases hε with rfl | rfl
    · have h2 : x ^ 2 ^ r = x := by simpa [tali_sp] using h1
      rw [← hx2, h2, h2]
    · have h2 : x ^ 2 ^ r = x⁻¹ := by simpa [tali_sp, inv_eq_iff_eq_inv] using h1
      rw [← hx2, h2, inv_pow, h2, inv_inv]
  · have h2 : 1 = x := by simpa [tali_sp] using h1
    rw [← h2, one_pow]

private theorem tali_dvd [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n)
    (hodd : Odd n) {b : Bool} {ε δ : ℤ} (hε : ε = 1 ∨ ε = -1) (hδ : δ = 1 ∨ δ = -1) {k : ℕ}
    {φ : (Fin 2 → Kˣ) → (Fin 2 → Kˣ)}
    (hφ : ∀ t, φ t = tali_sp b ε δ ((⇑(uc22pwI2Rho K))^[k] t))
    (hord : ∃ j : ℕ, φ^[2 ^ j] = id) : n ∣ k := by
  obtain ⟨j, hj⟩ := hord
  have hj' : φ^[2 ^ (j + 1)] = id := by
    rw [pow_succ, Function.iterate_mul, hj, Function.iterate_id]
  obtain ⟨b', ε', δ', h₁, -, hit⟩ := tali_iter hε hδ hφ (2 ^ (j + 1))
  have hfix : ∀ t, tali_sp b' ε' δ' (t ^ 2 ^ (k * 2 ^ j)) = t := fun t => by
    have := hit t
    rw [hj', id_eq, tali_iter_eq, show k * 2 ^ (j + 1) = 2 * (k * 2 ^ j) by ring,
      uc22pwI2Rho_pow_even] at this
    exact this.symm
  have hx := tali_pow_of_sp h₁ _ hfix
  refine uc22pwI2_dvd_of_rho_pow (e := 0) (k := j + 2) hodd hK hn (by simp) fun t => ?_
  rw [← pow_mul, show k * 2 ^ (j + 2) = 2 * (2 * (k * 2 ^ j)) by ring, uc22pwI2Rho_pow_even]
  funext i
  exact hx (t i)

private theorem tali_rho_iter_cases [Finite K] {n l k : ℕ} (hK : Nat.card K = 2 ^ n)
    (hl : n = 2 * l + 1) (hnk : n ∣ k) :
    (∀ t, (⇑(uc22pwI2Rho K))^[k] t = t) ∨
      ∀ t, (⇑(uc22pwI2Rho K))^[k] t = uc22pwI2Rho K (t ^ 2 ^ l) := by
  obtain ⟨p, rfl⟩ := hnk
  rcases Nat.even_or_odd' p with ⟨q, rfl | rfl⟩
  · left
    intro t
    rw [tali_iter_eq, show n * (2 * q) = 2 * (n * q) by ring, uc22pwI2Rho_pow_even]
    funext i
    exact tali_pow_two_pow_mul hK (t i) q
  · right
    intro t
    rw [tali_iter_eq, show n * (2 * q + 1) = 2 * (n * q + l) + 1 by rw [hl]; ring,
      uc22pwI2Rho_pow_odd]
    congr 1
    funext i
    rw [Pi.pow_apply, Pi.pow_apply, pow_add, pow_mul, tali_pow_two_pow_mul hK]

private theorem tali_rot_fix [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 1 ≤ n)
    {ε δ : ℤ} (hεδ : δ * ε = -1) {t : Fin 2 → Kˣ} (h : tali_sp true ε δ t = t) : t = 1 := by
  have h0 : t 1 ^ δ = t 0 := congrFun h 0
  have h1 : t 0 ^ ε = t 1 := congrFun h 1
  have h2 : t 1 = 1 := by
    apply tali_inv_eq_self hK hn
    calc (t 1)⁻¹ = t 1 ^ (δ * ε) := by rw [hεδ, zpow_neg_one]
      _ = t 1 := by rw [zpow_mul, h0, h1]
  have h3 : t 0 = 1 := by rw [← h0, h2, one_zpow]
  funext i
  fin_cases i
  · exact h3
  · exact h2

private theorem tali_neg_fix [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 1 ≤ n)
    {t : Fin 2 → Kˣ} (h : tali_sp false (-1) (-1) t = t) : t = 1 := by
  have h0 : (t 0)⁻¹ = t 0 := by simpa [tali_sp] using congrFun h 0
  have h1 : (t 1)⁻¹ = t 1 := by simpa [tali_sp] using congrFun h 1
  funext i
  fin_cases i
  · exact tali_inv_eq_self hK hn h0
  · exact tali_inv_eq_self hK hn h1

private theorem tali_inner [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 1 ≤ n) (b : Bool)
    {ε δ : ℤ} (hε : ε = 1 ∨ ε = -1) (hδ : δ = 1 ∨ δ = -1) {φ : (Fin 2 → Kˣ) → (Fin 2 → Kˣ)}
    (hφ : ∀ t, φ t = tali_sp b ε δ t) (hfix : ∃ t₀, t₀ ≠ 1 ∧ φ t₀ = t₀) :
    (∀ t, φ t = t) ∨ ((∀ t, φ (φ t) = t) ∧
      ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ 2 ^ n - 1 → ∃ t, orderOf t = ℓ ∧ φ t = t⁻¹) := by
  obtain ⟨t₀, h₀, hf⟩ := hfix
  rw [hφ] at hf
  have hinv : ∀ t, φ (φ t) = tali_sp b ε δ (tali_sp b ε δ t) := fun t => by rw [hφ, hφ]
  rcases hε with rfl | rfl <;> rcases hδ with rfl | rfl <;> cases b
  · exact Or.inl fun t => by rw [hφ, tali_sp_one]
  · refine Or.inr (tali_refl hK (fun t => by simp [hinv, tali_sp_comp, tali_sp_one]) 1 (-1)
      (fun a => ?_) fun a ha => Or.inl (by simpa using ha))
    rw [hφ, tali_sp_vec_true]
    exact tali_vec_inv_of (zpow_zero a) ⟨0, by ring⟩ ⟨0, by ring⟩
  · refine Or.inr (tali_refl hK (fun t => by simp [hinv, tali_sp_comp, tali_sp_one]) 0 1
      (fun a => ?_) fun a ha => Or.inr (by simpa using ha))
    rw [hφ, tali_sp_vec_false]
    exact tali_vec_inv_of (zpow_zero a) ⟨0, by ring⟩ ⟨0, by ring⟩
  · exact (h₀ (tali_rot_fix hK hn (by norm_num) hf)).elim
  · refine Or.inr (tali_refl hK (fun t => by simp [hinv, tali_sp_comp, tali_sp_one]) 1 0
      (fun a => ?_) fun a ha => Or.inl (by simpa using ha))
    rw [hφ, tali_sp_vec_false]
    exact tali_vec_inv_of (zpow_zero a) ⟨0, by ring⟩ ⟨0, by ring⟩
  · exact (h₀ (tali_rot_fix hK hn (by norm_num) hf)).elim
  · exact (h₀ (tali_neg_fix hK hn hf)).elim
  · refine Or.inr (tali_refl hK (fun t => by simp [hinv, tali_sp_comp, tali_sp_one]) 1 1
      (fun a => ?_) fun a ha => Or.inl (by simpa using ha))
    rw [hφ, tali_sp_vec_true]
    exact tali_vec_inv_of (zpow_zero a) ⟨0, by ring⟩ ⟨0, by ring⟩

private theorem tali_rho_rho (s : Fin 2 → Kˣ) : uc22pwI2Rho K (uc22pwI2Rho K s) = s ^ 2 :=
  uc22pwI2Rho_sq s

private theorem tali_psi_psi [Finite K] {n l : ℕ} (hK : Nat.card K = 2 ^ n) (hl : n = 2 * l + 1)
    (t : Fin 2 → Kˣ) : uc22pwI2Rho K (uc22pwI2Rho K (t ^ 2 ^ l) ^ 2 ^ l) = t := by
  rw [← map_pow, tali_rho_rho, ← pow_mul, ← pow_mul,
    show 2 ^ l * (2 ^ l * 2) = 2 ^ n by rw [hl]; ring]
  funext i
  exact tali_pow_card hK (t i)

private theorem tali_psi_vec (l : ℕ) (a : Kˣ) (p q : ℤ) :
    uc22pwI2Rho K (![a ^ p, a ^ q] ^ 2 ^ l) =
      ![a ^ (p * 2 ^ l + q * 2 ^ l), a ^ (p * 2 ^ l - q * 2 ^ l)] := by
  have e : ∀ r : ℤ, (a ^ r) ^ 2 ^ l = a ^ (r * 2 ^ l) := fun r => by
    rw [zpow_mul, ← zpow_natCast]
    push_cast
    rfl
  funext i
  fin_cases i
  · simp [tali_rho_apply, e, zpow_add]
  · simp [tali_rho_apply, e, zpow_sub]

private theorem tali_outer_sq [Finite K] {n l : ℕ} (hK : Nat.card K = 2 ^ n)
    (hl : n = 2 * l + 1) {b b' : Bool} {ε δ ε' δ' : ℤ}
    (hc : ∀ s : Fin 2 → Kˣ, uc22pwI2Rho K (tali_sp b ε δ s) = tali_sp b' ε' δ' (uc22pwI2Rho K s))
    {φ : (Fin 2 → Kˣ) → (Fin 2 → Kˣ)}
    (hφ : ∀ t, φ t = tali_sp b ε δ (uc22pwI2Rho K (t ^ 2 ^ l))) (t : Fin 2 → Kˣ) :
    φ (φ t) = tali_sp b ε δ (tali_sp b' ε' δ' t) := by
  rw [hφ (φ t), hφ t, tali_sp_pow, hc, tali_psi_psi hK hl]

private theorem tali_outer_bad [Finite K] {n l : ℕ} (hK : Nat.card K = 2 ^ n)
    (hl : n = 2 * l + 1) {b b' : Bool} {ε δ ε' δ' : ℤ}
    (hc : ∀ s : Fin 2 → Kˣ, uc22pwI2Rho K (tali_sp b ε δ s) = tali_sp b' ε' δ' (uc22pwI2Rho K s))
    (hrot : ∀ t : Fin 2 → Kˣ, tali_sp b ε δ (tali_sp b' ε' δ' t) = t → t = 1)
    {φ : (Fin 2 → Kˣ) → (Fin 2 → Kˣ)}
    (hφ : ∀ t, φ t = tali_sp b ε δ (uc22pwI2Rho K (t ^ 2 ^ l)))
    (hfix : ∃ t₀, t₀ ≠ 1 ∧ φ t₀ = t₀) : False := by
  obtain ⟨t₀, h₀, hf⟩ := hfix
  exact h₀ (hrot t₀ (by rw [← tali_outer_sq hK hl hc hφ, hf, hf]))

private theorem tali_outer_good [Finite K] {n l : ℕ} (hK : Nat.card K = 2 ^ n)
    (hl : n = 2 * l + 1) {b b' : Bool} {ε δ ε' δ' : ℤ}
    (hc : ∀ s : Fin 2 → Kˣ, uc22pwI2Rho K (tali_sp b ε δ s) = tali_sp b' ε' δ' (uc22pwI2Rho K s))
    (hid : ∀ t : Fin 2 → Kˣ, tali_sp b ε δ (tali_sp b' ε' δ' t) = t)
    {φ : (Fin 2 → Kˣ) → (Fin 2 → Kˣ)}
    (hφ : ∀ t, φ t = tali_sp b ε δ (uc22pwI2Rho K (t ^ 2 ^ l))) (p q : ℤ)
    (hpq : ∀ a : Kˣ, φ ![a ^ p, a ^ q] = (![a ^ p, a ^ q])⁻¹)
    (hne : ∀ a : Kˣ, a ≠ 1 → a ^ p ≠ 1 ∨ a ^ q ≠ 1) :
    (∀ t, φ (φ t) = t) ∧ ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ 2 ^ n - 1 → ∃ t, orderOf t = ℓ ∧ φ t = t⁻¹ :=
  tali_refl hK (fun t => by rw [tali_outer_sq hK hl hc hφ, hid]) p q hpq hne

private theorem tali_outer [Finite K] {n l : ℕ} (hK : Nat.card K = 2 ^ n) (hl : n = 2 * l + 1)
    (b : Bool) {ε δ : ℤ} (hε : ε = 1 ∨ ε = -1) (hδ : δ = 1 ∨ δ = -1)
    {φ : (Fin 2 → Kˣ) → (Fin 2 → Kˣ)}
    (hφ : ∀ t, φ t = tali_sp b ε δ (uc22pwI2Rho K (t ^ 2 ^ l)))
    (hfix : ∃ t₀, t₀ ≠ 1 ∧ φ t₀ = t₀) :
    (∀ t, φ (φ t) = t) ∧ ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ 2 ^ n - 1 → ∃ t, orderOf t = ℓ ∧ φ t = t⁻¹ := by
  have hn : 1 ≤ n := by omega
  have hN := tali_per hK hl
  have hc : ∀ a : Kˣ, a ≠ 1 → a ^ ((2 : ℤ) ^ l) ≠ 1 := fun a ha => tali_two_pow_ne_one hK hn ha l
  have hc' : ∀ a : Kˣ, a ≠ 1 → a ^ (-((2 : ℤ) ^ l)) ≠ 1 := fun a ha => by
    rw [zpow_neg]
    exact inv_ne_one.mpr (hc a ha)
  rcases hε with rfl | rfl <;> rcases hδ with rfl | rfl <;> cases b
  · refine tali_outer_good hK hl (tali_rho_diag 1) (fun t => by simp [tali_sp_one]) hφ
      (2 ^ l) (-(1 + 2 ^ l)) (fun a => ?_) fun a ha => Or.inl (hc a ha)
    rw [hφ, tali_psi_vec, tali_sp_vec_false]
    exact tali_vec_inv_of (hN a) ⟨0, by ring⟩ ⟨1, by ring⟩
  · exact (tali_outer_bad hK hl (tali_rho_swap rfl rfl) (fun t h => tali_rot_fix hK hn
      (ε := 1) (δ := -1) (by norm_num) (by simpa [tali_sp_comp] using h)) hφ hfix).elim
  · exact (tali_outer_bad hK hl (tali_rho_refl rfl) (fun t h => tali_rot_fix hK hn
      (ε := -1) (δ := 1) (by norm_num) (by simpa [tali_sp_comp] using h)) hφ hfix).elim
  · refine tali_outer_good hK hl (tali_rho_rot rfl)
      (fun t => by simp [tali_sp_comp, tali_sp_one]) hφ (1 + 2 ^ l) (-(2 ^ l)) (fun a => ?_)
      fun a ha => Or.inr (hc' a ha)
    rw [hφ, tali_psi_vec, tali_sp_vec_true]
    exact tali_vec_inv_of (hN a) ⟨-1, by ring⟩ ⟨0, by ring⟩
  · exact (tali_outer_bad hK hl (tali_rho_refl (by norm_num)) (fun t h => tali_rot_fix hK hn
      (ε := -1) (δ := 1) (by norm_num) (by simpa [tali_sp_comp] using h)) hφ hfix).elim
  · refine tali_outer_good hK hl (tali_rho_rot (by norm_num))
      (fun t => by simp [tali_sp_comp, tali_sp_one]) hφ (1 - 2 ^ l) (2 ^ l) (fun a => ?_)
      fun a ha => Or.inr (hc a ha)
    rw [hφ, tali_psi_vec, tali_sp_vec_true]
    exact tali_vec_inv_of (hN a) ⟨-1, by ring⟩ ⟨0, by ring⟩
  · refine tali_outer_good hK hl (tali_rho_diag (-1))
      (fun t => by simp [tali_sp_comp, tali_sp_one]) hφ (1 + 2 ^ l) (2 ^ l) (fun a => ?_)
      fun a ha => Or.inr (hc a ha)
    rw [hφ, tali_psi_vec, tali_sp_vec_false]
    exact tali_vec_inv_of (hN a) ⟨-1, by ring⟩ ⟨0, by ring⟩
  · exact (tali_outer_bad hK hl (tali_rho_swap (δ' := 1) rfl (by norm_num)) (fun t h =>
      tali_rot_fix hK hn (ε := 1) (δ := -1) (by norm_num) (by simpa [tali_sp_comp] using h))
      hφ hfix).elim

theorem torusAutomizer_of_signedPerm_rho {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    (hK : Nat.card K = 2 ^ n) (hn : 3 ≤ n) (hodd : Odd n) (ε δ : ℤ) (b : Bool)
    (hε : ε = 1 ∨ ε = -1) (hδ : δ = 1 ∨ δ = -1) (k : ℕ) (φ : (Fin 2 → Kˣ) → (Fin 2 → Kˣ))
    (hφ : ∀ t, φ t = (fun s : Fin 2 → Kˣ => if b then ![s 1 ^ δ, s 0 ^ ε] else
      ![s 0 ^ ε, s 1 ^ δ]) ((⇑(uc22pwI2Rho K))^[k] t))
    (hord : ∃ j : ℕ, φ^[2 ^ j] = id) (hfix : ∃ t₀, t₀ ≠ 1 ∧ φ t₀ = t₀) :
    (∀ t, φ t = t) ∨ ((∀ t, φ (φ t) = t) ∧
      ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ 2 ^ n - 1 → ∃ t, orderOf t = ℓ ∧ φ t = t⁻¹) := by
  have hφ' : ∀ t, φ t = tali_sp b ε δ ((⇑(uc22pwI2Rho K))^[k] t) := hφ
  obtain ⟨l, hl⟩ := hodd
  have hnk : n ∣ k := tali_dvd hK (by omega) ⟨l, hl⟩ hε hδ hφ' hord
  rcases tali_rho_iter_cases hK hl hnk with h | h
  · exact tali_inner hK (by omega) b hε hδ (fun t => by rw [hφ', h]) hfix
  · exact Or.inr (tali_outer hK hl b hε hδ (fun t => by rw [hφ', h]) hfix)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
