module

public import CFSG.Walter.Ree.Hopkins.Lemma22
public import CFSG.Walter.Ree.Hopkins.Lemma25
public import CFSG.Walter.Ree.Thompson3.ThompsonAut

public section

namespace CFSG.Walter.Ree.Hopkins

open CFSG.Walter.Ree.T2

variable {k : Type} [Field k] [CharP k 3] [Fintype k] {σ : k ≃+* k}

theorem d_unique {m a s : ℕ} (hk : Fintype.card k = 3 ^ m) (hm : Odd m) (ha : Even a)
    (haσ : ∀ x : k, (σ x * x) ^ a = x ^ 2) (hs : Odd s) (hsσ : ∀ x : k, (σ x * x ^ 2) ^ s = x)
    (ha3 : a % 3 = 2) (haq : a + 3 < Fintype.card k) {d₁ d₂ : k} {G₁ G₂ : Type} [Group G₁]
    [Finite G₁] [Group G₂] [Finite G₂] {R₁ : RType G₁ k σ d₁} {R₂ : RType G₂ k σ d₂}
    {c : k → k → k → k} (h₁ : Eq211 R₁ a c) (h₂ : Eq211 R₂ a c) : d₁ = d₂ := by
  obtain ⟨z, y, u, hE, hzyu, hD, hne⟩ := exists_triple hk hm ha haσ hs hsσ ha3 haq
  have e₁ := h₁ z y u hE hzyu hD
  have e₂ := h₂ z y u hE hzyu hD
  have hc : coef211 σ a z y u ≠ 0 := by
    rw [coef211_eq a z y u hD]; exact div_ne_zero hne hD
  exact mul_left_cancel₀ hc (e₁.trans e₂.symm)

theorem exists_a_mod_three {N a : ℕ} (hk : Fintype.card k = 3 ^ N) (hN : Odd N) (hN3 : 3 ≤ N)
    (ha : Even a) (haσ : ∀ x : k, (σ x * x) ^ a = x ^ 2) :
    ∃ a' : ℕ, Even a' ∧ (∀ x : k, (σ x * x) ^ a' = x ^ 2) ∧ a' % 3 = 2 ∧
      a' + 3 < Fintype.card k := by
  classical
  obtain ⟨m, hmN, hm⟩ := Bombieri.exists_eq_frob_pow hk σ
  have hσ1 : ∀ (x : k) (e : ℕ), (σ x * x) ^ e = x ^ ((3 ^ m + 1) * e) := fun x e => by
    rw [hm, ← pow_succ, ← pow_mul]
  set q := Fintype.card k with hqdef
  have hq27 : 27 ≤ q := by
    rw [hk]; calc 27 = 3 ^ 3 := by norm_num
      _ ≤ 3 ^ N := Nat.pow_le_pow_right (by norm_num) hN3
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := kˣ)
  have hord : orderOf g = q - 1 := by rw [hg, Nat.card_eq_fintype_card, Fintype.card_units]
  have hcong : (3 ^ m + 1) * a ≡ 2 [MOD q - 1] := by
    rw [← hord, ← pow_eq_pow_iff_modEq]
    apply Units.ext
    have := haσ (g : k)
    rw [hσ1] at this
    push_cast
    exact this
  set a' := a % (q - 1) with ha'def
  have hcong' : (3 ^ m + 1) * a' ≡ 2 [MOD q - 1] :=
    ((Nat.mod_modEq a (q - 1)).mul_left _).trans hcong
  have ha'q : a' < q - 1 := Nat.mod_lt _ (by omega)
  have ha'e : Even a' := by
    have hq1 : Even (q - 1) := by
      have : Odd q := by rw [hk]; exact Odd.pow (by decide)
      obtain ⟨c, hc⟩ := this
      exact ⟨c, by omega⟩
    have e := Nat.div_add_mod a (q - 1)
    rw [← e] at ha
    exact (Nat.even_add.1 ha).1 (hq1.mul_right _)
  have ha'0 : 0 < a' := by
    rcases Nat.eq_zero_or_pos a' with h0 | h0
    · rw [h0, mul_zero] at hcong'
      have : 2 % (q - 1) = 2 := Nat.mod_eq_of_lt (by omega)
      have h0' : 0 % (q - 1) = 2 % (q - 1) := hcong'
      rw [Nat.zero_mod, this] at h0'
      omega
    · exact h0
  obtain ⟨b, hb⟩ := (Nat.modEq_iff_dvd.1 hcong'.symm)
  have hq1 : ((q - 1 : ℕ) : ℤ) = (3 : ℤ) ^ N - 1 := by
    rw [Nat.cast_sub (by omega), hk]; push_cast; ring
  have hb' : ((3 : ℤ) ^ m + 1) * a' = 2 + ((3 : ℤ) ^ N - 1) * b := by
    rw [← hq1, ← hb]; push_cast; ring
  have h3 := lemma22_i hmN hb' hN (by exact_mod_cast ha'e) (by exact_mod_cast ha'0)
    (by rw [← hq1]; exact_mod_cast ha'q)
  have ha'3 : a' % 3 = 2 := by omega
  have hq3 : q % 3 = 0 := by
    rw [hk]; obtain ⟨N', rfl⟩ := Nat.exists_eq_add_of_le' (show 1 ≤ N by omega)
    rw [pow_succ]; simp
  refine ⟨a', ha'e, fun x => ?_, ha'3, by omega⟩
  rw [hσ1]
  exact T2.pow_eq_pow_of_modEq' (Nat.one_le_iff_ne_zero.mpr (by positivity)) (by norm_num)
    hcong' x

theorem d_unique_of_eq211
    (h211 : ∀ a : ℕ, Even a → (∀ x : k, (σ x * x) ^ a = x ^ 2) → a < Fintype.card k - 1 →
      ∃ c : k → k → k → k, ∀ (d : k) (G : Type) [Group G] [Finite G] (R : RType G k σ d),
        Eq211 R a c)
    {d₁ d₂ : k} {G₁ G₂ : Type} [Group G₁] [Finite G₁] [Group G₂] [Finite G₂]
    (R₁ : RType G₁ k σ d₁) (R₂ : RType G₂ k σ d₂) : d₁ = d₂ := by
  obtain ⟨n, hn, hk⟩ := R₁.card_k_eq
  obtain ⟨a, ha, haσ⟩ := R₁.exists_a'
  obtain ⟨s, hs, hsσ⟩ := R₁.exists_s hk
  obtain ⟨a', ha', ha'σ, ha'3, ha'q⟩ :=
    exists_a_mod_three hk (odd_two_mul_add_one n) (by omega) ha haσ
  obtain ⟨c, hc⟩ := h211 a' ha' ha'σ (by omega)
  exact d_unique hk (odd_two_mul_add_one n) ha' ha'σ hs hsσ ha'3 ha'q (hc d₁ G₁ R₁) (hc d₂ G₂ R₂)

theorem apply_eq_of_sq {n : ℕ} (hn : 1 ≤ n) (hk : Fintype.card k = 3 ^ (2 * n + 1))
    (hσ : ∀ x, σ (σ x) = x ^ 3) : ∀ x, σ x = x ^ 3 ^ (n + 1) := by
  obtain ⟨b, hb, hbσ⟩ := Bombieri.exists_eq_frob_pow hk σ
  have h2b : ∀ x : k, x ^ 3 ^ (b * 2 % (2 * n + 1)) = x ^ 3 := by
    intro x
    rw [← Bombieri.pow_three_pow_mod hk, ← Bombieri.pow_apply_of_eq_frob_pow hbσ, pow_two,
      RingAut.mul_apply, hσ]
  have hb1 := Bombieri.eq_one_of_pow_three_pow_eq hk (by omega) (Nat.mod_lt _ (by omega)) h2b
  have hbn : b = n + 1 := by
    have e := Nat.div_add_mod (b * 2) (2 * n + 1)
    rw [hb1] at e
    have hq : b * 2 / (2 * n + 1) < 2 := by
      rw [Nat.div_lt_iff_lt_mul (by omega)]; omega
    generalize b * 2 / (2 * n + 1) = Q at e hq
    interval_cases Q <;> omega
  rwa [hbn] at hbσ

theorem exists_a_of_sq {n : ℕ} (hn : 1 ≤ n) (hk : Fintype.card k = 3 ^ (2 * n + 1))
    (hσ : ∀ x, σ (σ x) = x ^ 3) : ∃ a : ℕ, Even a ∧ (∀ x : k, (σ x * x) ^ a = x ^ 2) ∧
      a % 3 = 2 ∧ a + 3 < Fintype.card k := by
  have hbσ := apply_eq_of_sq hn hk hσ
  refine ⟨3 ^ (n + 1) - 1, ?_, ?_, ?_, ?_⟩
  · have : Odd (3 ^ (n + 1)) := Odd.pow (by decide)
    obtain ⟨c, hc⟩ := this
    exact ⟨c, by omega⟩
  · intro x
    rcases eq_or_ne x 0 with rfl | hx
    · have h9 : 1 < 3 ^ (n + 1) := Nat.one_lt_pow (by omega) (by norm_num)
      have hne : 3 ^ (n + 1) - 1 ≠ 0 := by omega
      rw [map_zero, zero_mul, zero_pow hne, zero_pow two_ne_zero]
    · rw [hbσ, ← pow_succ, ← pow_mul]
      have e : (3 ^ (n + 1) + 1) * (3 ^ (n + 1) - 1) + 1 = 3 * 3 ^ (2 * n + 1) := by
        have h1 : 1 ≤ 3 ^ (n + 1) := Nat.one_le_pow _ _ (by norm_num)
        have : 3 * 3 ^ (2 * n + 1) = 3 ^ (n + 1) * 3 ^ (n + 1) := by
          rw [← pow_succ', ← pow_add]; congr 1; omega
        rw [this]
        zify [h1]
        ring
      have hx3 : x ^ (3 * 3 ^ (2 * n + 1)) = x ^ 3 := by
        rw [pow_mul, ← hk, FiniteField.pow_card]
      have : x ^ ((3 ^ (n + 1) + 1) * (3 ^ (n + 1) - 1)) * x = x ^ 2 * x := by
        rw [← pow_succ, e, hx3]; ring
      exact mul_right_cancel₀ hx this
  · have : 3 ^ (n + 1) % 3 = 0 := by rw [pow_succ]; simp
    have h1 : 1 ≤ 3 ^ (n + 1) := Nat.one_le_pow _ _ (by norm_num)
    omega
  · rw [hk]
    have h1 : 3 ^ (n + 1) + 2 < 3 ^ (2 * n + 1) := by
      have h2 : 3 ^ (2 * n + 1) = 3 ^ (n + 1) * 3 ^ n := by rw [← pow_add]; congr 1; omega
      have h3 : 3 ≤ 3 ^ n := by
        calc 3 = 3 ^ 1 := by norm_num
          _ ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) hn
      have h4 : 9 ≤ 3 ^ (n + 1) := by
        calc 9 = 3 ^ 2 := by norm_num
          _ ≤ 3 ^ (n + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [h2]; nlinarith
    have h0 : 1 ≤ 3 ^ n := Nat.one_le_pow _ _ (by norm_num)
    have h5 : 1 ≤ 3 ^ (n + 1) := Nat.one_le_pow _ _ (by norm_num)
    omega

theorem d_unique_of_sq {n s : ℕ} (hn : 1 ≤ n) (hk : Fintype.card k = 3 ^ (2 * n + 1))
    (hσ : ∀ x, σ (σ x) = x ^ 3) (hs : Odd s) (hsσ : ∀ x : k, (σ x * x ^ 2) ^ s = x)
    (h211 : ∀ a : ℕ, Even a → (∀ x : k, (σ x * x) ^ a = x ^ 2) → a < Fintype.card k - 1 →
      ∃ c : k → k → k → k, ∀ (d : k) (G : Type) [Group G] [Finite G] (R : RType G k σ d),
        Eq211 R a c)
    {d₁ d₂ : k} {G₁ G₂ : Type} [Group G₁] [Finite G₁] [Group G₂] [Finite G₂]
    (R₁ : RType G₁ k σ d₁) (R₂ : RType G₂ k σ d₂) : d₁ = d₂ := by
  obtain ⟨a, ha, haσ, ha3, haq⟩ := exists_a_of_sq hn hk hσ
  obtain ⟨c, hc⟩ := h211 a ha haσ (by omega)
  exact d_unique hk (odd_two_mul_add_one n) ha haσ hs hsσ ha3 haq (hc d₁ G₁ R₁) (hc d₂ G₂ R₂)

end CFSG.Walter.Ree.Hopkins
