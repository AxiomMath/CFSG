module

public import CFSG.Quasithin.EmptyFaithful.S146zMAut
public import CFSG.Quasithin.Background.F6SolvableQuotient

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.SectionRank.Ccomm

variable {D : Type*} [Group D] [Finite D]

omit [Finite D] in
theorem mem_of_pow_mem_of_coprime {C : Subgroup D} {x : D} {k : ℕ}
    (hk : Nat.Coprime (orderOf x) k) (h : x ^ k ∈ C) : x ∈ C := by
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.mpr hk
  have hx : x = (x ^ k) ^ b := by
    calc x = x ^ (a * (orderOf x : ℤ) + b * (k : ℤ)) := by rw [hab, zpow_one]
      _ = (x ^ k) ^ b := by
        rw [zpow_add, mul_comm a, zpow_mul, zpow_natCast, pow_orderOf_eq_one, one_zpow,
          one_mul, mul_comm b, zpow_mul, zpow_natCast]
  rw [hx]
  exact C.zpow_mem h b

theorem prime_dvd_forty_eight {ℓ : ℕ} (hℓ : ℓ.Prime) (h : ℓ ∣ 48) : ℓ = 2 ∨ ℓ = 3 := by
  have h48 : ℓ ∣ 2 ^ 4 * 3 := h.trans (by norm_num)
  rcases (Nat.Prime.dvd_mul hℓ).1 h48 with h2 | h3
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).1 (hℓ.dvd_of_dvd_pow h2))
  · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_three).1 h3)

theorem prime_dvd_four_eighty {ℓ : ℕ} (hℓ : ℓ.Prime) (h : ℓ ∣ 480) : ℓ = 2 ∨ ℓ = 3 ∨ ℓ = 5 := by
  have h480 : ℓ ∣ (2 ^ 5 * 3) * 5 := h.trans (by norm_num)
  rcases (Nat.Prime.dvd_mul hℓ).1 h480 with h1 | h5
  · rcases (Nat.Prime.dvd_mul hℓ).1 h1 with h2 | h3
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).1 (hℓ.dvd_of_dvd_pow h2))
    · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_three).1 h3))
  · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hℓ (by norm_num)).1 h5))

theorem prime_mem_allowed_of_solvable_quotient {Ĝ : Type*} [Group Ĝ] [Finite Ĝ] (φ : Ĝ →* D)
    (hφ : Function.Surjective φ) (hsolv : Group.IsSolvable D) (hO2 : CFSG.Open.pCore 2 D = ⊥)
    (hr3 : CFSG.Open.pRank 3 (⊤ : Subgroup Ĝ) ≤ 2) (hr5 : CFSG.Open.pRank 5 (⊤ : Subgroup Ĝ) ≤ 2)
    {p : ℕ} (hp : p = 3 ∨ p = 5)
    (hmax : ∀ q : ℕ, q.Prime → q ≠ 2 → CFSG.Open.pCore q D ≠ ⊥ → q ≤ p) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hdvd : ℓ ∣ Nat.card D) : ℓ = 2 ∨ ℓ = 3 ∨ (p = 5 ∧ ℓ = 5) := by
  classical
  by_contra hno
  push Not at hno
  obtain ⟨h2, h3, h5⟩ := hno
  have : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' ℓ hdvd
  have hcop : ∀ {k : ℕ}, (∀ q : ℕ, q.Prime → q ∣ k → q = 2 ∨ q = 3 ∨ (p = 5 ∧ q = 5)) →
      Nat.Coprime (orderOf x) k := by
    intro k hk
    rw [hx]
    refine (Nat.Prime.coprime_iff_not_dvd hℓ).mpr fun hdk => ?_
    rcases hk ℓ hℓ hdk with h | h | h
    · exact h2 h
    · exact h3 h
    · exact h5 h.1 h.2
  have hbot : ∀ {N : Subgroup D}, N = ⊥ → x ∈ Subgroup.centralizer (N : Set D) := by
    intro N hN
    subst hN
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    rw [SetLike.mem_coe, Subgroup.mem_bot] at hg
    subst hg
    simp
  have hcent : ∀ q : ℕ, q.Prime → x ∈ Subgroup.centralizer (CFSG.Open.pCore q D : Set D) := by
    intro q hq
    by_cases hq2 : q = 2
    · rw [hq2]
      exact hbot hO2
    by_cases hqb : CFSG.Open.pCore q D = ⊥
    · exact hbot hqb
    have hqp : q ≤ p := hmax q hq hq2 hqb
    have hq35 : q = 3 ∨ (q = 5 ∧ p = 5) := by
      have hq3 : 3 ≤ q := by
        rcases hq.eq_two_or_odd' with h | h
        · exact absurd h hq2
        · have := hq.two_le
          rcases h with ⟨m, hm⟩
          omega
      rcases hp with rfl | rfl
      · exact Or.inl (by omega)
      · have h5' : q ≠ 4 := fun h => by
          rw [h] at hq
          exact absurd hq (by norm_num)
        rcases (by omega : q = 3 ∨ q = 4 ∨ q = 5) with h | h | h
        · exact Or.inl h
        · exact absurd h h5'
        · exact Or.inr ⟨h, rfl⟩
    rcases hq35 with rfl | ⟨rfl, rfl⟩
    · have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      obtain ⟨k, -, hk, hkc⟩ := exists_pow_mem_centralizer_pCore (p := 3) (by norm_num) φ hφ hr3
      refine mem_of_pow_mem_of_coprime (hcop fun r hr hrk => ?_) (hkc x)
      rcases hk r hr hrk with h | h
      · exact Or.inr (Or.inl h)
      · rw [card_GL_two_three] at h
        rcases prime_dvd_forty_eight hr h with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
    · have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
      obtain ⟨k, -, hk, hkc⟩ := exists_pow_mem_centralizer_pCore (p := 5) (by norm_num) φ hφ hr5
      refine mem_of_pow_mem_of_coprime (hcop fun r hr hrk => ?_) (hkc x)
      rcases hk r hr hrk with h | h
      · exact Or.inr (Or.inr ⟨rfl, h⟩)
      · rw [card_GL_two_five] at h
        rcases prime_dvd_four_eighty hr h with h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr ⟨rfl, h⟩)
  have hxC : x ∈ Subgroup.centralizer (CFSG.fittingSubgroup D : Set D) := by
    have h1 : Subgroup.zpowers x ≤ Subgroup.centralizer (CFSG.fittingSubgroup D : Set D) :=
      subgroup_le_centralizer_fitting_of_le_centralizer_pCores fun q => by
        exact Subgroup.zpowers_le.mpr (hcent q.1.1 (Nat.prime_of_mem_primeFactors q.1.2))
    exact h1 (Subgroup.mem_zpowers x)
  have hxF : x ∈ CFSG.fittingSubgroup D :=
    centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hsolv hxC
  have hFn : (CFSG.fittingSubgroup D).Normal := CFSG.fittingSubgroup_normal
  have hFnil : Group.IsNilpotent ↥(CFSG.fittingSubgroup D) := CFSG.fittingSubgroup_nilpotent
  have hxl : x ∈ pCoreOf ℓ (CFSG.fittingSubgroup D) := by
    refine F6.mem_pCoreOf_of_isNilpotent hxF (e := 1) ?_
    rw [pow_one, ← hx]
    exact pow_orderOf_eq_one x
  have hle : pCoreOf ℓ (CFSG.fittingSubgroup D) ≤ CFSG.Open.pCore ℓ D := by
    refine le_pCore ℓ ?_ (pCoreOf_isPGroup ℓ (CFSG.fittingSubgroup D))
    rw [← Subgroup.normalizer_eq_top_iff, ← top_le_iff]
    exact (Subgroup.normalizer_eq_top_iff.mpr hFn).ge.trans
      (normalizer_le_normalizer_pCoreOf ℓ (CFSG.fittingSubgroup D))
  have hne : CFSG.Open.pCore ℓ D ≠ ⊥ := by
    intro hbot
    have := hle hxl
    rw [hbot, Subgroup.mem_bot] at this
    have h1 : orderOf x = 1 := by rw [this]; exact orderOf_one
    rw [hx] at h1
    exact hℓ.one_lt.ne' h1
  have hℓp : ℓ ≤ p := hmax ℓ hℓ h2 hne
  have hℓ3 : 3 ≤ ℓ := by
    rcases hℓ.eq_two_or_odd' with h | ⟨m, hm⟩
    · exact absurd h h2
    · have := hℓ.two_le
      omega
  rcases hp with hp | hp
  · omega
  · have : ℓ = 3 ∨ ℓ = 4 ∨ ℓ = 5 := by omega
    rcases this with h | h | h
    · exact h3 h
    · rw [h] at hℓ
      exact absurd hℓ (by norm_num)
    · exact h5 hp h

end CFSG.Quasithin
