module

public import CFSG.Quasithin.Background.A318PL3Core

public section

namespace CFSG.Quasithin

namespace A318P

section Skeleton

variable {X : Type*} [Group X] {Y : Type} [Group Y] {C : Type} [Group C]

theorem three_elements_mem_of_frame {H₁ : Subgroup X} (F : L3Frame Y C) (Φ : X →* MulAut Y)
    (hΦ₁ : ∀ h ∈ H₁, Φ h ∈ F.D) (hΦ₂ : ∀ d ∈ F.D, ∃ h ∈ H₁, Φ h = d)
    (hker : ∀ g, Φ g = 1 → g ∈ H₁)
    (hfield : ∀ (g : X) (c : C), orderOf c = 3 → Φ g = F.fld c → g ∉ H₁ → False) :
    ∀ g : X, (∃ k : ℕ, orderOf g = 3 ^ k) → g ∈ H₁ := by
  classical
  rintro g ⟨k, hk⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨i, hi⟩ : ∃ i : ℕ, orderOf (Φ g) = 3 ^ i := by
    have hd : orderOf (Φ g) ∣ 3 ^ k := hk ▸ orderOf_map_dvd Φ g
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hd
    exact ⟨i, hi⟩
  obtain ⟨d, hd, c, hdc⟩ := F.three_mem (Φ g) i hi
  have hαE : Φ g ∈ F.E := ⟨d, hd, c, hdc⟩
  set β : ↥F.E := ⟨Φ g, hαE⟩ with hβ
  have hρβ : F.rho β = c := F.rho_eq hd hdc
  have hc3 : c ^ 3 ^ k = 1 := by
    rw [← hρβ, ← map_pow]
    have : β ^ 3 ^ k = 1 := by
      apply Subtype.ext
      change (Φ g) ^ 3 ^ k = 1
      rw [← map_pow, ← hk, pow_orderOf_eq_one, map_one]
    rw [this, map_one]
  obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one hc3)
  by_cases hb0 : b = 0
  ·
    rw [hb0, pow_zero, orderOf_eq_one_iff] at hb
    rw [hb, map_one, mul_one] at hdc
    obtain ⟨h, hh, hΦh⟩ := hΦ₂ d hd
    have h1 : h⁻¹ * g ∈ H₁ := hker _ (by
      rw [map_mul, map_inv, hΦh, ← hdc]
      exact inv_mul_cancel _)
    have h2 := H₁.mul_mem hh h1
    simpa using h2
  · exfalso
    obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
    set g' : X := g ^ 3 ^ b' with hg'
    have hΦg' : Φ g' = (Φ g) ^ 3 ^ b' := by rw [hg', map_pow]
    have hβ' : Φ g' ∈ F.E := by
      rw [hΦg']
      exact pow_mem hαE _
    set β' : ↥F.E := ⟨Φ g', hβ'⟩ with hβ'def
    have hβpow : β' = β ^ 3 ^ b' := by
      apply Subtype.ext
      exact hΦg'
    have hρβ' : F.rho β' = c ^ 3 ^ b' := by
      rw [hβpow, map_pow, hρβ]
    have hc'ord : orderOf (c ^ 3 ^ b') = 3 := by
      have hne : (3 : ℕ) ^ b' ≠ 0 := pow_ne_zero _ (by norm_num)
      rw [orderOf_pow_of_dvd hne (hb ▸ pow_dvd_pow 3 (Nat.le_succ b')), hb, pow_succ,
        Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hne)]
    obtain ⟨d', hd', hd'c⟩ := F.rhoFun_spec β'
    have hd'c' : Φ g' = d' * F.fld (c ^ 3 ^ b') := by
      have := hd'c
      rw [← F.rho_apply, hρβ'] at this
      exact this
    obtain ⟨h, hh, hΦh⟩ := hΦ₂ d'⁻¹ (F.D.inv_mem hd')
    have hΦ1 : Φ (h * g') = F.fld (c ^ 3 ^ b') := by
      rw [map_mul, hΦh, hd'c']
      group
    have hg1 : h * g' ∉ H₁ := by
      intro hmem
      have := hΦ₁ _ hmem
      rw [hΦ1] at this
      have h1 := F.fld_inter _ this
      rw [h1, orderOf_one] at hc'ord
      omega
    exact hfield (h * g') (c ^ 3 ^ b') hc'ord hΦ1 hg1

end Skeleton

end A318P

end CFSG.Quasithin
