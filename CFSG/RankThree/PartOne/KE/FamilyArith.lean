module

public import CFSG.RankThree.PartOne.KE.EndpointStatements

public section

namespace CFSG.RankThree.PartOne.KE

open CFSG.RankThree.Chevalley (exhaustionPhi)

theorem cycloVal_one (ℓ f : ℕ) : cycloVal 1 ℓ f = ((ℓ ^ f : ℕ) : ℤ) - 1 := by
  simp [cycloVal, exhaustionPhi]

theorem cycloVal_two (ℓ f : ℕ) : cycloVal 2 ℓ f = ((ℓ ^ f : ℕ) : ℤ) + 1 := by
  simp [cycloVal, exhaustionPhi]

theorem cycloVal_three (ℓ f : ℕ) :
    cycloVal 3 ℓ f = ((ℓ ^ f : ℕ) : ℤ) ^ 2 + ((ℓ ^ f : ℕ) : ℤ) + 1 := by
  simp [cycloVal, exhaustionPhi]

theorem cycloVal_four (ℓ f : ℕ) : cycloVal 4 ℓ f = ((ℓ ^ f : ℕ) : ℤ) ^ 2 + 1 := by
  simp [cycloVal, exhaustionPhi]

theorem cycloVal_six (ℓ f : ℕ) :
    cycloVal 6 ℓ f = ((ℓ ^ f : ℕ) : ℤ) ^ 2 - ((ℓ ^ f : ℕ) : ℤ) + 1 := by
  simp [cycloVal, exhaustionPhi]

theorem cycloVal_eight (ℓ f : ℕ) : cycloVal 8 ℓ f = ((ℓ ^ f : ℕ) : ℤ) ^ 4 + 1 := by
  simp [cycloVal, exhaustionPhi]

theorem cycloVal_twelve (ℓ f : ℕ) :
    cycloVal 12 ℓ f = ((ℓ ^ f : ℕ) : ℤ) ^ 4 - ((ℓ ^ f : ℕ) : ℤ) ^ 2 + 1 := by
  simp [cycloVal, exhaustionPhi]

theorem F4_prime_dvd_cyclotomic {p ℓ f : ℕ} (hp : p.Prime)
    (h : (p : ℤ) ∣ (((ℓ ^ f : ℕ) : ℤ) ^ 2 - 1) * (((ℓ ^ f : ℕ) : ℤ) ^ 6 - 1) *
      (((ℓ ^ f : ℕ) : ℤ) ^ 8 - 1) * (((ℓ ^ f : ℕ) : ℤ) ^ 12 - 1)) :
    (p : ℤ) ∣ cycloVal 1 ℓ f ∨ (p : ℤ) ∣ cycloVal 2 ℓ f ∨ (p : ℤ) ∣ cycloVal 3 ℓ f ∨
      (p : ℤ) ∣ cycloVal 4 ℓ f ∨ (p : ℤ) ∣ cycloVal 6 ℓ f ∨ (p : ℤ) ∣ cycloVal 8 ℓ f ∨
      (p : ℤ) ∣ cycloVal 12 ℓ f := by
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  set Q : ℤ := ((ℓ ^ f : ℕ) : ℤ) with hQ
  have hfac : (Q ^ 2 - 1) * (Q ^ 6 - 1) * (Q ^ 8 - 1) * (Q ^ 12 - 1) =
      (cycloVal 1 ℓ f) ^ 4 * (cycloVal 2 ℓ f) ^ 4 * (cycloVal 3 ℓ f) ^ 2 *
        (cycloVal 4 ℓ f) ^ 2 * (cycloVal 6 ℓ f) ^ 2 * cycloVal 8 ℓ f * cycloVal 12 ℓ f := by
    rw [cycloVal_one, cycloVal_two, cycloVal_three, cycloVal_four, cycloVal_six, cycloVal_eight,
      cycloVal_twelve]
    ring
  rw [hfac] at h
  rcases hpz.dvd_or_dvd h with h | h
  · rcases hpz.dvd_or_dvd h with h | h
    · rcases hpz.dvd_or_dvd h with h | h
      · rcases hpz.dvd_or_dvd h with h | h
        · rcases hpz.dvd_or_dvd h with h | h
          · rcases hpz.dvd_or_dvd h with h | h
            · exact Or.inl (hpz.dvd_of_dvd_pow h)
            · exact Or.inr (Or.inl (hpz.dvd_of_dvd_pow h))
          · exact Or.inr (Or.inr (Or.inl (hpz.dvd_of_dvd_pow h)))
        · exact Or.inr (Or.inr (Or.inr (Or.inl (hpz.dvd_of_dvd_pow h))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hpz.dvd_of_dvd_pow h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))

theorem cycloVal_five (ℓ f : ℕ) :
    cycloVal 5 ℓ f = ∑ j ∈ Finset.range 5, (1 * ((ℓ ^ f : ℕ) : ℤ)) ^ j := by
  simp only [cycloVal, exhaustionPhi, Finset.sum_range_succ, Finset.sum_range_zero]
  simp
  ring

theorem cycloVal_ten (ℓ f : ℕ) :
    cycloVal 10 ℓ f = ∑ j ∈ Finset.range 5, ((-1) * ((ℓ ^ f : ℕ) : ℤ)) ^ j := by
  simp only [cycloVal, exhaustionPhi, Finset.sum_range_succ, Finset.sum_range_zero]
  simp
  ring

theorem cycloVal_seven (ℓ f : ℕ) :
    cycloVal 7 ℓ f = ∑ j ∈ Finset.range 7, (1 * ((ℓ ^ f : ℕ) : ℤ)) ^ j := by
  simp only [cycloVal, exhaustionPhi, Finset.sum_range_succ, Finset.sum_range_zero]
  simp
  ring

theorem cycloVal_fourteen (ℓ f : ℕ) :
    cycloVal 14 ℓ f = ∑ j ∈ Finset.range 7, ((-1) * ((ℓ ^ f : ℕ) : ℤ)) ^ j := by
  simp only [cycloVal, exhaustionPhi, Finset.sum_range_succ, Finset.sum_range_zero]
  simp
  ring

theorem not_dvd_cycloVal_one_two_of_not_dvd_sq {p ℓ f : ℕ} (hq : 1 ≤ ℓ ^ f)
    (h : ¬ p ∣ (ℓ ^ f) ^ 2 - 1) :
    ¬ (p : ℤ) ∣ cycloVal 1 ℓ f ∧ ¬ (p : ℤ) ∣ cycloVal 2 ℓ f := by
  have hsq : (((ℓ ^ f) ^ 2 - 1 : ℕ) : ℤ) =
      (((ℓ ^ f : ℕ) : ℤ) - 1) * (((ℓ ^ f : ℕ) : ℤ) + 1) := by
    have h1 : 1 ≤ (ℓ ^ f) ^ 2 := Nat.one_le_pow _ _ hq
    push_cast [Nat.cast_sub h1]
    ring
  have hnat : ¬ (p : ℤ) ∣ (((ℓ ^ f) ^ 2 - 1 : ℕ) : ℤ) := fun hd =>
    h (Int.natCast_dvd_natCast.mp hd)
  rw [hsq] at hnat
  rw [cycloVal_one, cycloVal_two]
  exact ⟨fun hd => hnat (hd.mul_right _), fun hd => hnat (hd.mul_left _)⟩

theorem not_dvd_cycloVal_one_of {p ℓ f : ℕ} (hq : 1 ≤ ℓ ^ f) (h : ¬ p ∣ ℓ ^ f - 1) :
    ¬ (p : ℤ) ∣ cycloVal 1 ℓ f := by
  rw [cycloVal_one]
  intro hd
  apply h
  have h1 : (p : ℤ) ∣ ((ℓ ^ f - 1 : ℕ) : ℤ) := by
    rw [Nat.cast_sub hq]
    simpa using hd
  exact Int.natCast_dvd_natCast.mp h1

theorem not_dvd_cycloVal_two_of {p ℓ f : ℕ} (h : ¬ p ∣ ℓ ^ f + 1) :
    ¬ (p : ℤ) ∣ cycloVal 2 ℓ f := by
  rw [cycloVal_two]
  intro hd
  apply h
  exact_mod_cast hd

@[expose] def SmallPrimeGuard (p ℓ f : ℕ) : Prop :=
  ∀ r : ℕ, r = 5 ∨ r = 7 → ∀ δ : ℤ, δ = 1 ∨ δ = -1 →
    (p : ℤ) ∣ ∑ j ∈ Finset.range r, (δ * ((ℓ ^ f : ℕ) : ℤ)) ^ j → p ≤ r →
      p = r ∧ ((ℓ ^ f : ℕ) : ℤ) ≡ δ [ZMOD r]

theorem five_lt_of_dvd_five {p ℓ f : ℕ} (hguard : SmallPrimeGuard p ℓ f)
    (h1 : ¬ (p : ℤ) ∣ cycloVal 1 ℓ f) (hd : (p : ℤ) ∣ cycloVal 5 ℓ f) : 5 < p := by
  by_contra hle
  push Not at hle
  rw [cycloVal_five] at hd
  obtain ⟨hp5, hmod⟩ := hguard 5 (Or.inl rfl) 1 (Or.inl rfl) hd hle
  apply h1
  rw [cycloVal_one]
  have h5 : ((5 : ℕ) : ℤ) ∣ 1 - ((ℓ ^ f : ℕ) : ℤ) := Int.modEq_iff_dvd.mp hmod
  rw [← hp5] at h5
  have h6 := dvd_neg.mpr h5
  rwa [neg_sub] at h6

theorem five_lt_of_dvd_ten {p ℓ f : ℕ} (hguard : SmallPrimeGuard p ℓ f)
    (h2 : ¬ (p : ℤ) ∣ cycloVal 2 ℓ f) (hd : (p : ℤ) ∣ cycloVal 10 ℓ f) : 5 < p := by
  by_contra hle
  push Not at hle
  rw [cycloVal_ten] at hd
  obtain ⟨hp5, hmod⟩ := hguard 5 (Or.inl rfl) (-1) (Or.inr rfl) hd hle
  apply h2
  rw [cycloVal_two]
  have h5 : ((5 : ℕ) : ℤ) ∣ -1 - ((ℓ ^ f : ℕ) : ℤ) := Int.modEq_iff_dvd.mp hmod
  rw [← hp5] at h5
  have h6 := dvd_neg.mpr h5
  rwa [neg_sub, sub_neg_eq_add] at h6

theorem seven_lt_of_dvd_seven {p ℓ f : ℕ} (hguard : SmallPrimeGuard p ℓ f)
    (h1 : ¬ (p : ℤ) ∣ cycloVal 1 ℓ f) (hd : (p : ℤ) ∣ cycloVal 7 ℓ f) : 7 < p := by
  by_contra hle
  push Not at hle
  rw [cycloVal_seven] at hd
  obtain ⟨hp7, hmod⟩ := hguard 7 (Or.inr rfl) 1 (Or.inl rfl) hd hle
  apply h1
  rw [cycloVal_one]
  have h5 : ((7 : ℕ) : ℤ) ∣ 1 - ((ℓ ^ f : ℕ) : ℤ) := Int.modEq_iff_dvd.mp hmod
  rw [← hp7] at h5
  have h6 := dvd_neg.mpr h5
  rwa [neg_sub] at h6

theorem seven_lt_of_dvd_fourteen {p ℓ f : ℕ} (hguard : SmallPrimeGuard p ℓ f)
    (h2 : ¬ (p : ℤ) ∣ cycloVal 2 ℓ f) (hd : (p : ℤ) ∣ cycloVal 14 ℓ f) : 7 < p := by
  by_contra hle
  push Not at hle
  rw [cycloVal_fourteen] at hd
  obtain ⟨hp7, hmod⟩ := hguard 7 (Or.inr rfl) (-1) (Or.inr rfl) hd hle
  apply h2
  rw [cycloVal_two]
  have h5 : ((7 : ℕ) : ℤ) ∣ -1 - ((ℓ ^ f : ℕ) : ℤ) := Int.modEq_iff_dvd.mp hmod
  rw [← hp7] at h5
  have h6 := dvd_neg.mpr h5
  rwa [neg_sub, sub_neg_eq_add] at h6

end CFSG.RankThree.PartOne.KE
