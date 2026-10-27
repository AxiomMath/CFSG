module

public import CFSG.Quasithin.EmptyFaithful.S152Y11

public section

namespace CFSG.Quasithin

open scoped commutatorElement

variable {B : Type*} [Group B] [Finite B]

omit [Finite B] in
theorem mem_commutator_of_inverted {E R : Subgroup B} {ρ a : B} (hρ : ρ ∈ R) (ha : a ∈ E)
    {m : ℕ} (hm : Odd m) (ham : a ^ m = 1) (hinv : ρ * a * ρ⁻¹ = a⁻¹) : a ∈ ⁅E, R⁆ := by
  set a' := a ^ ((m + 1) / 2) with ha'
  have ha'E : a' ∈ E := E.pow_mem ha _
  have hinv' : ρ * a' * ρ⁻¹ = a'⁻¹ := by
    rw [ha', ← conj_pow, hinv, inv_pow]
  have h1 : ρ * a'⁻¹ * ρ⁻¹ = a' := by
    have : ρ * a'⁻¹ * ρ⁻¹ = (ρ * a' * ρ⁻¹)⁻¹ := by group
    rw [this, hinv', inv_inv]
  have h2 : a' * a' = a := by
    obtain ⟨j, hj⟩ := hm
    have : (m + 1) / 2 = j + 1 := by omega
    have hmj : a ^ m = 1 := ham
    rw [ha', this, ← pow_add, show j + 1 + (j + 1) = m + 1 by omega, pow_succ, hmj, one_mul]
  have key : ⁅a', ρ⁆ = a := by
    calc ⁅a', ρ⁆ = a' * (ρ * a'⁻¹ * ρ⁻¹) := by simp only [commutatorElement_def]; group
      _ = a := by rw [h1, h2]
  rw [← key]
  exact Subgroup.commutator_mem_commutator ha'E hρ

omit [Finite B] in
theorem eq_one_or_eq_of_mem_zpowers_Y {b x : B} (hb : b ^ 2 = 1) (hx : x ∈ Subgroup.zpowers b) :
    x = 1 ∨ x = b := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  rcases Int.even_or_odd' k with ⟨n, rfl | rfl⟩
  · left
    rw [zpow_mul, zpow_ofNat, hb, one_zpow]
  · right
    rw [zpow_add, zpow_mul, zpow_ofNat, hb, one_zpow, one_mul, zpow_one]

omit [Finite B] in
theorem eq_one_of_odd_of_two_power {x : B} (ho : Odd (orderOf x)) {k : ℕ} (hk : x ^ 2 ^ k = 1) :
    x = 1 := by
  have h1 : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
  rw [hi] at ho
  have hi0 : i = 0 := by
    by_contra hne
    exact absurd ho (Nat.not_odd_iff_even.mpr (Nat.even_pow.mpr ⟨even_two, hne⟩))
  exact orderOf_eq_one_iff.mp (by rw [hi, hi0]; rfl)

section RCases

variable {X R : Subgroup B}

inductive RCase (X R : Subgroup B) : Prop
  | eigen (hY : ⁅oTwoUpper X, R⁆ = oTwoUpper X)
      (hρ : ∃ ρ ∈ R, ρ ≠ 1 ∧ ¬ ∀ a ∈ oTwoUpper X, ρ * a * ρ⁻¹ = a⁻¹) : RCase X R
  | inv (hY : ⁅oTwoUpper X, R⁆ = oTwoUpper X) (hR : Nat.card R = 2)
      (hρ : ∀ ρ ∈ R, ρ ≠ 1 → ∀ a ∈ oTwoUpper X, ρ * a * ρ⁻¹ = a⁻¹) : RCase X R
  | three (hY : Nat.card ↥⁅oTwoUpper X, R⁆ = 3) (hR : Nat.card R = 2)
      (hρ : ∀ ρ ∈ R, ρ ≠ 1 → ∀ a ∈ ⁅oTwoUpper X, R⁆, ρ * a * ρ⁻¹ = a⁻¹) : RCase X R

theorem rCase_of_omShape (sh : OmShape X) (hRX : R ≤ X) (hR2 : IsPGroup 2 R) (hRne : R ≠ ⊥)
    (hcomm : ∀ a ∈ R, ∀ b ∈ R, a * b = b * a) : RCase X R := by
  set E := oTwoUpper X with hE
  have hEodd : ∀ x ∈ E, Odd (orderOf x) := fun x hx => by
    refine Odd.of_dvd_nat ?_ (Subgroup.orderOf_dvd_natCard E hx)
    rw [sh.card_O]; decide
  have hXN : X ≤ Subgroup.normalizer (E : Set B) := le_normalizer_oTwoUpper X
  have hYE : ⁅E, R⁆ ≤ E :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp (hRX.trans hXN)
  have hsq : ∀ ρ ∈ R, ρ * ρ = 1 := fun ρ hρ => by
    obtain ⟨k, hk⟩ := hR2 ⟨ρ, hρ⟩
    exact sh.two_elements ρ (hRX hρ) ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hsq' : ∀ ρ ∈ R, ρ ^ 2 = 1 := fun ρ hρ => by rw [pow_two]; exact hsq ρ hρ
  have hYE_of_inv : (∃ ρ ∈ R, ∀ a ∈ E, ρ * a * ρ⁻¹ = a⁻¹) → ⁅E, R⁆ = E := by
    rintro ⟨ρ, hρ, hinv⟩
    refine le_antisymm hYE fun a ha => ?_
    exact mem_commutator_of_inverted hρ ha (m := 3) (by decide) (sh.exp_O a ha) (hinv a ha)
  have heq_of_inv : ∀ ρ ∈ R, ∀ b ∈ R, (∀ a ∈ E, ρ * a * ρ⁻¹ = a⁻¹) →
      (∀ a ∈ E, b * a * b⁻¹ = a⁻¹) → ρ = b := by
    intro ρ hρ b hb hρi hbi
    have hbb : b⁻¹ = b := inv_eq_of_mul_eq_one_right (hsq b hb)
    have hc : ∀ a ∈ E, (ρ * b⁻¹) * a = a * (ρ * b⁻¹) := by
      intro a ha
      have h1 : (ρ * b⁻¹) * a * (ρ * b⁻¹)⁻¹ = a := by
        have e : (ρ * b⁻¹) * a * (ρ * b⁻¹)⁻¹ = ρ * (b⁻¹ * a * b) * ρ⁻¹ := by group
        have hba : b⁻¹ * a * b = b * a * b⁻¹ := by rw [hbb]
        rw [e, hba, hbi a ha, hρi a⁻¹ (E.inv_mem ha), inv_inv]
      calc (ρ * b⁻¹) * a = ((ρ * b⁻¹) * a * (ρ * b⁻¹)⁻¹) * (ρ * b⁻¹) := by group
        _ = a * (ρ * b⁻¹) := by rw [h1]
    have hxE : ρ * b⁻¹ ∈ E := sh.centralizer_O _ (hRX (R.mul_mem hρ (R.inv_mem hb))) hc
    have hxsq : (ρ * b⁻¹) ^ 2 ^ 1 = 1 := by
      rw [hbb, pow_one, pow_two]
      calc ρ * b * (ρ * b) = ρ * (b * ρ) * b := by group
        _ = ρ * (ρ * b) * b := by rw [hcomm b hb ρ hρ]
        _ = (ρ * ρ) * (b * b) := by group
        _ = 1 := by rw [hsq ρ hρ, hsq b hb, one_mul]
    have := eq_one_of_odd_of_two_power (hEodd _ hxE) hxsq
    rw [mul_inv_eq_one] at this
    exact this
  by_cases hYEeq : ⁅E, R⁆ = E
  · by_cases hex : ∃ ρ ∈ R, ρ ≠ 1 ∧ ¬ ∀ a ∈ E, ρ * a * ρ⁻¹ = a⁻¹
    · exact RCase.eigen hYEeq hex
    · push Not at hex
      obtain ⟨b, hb, hb1⟩ : ∃ b ∈ R, b ≠ 1 := by
        obtain ⟨⟨b, hb⟩, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hRne
        exact ⟨b, hb, fun h => hb1 (Subtype.ext h)⟩
      have hbinv := hex b hb hb1
      have hRb : R = Subgroup.zpowers b := by
        apply le_antisymm
        · intro ρ hρ
          by_cases hρ1 : ρ = 1
          · rw [hρ1]; exact Subgroup.one_mem _
          · have := heq_of_inv ρ hρ b hb (hex ρ hρ hρ1) hbinv
            rw [this]; exact Subgroup.mem_zpowers b
        · exact Subgroup.zpowers_le.mpr hb
      refine RCase.inv hYEeq ?_ fun ρ hρ hρ1 a ha => hex ρ hρ hρ1 a ha
      rw [hRb, Nat.card_zpowers, orderOf_eq_prime (hsq' b hb) hb1]
  · have hnoinv : ∀ ρ ∈ R, ¬ ∀ a ∈ E, ρ * a * ρ⁻¹ = a⁻¹ := fun ρ hρ hinv =>
      hYEeq (hYE_of_inv ⟨ρ, hρ, hinv⟩)
    obtain ⟨ρ, hρ, hρ1⟩ : ∃ ρ ∈ R, ρ ≠ 1 := by
      obtain ⟨⟨b, hb⟩, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hRne
      exact ⟨b, hb, fun h => hb1 (Subtype.ext h)⟩
    obtain ⟨e₁, he₁, e₂, he₂, he₁1, he₂1, h₁, h₂, hgen⟩ :=
      (sh.inv_or_eigen ρ (hRX hρ) (hsq ρ hρ) hρ1).resolve_left (hnoinv ρ hρ)
    have he₂Y : e₂ ∈ ⁅E, R⁆ :=
      mem_commutator_of_inverted hρ he₂ (m := 3) (by decide) (sh.exp_O e₂ he₂) h₂
    have hcz : Nat.card (Subgroup.zpowers e₂) = 3 := by
      rw [Nat.card_zpowers]
      exact orderOf_eq_prime (sh.exp_O e₂ he₂) he₂1
    have hzY : Subgroup.zpowers e₂ ≤ ⁅E, R⁆ := Subgroup.zpowers_le.mpr he₂Y
    have hYcard : Nat.card ↥⁅E, R⁆ = 3 := by
      have h3 : 3 ∣ Nat.card ↥⁅E, R⁆ := hcz ▸ Subgroup.card_dvd_of_le hzY
      have h9 : Nat.card ↥⁅E, R⁆ ∣ 3 ^ 2 := by
        have := Subgroup.card_dvd_of_le hYE
        rw [sh.card_O] at this
        simpa using this
      obtain ⟨i, hi, hci⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp h9
      have hne9 : Nat.card ↥⁅E, R⁆ ≠ 9 := fun h9' =>
        hYEeq (Subgroup.eq_of_le_of_card_ge hYE (by rw [sh.card_O, h9']))
      interval_cases i
      · rw [hci] at h3; simp at h3
      · simpa using hci
      · exact absurd (by simpa using hci) hne9
    have hRρ : R = Subgroup.zpowers ρ := by
      apply le_antisymm
      · intro ρ' hρ'
        by_cases hρ'1 : ρ' = 1
        · rw [hρ'1]; exact Subgroup.one_mem _
        · by_cases hρρ' : ρ' = ρ
          · rw [hρρ']; exact Subgroup.mem_zpowers ρ
          · exfalso
            have hpair := sh.pair ρ (hRX hρ) ρ' (hRX hρ') (hsq ρ hρ) (hsq ρ' hρ') hρ1 hρ'1
              (Ne.symm hρρ') (hcomm ρ hρ ρ' hρ') (hnoinv ρ hρ) (hnoinv ρ' hρ')
            exact hYEeq (hYE_of_inv ⟨ρ * ρ', R.mul_mem hρ hρ', fun a ha => hpair a ha⟩)
      · exact Subgroup.zpowers_le.mpr hρ
    have hRcard : Nat.card R = 2 := by
      rw [hRρ, Nat.card_zpowers, orderOf_eq_prime (hsq' ρ hρ) hρ1]
    refine RCase.three hYcard hRcard ?_
    intro ρ' hρ' hρ'1 a ha
    have hρρ' : ρ' = ρ := by
      rw [hRρ] at hρ'
      exact (eq_one_or_eq_of_mem_zpowers_Y (hsq' ρ hρ) hρ').resolve_left hρ'1
    subst hρρ'
    have hYz : ⁅E, R⁆ = Subgroup.zpowers e₂ :=
      (Subgroup.eq_of_le_of_card_ge hzY (by rw [hcz, hYcard])).symm
    rw [hYz] at ha
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    rw [← conj_zpow, h₂, inv_zpow]

end RCases

end CFSG.Quasithin
