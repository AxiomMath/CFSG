module

public import CFSG.RankThree.PartTwo.Sec21.FF84Defs

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84

open CFSG CFSG.RankThree.PartTwo.Sec21

variable {H : Type} [Group H]

structure Red3 (P P₁ P₂ : Subgroup H) : Prop where
  sylow : IsSylowOf 3 P ⊤
  card : Nat.card P = 9
  c₁ : Nat.card P₁ = 3
  c₂ : Nat.card P₂ = 3
  sup : P₁ ⊔ P₂ = P
  inf : P₁ ⊓ P₂ = ⊥
  sc₁ : IsStronglyClosedIn P (P₁ : Set H)
  sc₂ : IsStronglyClosedIn P (P₂ : Set H)

theorem exists_mul_of_mem_sup_of_commute {X : Type*} [Group X] {A B : Subgroup X}
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {x : X} (hx : x ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  let P : Subgroup X :=
    { carrier := {x | ∃ a ∈ A, ∃ b ∈ B, x = a * b}
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        refine ⟨a * a', mul_mem ha ha', b * b', mul_mem hb hb', ?_⟩
        calc a * b * (a' * b') = a * (b * a') * b' := by group
          _ = a * (a' * b) * b' := by rw [hAB a' ha' b hb]
          _ = a * a' * (b * b') := by group
      one_mem' := ⟨1, one_mem _, 1, one_mem _, by simp⟩
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, inv_mem ha, b⁻¹, inv_mem hb, ?_⟩
        rw [mul_inv_rev, ← hAB a⁻¹ (inv_mem ha) b⁻¹ (inv_mem hb)] }
  have hle : A ⊔ B ≤ P := sup_le (fun a ha => ⟨a, ha, 1, one_mem _, by simp⟩)
    (fun b hb => ⟨1, one_mem _, b, hb, by simp⟩)
  exact hle hx

namespace Red3

variable [Finite H] {P P₁ P₂ : Subgroup H} (h : Red3 P P₁ P₂)
include h

theorem le₁ : P₁ ≤ P := h.sup ▸ le_sup_left

theorem le₂ : P₂ ≤ P := h.sup ▸ le_sup_right

theorem comm {x y : H} (hx : x ∈ P) (hy : y ∈ P) : x * y = y * x := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard : Nat.card P = 3 ^ 2 := by rw [h.card]; norm_num
  have := IsPGroup.commutative_of_card_eq_prime_sq hcard
  exact congrArg Subtype.val (this (⟨x, hx⟩ : P) ⟨y, hy⟩)

theorem pow_three_of_mem₁ {a : H} (ha : a ∈ P₁) : a ^ 3 = 1 := by
  have : (⟨a, ha⟩ : P₁) ^ Nat.card P₁ = 1 := pow_card_eq_one'
  rw [h.c₁] at this
  exact congrArg Subtype.val this

theorem pow_three_of_mem₂ {a : H} (ha : a ∈ P₂) : a ^ 3 = 1 := by
  have : (⟨a, ha⟩ : P₂) ^ Nat.card P₂ = 1 := pow_card_eq_one'
  rw [h.c₂] at this
  exact congrArg Subtype.val this

theorem pow_three {x : H} (hx : x ∈ P) : x ^ 3 = 1 := by
  rw [← h.sup] at hx
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_commute
    (fun a ha b hb => h.comm (h.le₁ ha) (h.le₂ hb)) hx
  have hc : Commute a b := h.comm (h.le₁ ha) (h.le₂ hb)
  rw [hc.mul_pow, h.pow_three_of_mem₁ ha, h.pow_three_of_mem₂ hb, one_mul]

@[expose] noncomputable def toSylow : Sylow 3 H :=
  h.sylow.2.1.toSylow (by
    have := h.sylow.2.2
    rwa [Subgroup.relIndex_top_right, ← Nat.Prime.coprime_iff_not_dvd Nat.prime_three,
      Nat.coprime_comm] at *)

@[simp] theorem coe_toSylow : (h.toSylow : Subgroup H) = P := rfl

theorem eq_of_invariant {Q R T : Subgroup H} (hT : Nat.card T = 3)
    (hQP : Q ≤ P) (hRP : R ≤ P) (hsup : Q ⊔ R = P) (hTP : T ≤ P) {n : H}
    (hinv : ∀ q ∈ Q, n * q * n⁻¹ = q⁻¹) (hcen : ∀ r ∈ R, n * r * n⁻¹ = r)
    (hT' : ∀ a ∈ T, n * a * n⁻¹ ∈ T) (hQ : Nat.card Q = 3) (hR : Nat.card R = 3) :
    T = Q ∨ T = R := by
  have hne : T ≠ ⊥ := by
    intro hb
    rw [hb] at hT
    simp at hT
  obtain ⟨⟨a, haT⟩, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
  have ha1' : a ≠ 1 := fun h => ha1 (Subtype.ext h)
  have ha3 : a ^ 3 = 1 := h.pow_three (hTP haT)
  have hord : orderOf a = 3 := orderOf_eq_prime ha3 ha1'
  have hTeq : T = Subgroup.zpowers a := by
    symm
    exact Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr haT)
      (by rw [Nat.card_zpowers, hord, hT])
  obtain ⟨q, hq, r, hr, har⟩ := exists_mul_of_mem_sup_of_commute (A := Q) (B := R)
    (fun q hq r hr => h.comm (hQP hq) (hRP hr)) (hsup ▸ hTP haT : a ∈ Q ⊔ R)
  have hq3 : q ^ 3 = 1 := h.pow_three (hQP hq)
  have hr3 : r ^ 3 = 1 := h.pow_three (hRP hr)
  have hc : q * r = r * q := h.comm (hQP hq) (hRP hr)
  have hb : n * a * n⁻¹ = q⁻¹ * r := by
    rw [har]
    calc n * (q * r) * n⁻¹ = (n * q * n⁻¹) * (n * r * n⁻¹) := by group
      _ = q⁻¹ * r := by rw [hinv q hq, hcen r hr]
  have hbT := hT' a haT
  rw [hTeq] at hbT
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hbT
  have hmod : a ^ (k % (orderOf a : ℤ)) = a ^ k := zpow_mod_orderOf a k
  rw [hord] at hmod
  have hk3 : k % ((3 : ℕ) : ℤ) = 0 ∨ k % ((3 : ℕ) : ℤ) = 1 ∨ k % ((3 : ℕ) : ℤ) = 2 := by omega
  rcases hk3 with h0 | h1 | h2
  · rw [h0] at hmod
    simp only [zpow_zero] at hmod
    rw [← hmod] at hk
    exfalso
    apply ha1'
    have : n * a * n⁻¹ = 1 := hk.symm
    simpa using this
  · rw [h1] at hmod
    simp only [zpow_one] at hmod
    rw [← hmod] at hk
    have hk' : q * r = q⁻¹ * r := by rw [← har, hk, hb]
    have hqq : q = q⁻¹ := mul_right_cancel hk'
    have h2 : q * q = 1 := mul_eq_one_iff_eq_inv.mpr hqq
    have hq1 : q = 1 := by
      calc q = q * (q * q) := by rw [h2, mul_one]
        _ = q ^ 3 := by rw [pow_succ, pow_two, mul_assoc]
        _ = 1 := hq3
    right
    have har' : a = r := by rw [har, hq1, one_mul]
    have hTR : T ≤ R := by
      rw [hTeq]
      exact Subgroup.zpowers_le.mpr (har' ▸ hr)
    exact Subgroup.eq_of_le_of_card_ge hTR (by rw [hR, hT])
  · rw [h2] at hmod
    have hk2 : n * a * n⁻¹ = a ^ (2 : ℤ) := by rw [hmod, hk]
    have hsq : a ^ (2 : ℤ) = q ^ 2 * r ^ 2 := by
      rw [har]
      simp only [zpow_ofNat]
      exact (Commute.mul_pow (show Commute q r from hc) 2)
    rw [hb, hsq] at hk2
    have hqi : q⁻¹ = q ^ 2 := by
      have : q ^ 3 = 1 := hq3
      rw [inv_eq_iff_mul_eq_one, ← pow_succ']
      exact this
    rw [hqi] at hk2
    have hr2 : r = r ^ 2 := mul_left_cancel hk2 |>.trans rfl
    have hr1 : r = 1 := by
      have : r * r = r * 1 := by rw [mul_one, ← pow_two]; exact hr2.symm
      exact mul_left_cancel this
    left
    have har' : a = q := by rw [har, hr1, mul_one]
    have hTQ : T ≤ Q := by
      rw [hTeq]
      exact Subgroup.zpowers_le.mpr (har' ▸ hq)
    exact Subgroup.eq_of_le_of_card_ge hTQ (by rw [hQ, hT])

theorem reflection {Q R : Subgroup H} (hQ : Nat.card Q = 3) (hR : Nat.card R = 3)
    (hQP : Q ≤ P) (hRP : R ≤ P) (hsup : Q ⊔ R = P) {n : H}
    (hinv : ∀ q ∈ Q, n * q * n⁻¹ = q⁻¹) (hcen : ∀ r ∈ R, n * r * n⁻¹ = r) :
    (P₁ = Q ∧ P₂ = R) ∨ (P₁ = R ∧ P₂ = Q) := by
  have hmemP : ∀ a ∈ P, n * a * n⁻¹ ∈ P := by
    intro a ha
    rw [← hsup] at ha
    obtain ⟨q, hq, r, hr, rfl⟩ := exists_mul_of_mem_sup_of_commute (A := Q) (B := R)
      (fun q hq r hr => h.comm (hQP hq) (hRP hr)) ha
    have : n * (q * r) * n⁻¹ = q⁻¹ * r := by
      calc n * (q * r) * n⁻¹ = (n * q * n⁻¹) * (n * r * n⁻¹) := by group
        _ = q⁻¹ * r := by rw [hinv q hq, hcen r hr]
    rw [this]
    exact mul_mem (inv_mem (hQP hq)) (hRP hr)
  have h₁ : P₁ = Q ∨ P₁ = R := by
    refine h.eq_of_invariant h.c₁ hQP hRP hsup h.le₁ hinv hcen (fun a ha => ?_) hQ hR
    have hP : n * a * n⁻¹ ∈ P := hmemP a (h.le₁ ha)
    have := h.sc₁.2 a ha n⁻¹ (by simpa using hP)
    simpa using this
  have h₂ : P₂ = Q ∨ P₂ = R := by
    refine h.eq_of_invariant h.c₂ hQP hRP hsup h.le₂ hinv hcen (fun a ha => ?_) hQ hR
    have hP : n * a * n⁻¹ ∈ P := hmemP a (h.le₂ ha)
    have := h.sc₂.2 a ha n⁻¹ (by simpa using hP)
    simpa using this
  have hne : ∀ T : Subgroup H, Nat.card T = 3 → T ≠ ⊥ := by
    intro T hT hb
    rw [hb] at hT
    simp at hT
  rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
  · exact absurd (by rw [← h.inf, h₁, h₂, inf_idem]) (hne Q hQ)
  · exact Or.inl ⟨h₁, h₂⟩
  · exact Or.inr ⟨h₁, h₂⟩
  · exact absurd (by rw [← h.inf, h₁, h₂, inf_idem]) (hne R hR)

end Red3

end CFSG.RankThree.PartTwo.Sec21.FF84
