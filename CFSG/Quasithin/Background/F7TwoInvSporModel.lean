module

public import CFSG.Quasithin.Background.F7TwoInvSeed
public import CFSG.Quasithin.Background.F7TwoInvExcBasic

public section

namespace CFSG.Quasithin.F7Two

variable {Γ : Type*} [Group Γ]

theorem invAutGen_of_conj_model {P : Subgroup Γ} {φ : MulAut P} {ρ : Γ} {a b : P}
    (hφ : ∀ g : P, ((φ g : P) : Γ) = ρ * g * ρ⁻¹)
    (hab : Subgroup.closure ({a, b} : Set P) = ⊤) (ha : ρ * a = a * ρ)
    (hb : ∀ n : ℕ, (ρ * b * ρ⁻¹ * (b : Γ)⁻¹) ^ 2 ^ n ≠ 1) : InvAutGen P φ := by
  have hXi : b ∈ invXiAut φ := by
    rw [mem_invXiAut_iff]
    intro n h
    apply hb n
    have h' := congrArg (fun x : P => (x : Γ)) h
    simpa [hφ] using h'
  refine invAutGen_of_seeds hab ?_ ⟨b, by simp, hXi⟩
  rintro x (rfl | rfl)
  · refine Or.inr (Subtype.ext ?_)
    rw [hφ]
    exact mul_inv_eq_iff_eq_mul.2 ha
  · exact Or.inl hXi

theorem forall_pow_two_pow_ne_one_of_orderOf {y : Γ} {s m : ℕ} (hm : Odd m) (hm1 : 1 < m)
    (hy : orderOf y = 2 ^ s * m) : ∀ n : ℕ, y ^ 2 ^ n ≠ 1 :=
  pow_two_pow_ne_one_of_pow hm (by rw [← hy]; exact pow_orderOf_eq_one y)
    (pow_ne_one_of_lt_orderOf (by positivity)
      (by rw [hy]; exact lt_mul_of_one_lt_right (by positivity) hm1))

section Model

variable {P R : Subgroup Γ}

@[expose] def modelConjHom (hconj : ∀ x ∈ R, ∀ p ∈ P, x * p * x⁻¹ ∈ P) : R →* MulAut P where
  toFun x :=
    { toFun := fun p => ⟨x * p * (x : Γ)⁻¹, hconj x x.2 p p.2⟩
      invFun := fun p => ⟨(x : Γ)⁻¹ * p * x, by simpa using hconj x⁻¹ (R.inv_mem x.2) p p.2⟩
      left_inv := fun p => Subtype.ext (by simp [mul_assoc])
      right_inv := fun p => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun p q => Subtype.ext (by simp [mul_assoc]) }
  map_one' := MulEquiv.ext fun p => Subtype.ext (by simp)
  map_mul' x y := MulEquiv.ext fun p => Subtype.ext (by simp [mul_assoc])

theorem modelConjHom_apply (hconj : ∀ x ∈ R, ∀ p ∈ P, x * p * x⁻¹ ∈ P) (x : R) (p : P) :
    ((modelConjHom hconj x p : P) : Γ) = x * p * (x : Γ)⁻¹ := rfl

@[expose] def SeedOK (s : Γ) (X : Set P) : Prop :=
  (∀ x ∈ X, (∀ n : ℕ, (s * x * s⁻¹ * (x : Γ)⁻¹) ^ 2 ^ n ≠ 1) ∨ s * x = x * s) ∧
    ∃ x ∈ X, ∀ n : ℕ, (s * x * s⁻¹ * (x : Γ)⁻¹) ^ 2 ^ n ≠ 1

theorem seedOK_pair {s : Γ} {a b : P}
    (ha : (∀ n : ℕ, (s * a * s⁻¹ * (a : Γ)⁻¹) ^ 2 ^ n ≠ 1) ∨ s * a = a * s)
    (hb : (∀ n : ℕ, (s * b * s⁻¹ * (b : Γ)⁻¹) ^ 2 ^ n ≠ 1) ∨ s * b = b * s)
    (hne : (∀ n : ℕ, (s * a * s⁻¹ * (a : Γ)⁻¹) ^ 2 ^ n ≠ 1) ∨
      (∀ n : ℕ, (s * b * s⁻¹ * (b : Γ)⁻¹) ^ 2 ^ n ≠ 1)) : SeedOK s ({a, b} : Set P) := by
  refine ⟨fun x hx => ?_, ?_⟩
  · rcases hx with rfl | rfl
    exacts [ha, hb]
  · rcases hne with h | h
    exacts [⟨a, by simp, h⟩, ⟨b, by simp, h⟩]

theorem invAutGen_modelConjHom_of_seedOK (hconj : ∀ x ∈ R, ∀ p ∈ P, x * p * x⁻¹ ∈ P) {s : Γ}
    (hs : s ∈ R) {X : Set P} (hX : Subgroup.closure X = ⊤) (hseed : SeedOK s X) :
    InvAutGen P (modelConjHom hconj ⟨s, hs⟩) := by
  have key : ∀ x : P, x ∈ invXiAut (modelConjHom hconj ⟨s, hs⟩) ↔
      ∀ n : ℕ, (s * x * s⁻¹ * (x : Γ)⁻¹) ^ 2 ^ n ≠ 1 := fun x => by
    rw [mem_invXiAut_iff]
    constructor
    · intro h n hn
      apply h n
      apply Subtype.ext
      simpa [modelConjHom_apply] using hn
    · intro h n hn
      apply h n
      have := congrArg (fun y : P => (y : Γ)) hn
      simpa [modelConjHom_apply] using this
  obtain ⟨hall, x₀, hx₀, hx₀n⟩ := hseed
  refine invAutGen_of_seeds hX (fun x hx => ?_) ⟨x₀, hx₀, (key x₀).2 hx₀n⟩
  rcases hall x hx with h | h
  · exact Or.inl ((key x).2 h)
  · refine Or.inr (Subtype.ext ?_)
    rw [modelConjHom_apply]
    exact mul_inv_eq_iff_eq_mul.2 h

theorem invAutGen_of_model (hle : P ≤ R) (hconj : ∀ x ∈ R, ∀ p ∈ P, x * p * x⁻¹ ∈ P)
    (hsurj : ∀ α : MulAut P, ∃ x ∈ R, ∀ p : P, ((α p : P) : Γ) = x * p * x⁻¹)
    (hinj : ∀ x ∈ R, (∀ p ∈ P, x * p = p * x) → x = 1) {X : Set P}
    (hX : Subgroup.closure X = ⊤) (reps : List Γ)
    (hcover : ∀ x ∈ R, x * x = 1 → x ≠ 1 → ∃ ρ ∈ reps, ∃ c ∈ P, x = c * ρ * c⁻¹)
    (hreps : ∀ ρ ∈ reps, ρ ∈ R ∧ ∃ d ∈ R, SeedOK (d * ρ * d⁻¹) X) :
    ∀ φ : MulAut P, φ * φ = 1 → φ ≠ 1 → InvAutGen P φ := by
  intro φ hφ2 hφ1
  obtain ⟨x, hxR, hx⟩ := hsurj φ
  have hφx : φ = modelConjHom hconj ⟨x, hxR⟩ := MulEquiv.ext fun p => Subtype.ext (hx p)
  have hx2 : x * x = 1 := by
    refine hinj _ (R.mul_mem hxR hxR) fun p hp => ?_
    have h1 := congrArg (fun ψ : MulAut P => ((ψ ⟨p, hp⟩ : P) : Γ)) hφ2
    simp only [MulAut.mul_apply, MulAut.one_apply] at h1
    rw [hx, hx] at h1
    simp only at h1
    calc x * x * p = (x * (x * p * x⁻¹) * x⁻¹) * x * x := by group
      _ = p * (x * x) := by rw [h1, mul_assoc]
  have hx1 : x ≠ 1 := by
    rintro rfl
    exact hφ1 (MulEquiv.ext fun p => Subtype.ext (by rw [hx p]; simp))
  obtain ⟨ρ, hρ, c, hc, hxc⟩ := hcover x hxR hx2 hx1
  obtain ⟨hρR, d, hdR, hseed⟩ := hreps ρ hρ
  have hρ'R : d * ρ * d⁻¹ ∈ R := R.mul_mem (R.mul_mem hdR hρR) (R.inv_mem hdR)
  have hP' := invAutGen_modelConjHom_of_seedOK hconj hρ'R hX hseed
  have hcR : c ∈ R := hle hc
  have hρeq : (⟨ρ, hρR⟩ : R) = ⟨d, hdR⟩⁻¹ * ⟨d * ρ * d⁻¹, hρ'R⟩ * ⟨d, hdR⟩ :=
    Subtype.ext (by simp [mul_assoc])
  have hP : InvAutGen P (modelConjHom hconj ⟨ρ, hρR⟩) := by
    refine invAutGen_of_conj_aut (modelConjHom hconj ⟨d, hdR⟩)⁻¹ ?_ hP'
    rw [hρeq, map_mul, map_mul, map_inv, inv_inv]
  have hxeq : (⟨x, hxR⟩ : R) = ⟨c, hcR⟩ * ⟨ρ, hρR⟩ * ⟨c, hcR⟩⁻¹ := Subtype.ext (by simp [hxc])
  rw [hφx]
  refine invAutGen_of_conj_aut (modelConjHom hconj ⟨c, hcR⟩) ?_ hP
  rw [hxeq, map_mul, map_mul, map_inv]

end Model

end CFSG.Quasithin.F7Two
