module

public import Mathlib.Algebra.Field.IsField
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.Timmesfeld.Transvection.GaloisAlign

variable {K : Type*} [Field K]

theorem eq_of_mul_self_eq_mul_self [CharP K 2] {x y : K} (h : x * x = y * y) : x = y := by
  have h1 : (x + y) * (x + y) = 0 := by
    rw [CharTwo.add_mul_self, h, CharTwo.add_self_eq_zero]
  have h2 : x + y = 0 := mul_self_eq_zero.1 h1
  rw [← CharTwo.sub_eq_add, sub_eq_zero] at h2
  exact h2

variable [Finite K] [CharP K 2]

theorem exists_ringEquiv_of_map_add {f : K → K} (hf : ∀ a b, f (a + b) = f a + f b)
    (hf1 : f 1 ≠ 0) (κ : Kˣ →* Kˣ) (hκ : ∀ ν : Kˣ, f (κ ν) = ν * ν * f 1) :
    ∃ τ : K ≃+* K, ∀ ν : Kˣ, ((κ ν : Kˣ) : K) = τ ν := by
  classical
  have hf0 : f 0 = 0 := by
    have h := hf 0 0
    rw [add_zero] at h
    exact left_eq_add.1 h
  have hinj : Function.Injective κ := by
    intro ν ν' h
    have h1 := hκ ν
    rw [h, hκ ν'] at h1
    exact Units.ext (eq_of_mul_self_eq_mul_self (mul_right_cancel₀ hf1 h1).symm)
  let e : Kˣ ≃* Kˣ := MulEquiv.ofBijective κ ⟨hinj, Finite.injective_iff_surjective.1 hinj⟩
  have he : ∀ ν, e ν = κ ν := fun _ => rfl
  let ψ : K → K := fun c => if hc : c = 0 then 0 else ((e.symm (Units.mk0 c hc) : Kˣ) : K)
  have hψ0 : ψ 0 = 0 := dite_eq_left rfl
  have hψu : ∀ ν : Kˣ, ψ (κ ν) = ν := by
    intro ν
    have hne : ((κ ν : Kˣ) : K) ≠ 0 := (κ ν).ne_zero
    simp only [ψ, dite_eq_right hne, Units.mk0_val]
    rw [← he, MulEquiv.symm_apply_apply]
  have hψsq : ∀ c, ψ c * ψ c * f 1 = f c := by
    intro c
    by_cases hc : c = 0
    · rw [hc, hψ0, hf0, mul_zero, zero_mul]
    · obtain ⟨ν, hν⟩ := Finite.injective_iff_surjective.1 hinj (Units.mk0 c hc)
      have hc' : c = ((κ ν : Kˣ) : K) := by rw [hν, Units.val_mk0]
      rw [hc', hψu, hκ]
  have hψadd : ∀ a b, ψ (a + b) = ψ a + ψ b := by
    intro a b
    refine eq_of_mul_self_eq_mul_self (mul_right_cancel₀ hf1 ?_)
    rw [hψsq, CharTwo.add_mul_self, add_mul, hψsq, hψsq, hf]
  have hψmul : ∀ a b, ψ (a * b) = ψ a * ψ b := by
    intro a b
    by_cases ha : a = 0
    · rw [ha, zero_mul, hψ0, zero_mul]
    by_cases hb : b = 0
    · rw [hb, mul_zero, hψ0, mul_zero]
    obtain ⟨ν, hν⟩ := Finite.injective_iff_surjective.1 hinj (Units.mk0 a ha)
    obtain ⟨ν', hν'⟩ := Finite.injective_iff_surjective.1 hinj (Units.mk0 b hb)
    have ha' : a = ((κ ν : Kˣ) : K) := by rw [hν, Units.val_mk0]
    have hb' : b = ((κ ν' : Kˣ) : K) := by rw [hν', Units.val_mk0]
    rw [ha', hb', ← Units.val_mul, ← map_mul, hψu, hψu, hψu, Units.val_mul]
  have hψ1 : ψ 1 = 1 := by
    have h := hψu 1
    rwa [map_one, Units.val_one] at h
  let ρ : K →+* K :=
    { toFun := ψ
      map_one' := hψ1
      map_mul' := hψmul
      map_zero' := hψ0
      map_add' := hψadd }
  have hρinj : Function.Injective ρ := ρ.injective
  let τ : K ≃+* K := RingEquiv.ofBijective ρ ⟨hρinj, Finite.injective_iff_surjective.1 hρinj⟩
  refine ⟨τ.symm, fun ν => ?_⟩
  rw [RingEquiv.eq_symm_apply]
  exact hψu ν

theorem exists_ringEquiv_of_torus {V : Type*} (act : Kˣ → V → V) {γ : V → K → K}
    (hadd : ∀ x s t, γ x (s + t) = γ x s + γ x t)
    (hi : ∀ (μ : Kˣ) x t, γ (act μ x) t = γ x (μ * μ * t)) (κ : Kˣ →* Kˣ)
    (hj : ∀ (ν : Kˣ) x t, γ (act (κ ν) x) t = ((ν⁻¹ : Kˣ) : K) * ((ν⁻¹ : Kˣ) : K) * γ x t)
    (hne : ∃ x t, γ x t ≠ 0) :
    ∃ τ : K ≃+* K, ∀ ν : Kˣ, ((κ ν : Kˣ) : K) = ((τ ν)⁻¹ : K) := by
  obtain ⟨x₀, t₀, h0⟩ := hne
  let κ' : Kˣ →* Kˣ := κ.comp (MulEquiv.inv Kˣ).toMonoidHom
  have hκ' : ∀ ν, κ' ν = κ ν⁻¹ := fun _ => rfl
  have hf : ∀ a b : K, γ x₀ ((a + b) * (a + b) * t₀) = γ x₀ (a * a * t₀) + γ x₀ (b * b * t₀) := by
    intro a b
    rw [CharTwo.add_mul_self, add_mul, hadd]
  have hf1 : γ x₀ (1 * 1 * t₀) ≠ 0 := by rwa [one_mul, one_mul]
  have hκf : ∀ ν : Kˣ, γ x₀ (((κ' ν : Kˣ) : K) * ((κ' ν : Kˣ) : K) * t₀) =
      ν * ν * γ x₀ (1 * 1 * t₀) := by
    intro ν
    rw [← hi, hκ', hj, inv_inv, one_mul, one_mul]
  obtain ⟨τ, hτ⟩ := exists_ringEquiv_of_map_add (f := fun c => γ x₀ (c * c * t₀)) hf hf1 κ' hκf
  refine ⟨τ, fun ν => ?_⟩
  have h := hτ ν⁻¹
  rw [hκ', inv_inv] at h
  rw [h, Units.val_inv_eq_inv_val, map_inv₀]

end CFSG.Timmesfeld.Transvection.GaloisAlign
