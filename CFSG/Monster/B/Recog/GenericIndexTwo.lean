module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.Monster.B.Recog

namespace IndexTwo

variable {A E E' : Type*} [Group A] [Group E] [Group E']

theorem eq_or_eq_mul (ι : A →* E) (h2 : ι.range.index = 2) {s : E} (hs : s ∉ ι.range)
    (x : E) : (∃ a, x = ι a) ∨ ∃ a, x = ι a * s := by
  by_cases hx : x ∈ ι.range
  · obtain ⟨a, rfl⟩ := hx
    exact Or.inl ⟨a, rfl⟩
  · have : x * s⁻¹ ∈ ι.range := by
      rw [Subgroup.mul_mem_iff_of_index_two h2]
      exact iff_of_false hx fun h => hs (by simpa using ι.range.inv_mem h)
    obtain ⟨a, ha⟩ := this
    exact Or.inr ⟨a, by rw [ha, inv_mul_cancel_right]⟩

theorem mul_not_mem (ι : A →* E) {s : E} (hs : s ∉ ι.range) (a : A) : ι a * s ∉ ι.range :=
  fun h => hs (by simpa using ι.range.mul_mem (⟨a⁻¹, rfl⟩ : ι a⁻¹ ∈ ι.range) h)

theorem exists_sq (ι : A →* E) (hι : Function.Injective ι) (h2 : ι.range.index = 2) (σ : A →* A)
    (s : E) (hσ : ∀ a, s * ι a * s⁻¹ = ι (σ a)) :
    ∃ τ, s * s = ι τ ∧ σ τ = τ ∧ ∀ a, σ (σ a) = τ * a * τ⁻¹ := by
  obtain ⟨τ, hτ⟩ := Subgroup.mul_self_mem_of_index_two h2 s
  refine ⟨τ, hτ.symm, hι ?_, fun a => hι ?_⟩
  · rw [← hσ, hτ, mul_assoc, mul_inv_cancel_right]
  · rw [← hσ, ← hσ, map_mul, map_mul, map_inv, hτ]
    group

theorem mul_mul_eq (ι : A →* E) (a b : A) (s : E) : ι a * (ι b * s) = ι (a * b) * s := by
  rw [map_mul, mul_assoc]

theorem mul_mul_eq' (ι : A →* E) {s : E} {σ : A → A} (hc : ∀ b, s * ι b = ι (σ b) * s)
    (a b : A) : ι a * s * ι b = ι (a * σ b) * s := by
  rw [mul_assoc, hc, map_mul, mul_assoc]

theorem mul_mul_eq'' (ι : A →* E) {s : E} {σ : A → A} {τ : A}
    (hc : ∀ b, s * ι b = ι (σ b) * s) (hτ : s * s = ι τ) (a b : A) :
    ι a * s * (ι b * s) = ι (a * σ b * τ) := by
  rw [← mul_assoc, mul_mul_eq' ι hc, mul_assoc, hτ, ← map_mul]

theorem exists_hom (ι : A →* E) (ι' : A →* E') (hι : Function.Injective ι)
    (h2 : ι.range.index = 2) {s : E} (hs : s ∉ ι.range) (s' : E') (σ : A → A) (τ : A)
    (hσ : ∀ a, s * ι a * s⁻¹ = ι (σ a)) (hσ' : ∀ a, s' * ι' a * s'⁻¹ = ι' (σ a))
    (hτ : s * s = ι τ) (hτ' : s' * s' = ι' τ) :
    ∃ f : E →* E', (∀ a, f (ι a) = ι' a) ∧ f s = s' := by
  classical
  have hmem : ∀ x : E, x ∉ ι.range → x * s⁻¹ ∈ ι.range := fun x hx => by
    rw [Subgroup.mul_mem_iff_of_index_two h2]
    exact iff_of_false hx fun h => hs (by simpa using ι.range.inv_mem h)
  let f : E → E' := fun x =>
    if h : x ∈ ι.range then ι' (Classical.choose (MonoidHom.mem_range.1 h))
    else ι' (Classical.choose (MonoidHom.mem_range.1 (hmem x h))) * s'
  have f₀ : ∀ a, f (ι a) = ι' a := fun a => by
    have h : ι a ∈ ι.range := ⟨a, rfl⟩
    simp only [f, h, dite_true]
    rw [hι (Classical.choose_spec (MonoidHom.mem_range.1 h))]
  have f₁ : ∀ a, f (ι a * s) = ι' a * s' := fun a => by
    have h := mul_not_mem ι hs a
    simp only [f, h, dite_false]
    have hc := Classical.choose_spec (MonoidHom.mem_range.1 (hmem _ h))
    have : Classical.choose (MonoidHom.mem_range.1 (hmem _ h)) = a :=
      hι (hc.trans (mul_inv_cancel_right _ _))
    rw [this]
  have hc : ∀ b, s * ι b = ι (σ b) * s := fun b => by rw [← hσ, inv_mul_cancel_right]
  have hc' : ∀ b, s' * ι' b = ι' (σ b) * s' := fun b => by rw [← hσ', inv_mul_cancel_right]
  refine ⟨MonoidHom.mk' f fun x y => ?_, f₀, by simpa using f₁ 1⟩
  rcases eq_or_eq_mul ι h2 hs x with ⟨a, rfl⟩ | ⟨a, rfl⟩ <;>
    rcases eq_or_eq_mul ι h2 hs y with ⟨b, rfl⟩ | ⟨b, rfl⟩
  · rw [← map_mul, f₀, f₀, f₀, map_mul]
  · rw [mul_mul_eq, f₁, f₀, f₁, mul_mul_eq]
  · rw [mul_mul_eq' ι hc, f₁, f₁, f₀, mul_mul_eq' ι' hc']
  · rw [mul_mul_eq'' ι hc hτ, f₀, f₁, f₁, mul_mul_eq'' ι' hc' hτ']

end IndexTwo

open IndexTwo

variable {A E₁ E₂ : Type*} [Group A] [Group E₁] [Group E₂]

theorem exists_mulEquiv_of_index_two_of_eq (ι₁ : A →* E₁) (ι₂ : A →* E₂)
    (hι₁ : Function.Injective ι₁) (hι₂ : Function.Injective ι₂) (h₁ : ι₁.range.index = 2)
    (h₂ : ι₂.range.index = 2) {s₁ : E₁} {s₂ : E₂} (hs₁ : s₁ ∉ ι₁.range) (hs₂ : s₂ ∉ ι₂.range)
    (σ : A → A) (τ : A) (hσ₁ : ∀ a, s₁ * ι₁ a * s₁⁻¹ = ι₁ (σ a))
    (hσ₂ : ∀ a, s₂ * ι₂ a * s₂⁻¹ = ι₂ (σ a)) (hτ₁ : s₁ * s₁ = ι₁ τ) (hτ₂ : s₂ * s₂ = ι₂ τ) :
    ∃ e : E₁ ≃* E₂, (∀ a, e (ι₁ a) = ι₂ a) ∧ e s₁ = s₂ := by
  obtain ⟨f, hf, hfs⟩ := exists_hom ι₁ ι₂ hι₁ h₁ hs₁ s₂ σ τ hσ₁ hσ₂ hτ₁ hτ₂
  obtain ⟨g, hg, hgs⟩ := exists_hom ι₂ ι₁ hι₂ h₂ hs₂ s₁ σ τ hσ₂ hσ₁ hτ₂ hτ₁
  refine ⟨MonoidHom.toMulEquiv f g ?_ ?_, hf, hfs⟩
  · ext x
    rcases eq_or_eq_mul ι₁ h₁ hs₁ x with ⟨a, rfl⟩ | ⟨a, rfl⟩
    · simp [hf, hg]
    · simp [hf, hg, hfs, hgs]
  · ext x
    rcases eq_or_eq_mul ι₂ h₂ hs₂ x with ⟨a, rfl⟩ | ⟨a, rfl⟩
    · simp [hf, hg]
    · simp [hf, hg, hfs, hgs]

theorem exists_mulEquiv_of_index_two (ι₁ : A →* E₁) (ι₂ : A →* E₂)
    (hι₁ : Function.Injective ι₁) (hι₂ : Function.Injective ι₂) (h₁ : ι₁.range.index = 2)
    (h₂ : ι₂.range.index = 2) {s₁ : E₁} {s₂ : E₂} (hs₁ : s₁ ∉ ι₁.range) (hs₂ : s₂ ∉ ι₂.range)
    (σ₁ : A ≃* A) (σ₂ : A → A) (hσ₁ : ∀ a, s₁ * ι₁ a * s₁⁻¹ = ι₁ (σ₁ a))
    (hσ₂ : ∀ a, s₂ * ι₂ a * s₂⁻¹ = ι₂ (σ₂ a)) (b : A) (hb : ∀ a, σ₂ a = σ₁ (b * a * b⁻¹))
    (hnorm : ∀ c ∈ Subgroup.center A, σ₁ c = c → ∃ d ∈ Subgroup.center A, c = d * σ₁ d) :
    ∃ e : E₁ ≃* E₂, ∀ a, e (ι₁ a) = ι₂ a := by
  set t := s₂ * ι₂ b⁻¹ with ht
  have htσ : ∀ a, t * ι₂ a * t⁻¹ = ι₂ (σ₁ a) := fun a => by
    have := hσ₂ (b⁻¹ * a * b)
    rw [hb, show b * (b⁻¹ * a * b) * b⁻¹ = a by group] at this
    rw [← this, ht, map_mul, map_mul, map_inv]
    group
  have htn : t ∉ ι₂.range := fun h => hs₂ (by
    simpa [ht] using ι₂.range.mul_mem h (⟨b, rfl⟩ : ι₂ b ∈ ι₂.range))
  obtain ⟨τ₁, hτ₁, hτ₁σ, hτ₁c⟩ := exists_sq ι₁ hι₁ h₁ σ₁.toMonoidHom s₁ hσ₁
  obtain ⟨τ₂, hτ₂, hτ₂σ, hτ₂c⟩ := exists_sq ι₂ hι₂ h₂ σ₁.toMonoidHom t htσ
  simp only [MulEquiv.coe_toMonoidHom] at hτ₁σ hτ₁c hτ₂σ hτ₂c
  have hcen : τ₂⁻¹ * τ₁ ∈ Subgroup.center A := Subgroup.mem_center_iff.2 fun a => by
    have := hτ₁c a
    rw [hτ₂c] at this
    calc a * (τ₂⁻¹ * τ₁) = τ₂⁻¹ * (τ₂ * a * τ₂⁻¹) * τ₁ := by group
      _ = τ₂⁻¹ * τ₁ * a := by rw [this]; group
  have hfix : σ₁ (τ₂⁻¹ * τ₁) = τ₂⁻¹ * τ₁ := by rw [map_mul, map_inv, hτ₁σ, hτ₂σ]
  obtain ⟨d, hd, hcd⟩ := hnorm _ hcen hfix
  have hσd : σ₁ d ∈ Subgroup.center A := Subgroup.mem_center_iff.2 fun a => by
    have := Subgroup.mem_center_iff.1 hd (σ₁.symm a)
    simpa using congrArg σ₁ this
  set t' := t * ι₂ (σ₁ d) with ht'
  have ht'σ : ∀ a, t' * ι₂ a * t'⁻¹ = ι₂ (σ₁ a) := fun a => by
    have hcomm : ι₂ (σ₁ d) * ι₂ a * (ι₂ (σ₁ d))⁻¹ = ι₂ a := by
      rw [← map_mul, ← Subgroup.mem_center_iff.1 hσd a, map_mul, mul_inv_cancel_right]
    calc t' * ι₂ a * t'⁻¹ = t * (ι₂ (σ₁ d) * ι₂ a * (ι₂ (σ₁ d))⁻¹) * t⁻¹ := by
          rw [ht']
          group
      _ = ι₂ (σ₁ a) := by rw [hcomm, htσ]
  have ht'n : t' ∉ ι₂.range := fun h => htn (by
    simpa [ht'] using ι₂.range.mul_mem h (⟨(σ₁ d)⁻¹, rfl⟩ : ι₂ (σ₁ d)⁻¹ ∈ ι₂.range))
  have ht'sq : t' * t' = ι₂ τ₁ := by
    have hdt : ι₂ (σ₁ d) * t = t * ι₂ d := by rw [← htσ, inv_mul_cancel_right]
    have : τ₁ = τ₂ * (d * σ₁ d) := by rw [← hcd, mul_inv_cancel_left]
    rw [this, ht', map_mul, map_mul, ← hτ₂]
    calc t * ι₂ (σ₁ d) * (t * ι₂ (σ₁ d)) = t * (ι₂ (σ₁ d) * t) * ι₂ (σ₁ d) := by group
      _ = t * t * (ι₂ d * ι₂ (σ₁ d)) := by rw [hdt]; group
  obtain ⟨e, he, -⟩ := exists_mulEquiv_of_index_two_of_eq ι₁ ι₂ hι₁ hι₂ h₁ h₂ hs₁ ht'n σ₁ τ₁ hσ₁
    ht'σ hτ₁ ht'sq
  exact ⟨e, he⟩

theorem exists_mulEquiv_of_index_two' (ι₁ : A →* E₁) (ι₂ : A →* E₂)
    (hι₁ : Function.Injective ι₁) (hι₂ : Function.Injective ι₂) (h₁ : ι₁.range.index = 2)
    (h₂ : ι₂.range.index = 2) {s₁ : E₁} {s₂ : E₂} (hs₁ : s₁ ∉ ι₁.range) (hs₂ : s₂ ∉ ι₂.range)
    (σ₁ : A ≃* A) (σ₂ : A → A) (hσ₁ : ∀ a, s₁ * ι₁ a * s₁⁻¹ = ι₁ (σ₁ a))
    (hσ₂ : ∀ a, s₂ * ι₂ a * s₂⁻¹ = ι₂ (σ₂ a)) (c : A) (hc : ∀ a, σ₂ a = c * σ₁ a * c⁻¹)
    (hnorm : ∀ c ∈ Subgroup.center A, σ₁ c = c → ∃ d ∈ Subgroup.center A, c = d * σ₁ d) :
    ∃ e : E₁ ≃* E₂, ∀ a, e (ι₁ a) = ι₂ a :=
  exists_mulEquiv_of_index_two ι₁ ι₂ hι₁ hι₂ h₁ h₂ hs₁ hs₂ σ₁ σ₂ hσ₁ hσ₂ (σ₁.symm c)
    (fun a => by rw [hc, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]) hnorm

end CFSG.Monster.B.Recog
