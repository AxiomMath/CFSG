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

namespace CFSG.Quasithin

open scoped commutatorElement Pointwise

variable {A : Type*} [Group A] {B : Type*} [Group B]

theorem commutator_mul_central_left {a z b : A} (hzb : z * b = b * z) :
    ⁅a * z, b⁆ = ⁅a, b⁆ := by
  have h : z * b * z⁻¹ = b := by rw [hzb]; group
  simp only [commutatorElement_def]
  calc a * z * b * (a * z)⁻¹ * b⁻¹ = a * (z * b * z⁻¹) * a⁻¹ * b⁻¹ := by group
    _ = a * b * a⁻¹ * b⁻¹ := by rw [h]

theorem commutator_mul_central_right {a b w : A} (hwa : w * a = a * w) :
    ⁅a, b * w⁆ = ⁅a, b⁆ := by
  have h : w * a⁻¹ * w⁻¹ = a⁻¹ := by
    have : Commute w a := hwa
    have h2 : w * a⁻¹ = a⁻¹ * w := this.inv_right.eq
    rw [h2]; group
  simp only [commutatorElement_def]
  calc a * (b * w) * a⁻¹ * (b * w)⁻¹ = a * b * (w * a⁻¹ * w⁻¹) * b⁻¹ := by group
    _ = a * b * a⁻¹ * b⁻¹ := by rw [h]

theorem abelian_of_generators (π : A →* B) {X : Subgroup A} {d₁ d₂ : A}
    (hd₁ : d₁ ∈ X ⊓ Subgroup.centralizer ((X ⊓ π.ker : Subgroup A) : Set A))
    (hd₂ : d₂ ∈ X ⊓ Subgroup.centralizer ((X ⊓ π.ker : Subgroup A) : Set A))
    (hd12 : Commute d₁ d₂)
    (hgen : ∀ d ∈ X ⊓ Subgroup.centralizer ((X ⊓ π.ker : Subgroup A) : Set A),
      ∃ i j : ℕ, π d = π d₁ ^ i * π d₂ ^ j) :
    ∀ a ∈ X ⊓ Subgroup.centralizer ((X ⊓ π.ker : Subgroup A) : Set A),
      ∀ b ∈ X ⊓ Subgroup.centralizer ((X ⊓ π.ker : Subgroup A) : Set A), a * b = b * a := by
  set N : Subgroup A := X ⊓ π.ker with hN
  set D : Subgroup A := X ⊓ Subgroup.centralizer (N : Set A) with hD
  have hcen : ∀ z ∈ N, ∀ d ∈ D, z * d = d * z := fun z hz d hd =>
    Subgroup.mem_centralizer_iff.mp hd.2 z hz
  have hker : ∀ z ∈ D, π z = 1 → z ∈ N := fun z hz h => ⟨hz.1, MonoidHom.mem_ker.mpr h⟩
  intro a ha b hb
  obtain ⟨i, j, hij⟩ := hgen a ha
  obtain ⟨i', j', hij'⟩ := hgen b hb
  set a' := d₁ ^ i * d₂ ^ j with ha'
  set b' := d₁ ^ i' * d₂ ^ j' with hb'
  have ha'D : a' ∈ D := D.mul_mem (D.pow_mem hd₁ i) (D.pow_mem hd₂ j)
  have hb'D : b' ∈ D := D.mul_mem (D.pow_mem hd₁ i') (D.pow_mem hd₂ j')
  have hπa' : π a' = π a := by rw [ha', map_mul, map_pow, map_pow, hij]
  have hπb' : π b' = π b := by rw [hb', map_mul, map_pow, map_pow, hij']
  have zaD : a * a'⁻¹ ∈ D := D.mul_mem ha (D.inv_mem ha'D)
  have zbD : b * b'⁻¹ ∈ D := D.mul_mem hb (D.inv_mem hb'D)
  have zaN : a * a'⁻¹ ∈ N := hker _ zaD (by rw [map_mul, map_inv, hπa']; exact mul_inv_cancel _)
  have zbN : b * b'⁻¹ ∈ N := hker _ zbD (by rw [map_mul, map_inv, hπb']; exact mul_inv_cancel _)
  have h2 : Commute (a * a'⁻¹) (b * b'⁻¹) := by
    unfold Commute SemiconjBy; exact hcen _ zaN _ zbD
  have h3 : Commute (a * a'⁻¹) b' := by
    unfold Commute SemiconjBy; exact hcen _ zaN b' hb'D
  have h4 : Commute (b * b'⁻¹) a' := by
    unfold Commute SemiconjBy; exact hcen _ zbN a' ha'D
  have h5 : Commute a' b' :=
    Commute.mul_left
      (Commute.mul_right ((Commute.refl d₁).pow_pow i i') (hd12.pow_pow i j'))
      (Commute.mul_right (hd12.symm.pow_pow j i') ((Commute.refl d₂).pow_pow j j'))
  have hA : a = (a * a'⁻¹) * a' := by group
  have hB : b = (b * b'⁻¹) * b' := by group
  calc a * b = ((a * a'⁻¹) * a') * ((b * b'⁻¹) * b') := by rw [← hA, ← hB]
    _ = (a * a'⁻¹) * (b * b'⁻¹) * (a' * b') := h4.symm.mul_mul_mul_comm _ _
    _ = (b * b'⁻¹) * (a * a'⁻¹) * (b' * a') := by rw [h2.eq, h5.eq]
    _ = ((b * b'⁻¹) * b') * ((a * a'⁻¹) * a') := (h3.symm.mul_mul_mul_comm _ _).symm
    _ = b * a := by rw [← hA, ← hB]

theorem abelian_of_eigenvectors (π : A →* B) {X R : Subgroup A} {ρ d₁ d₂ : A}
    (hRX : R ≤ Subgroup.normalizer (X : Set A))
    (hRN : ∀ ρ ∈ R, ∀ n ∈ X ⊓ π.ker, ρ * n = n * ρ) (hρ : ρ ∈ R)
    (hπab : ∀ x ∈ X, ∀ y ∈ X, π x * π y = π y * π x)
    (hexp : ∀ x ∈ X, π x ^ 3 = 1)
    (hd₁ : d₁ ∈ X ⊓ Subgroup.centralizer ((X ⊓ π.ker : Subgroup A) : Set A))
    (hd₂ : d₂ ∈ X ⊓ Subgroup.centralizer ((X ⊓ π.ker : Subgroup A) : Set A))
    (hgen : ∀ d ∈ X ⊓ Subgroup.centralizer ((X ⊓ π.ker : Subgroup A) : Set A),
      ∃ i j : ℕ, π d = π d₁ ^ i * π d₂ ^ j)
    (h₁ : π (ρ * d₁ * ρ⁻¹) = π d₁) (h₂ : π (ρ * d₂ * ρ⁻¹) = (π d₂)⁻¹) :
    ∀ a ∈ X ⊓ Subgroup.centralizer ((X ⊓ π.ker : Subgroup A) : Set A),
      ∀ b ∈ X ⊓ Subgroup.centralizer ((X ⊓ π.ker : Subgroup A) : Set A), a * b = b * a := by
  set N : Subgroup A := X ⊓ π.ker with hN
  set D : Subgroup A := X ⊓ Subgroup.centralizer (N : Set A) with hD
  have hcen : ∀ z ∈ N, ∀ d ∈ D, z * d = d * z := fun z hz d hd =>
    Subgroup.mem_centralizer_iff.mp hd.2 z hz
  have hker : ∀ z ∈ D, π z = 1 → z ∈ N := fun z hz h => ⟨hz.1, MonoidHom.mem_ker.mpr h⟩
  have hρD : ∀ d ∈ D, ρ * d * ρ⁻¹ ∈ D := by
    intro d hd
    refine ⟨(Subgroup.mem_normalizer_iff.mp (hRX hρ) d).mp hd.1, ?_⟩
    show ρ * d * ρ⁻¹ ∈ Subgroup.centralizer (N : Set A)
    rw [Subgroup.mem_centralizer_iff]
    intro n hn
    have hnρ : Commute n ρ := by
      unfold Commute SemiconjBy
      exact (hRN ρ hρ n hn).symm
    have hnd : Commute n d := by
      unfold Commute SemiconjBy
      exact hcen n hn d hd
    exact ((hnρ.mul_right hnd).mul_right hnρ.inv_right).eq
  have z₁D : d₁⁻¹ * (ρ * d₁ * ρ⁻¹) ∈ D := D.mul_mem (D.inv_mem hd₁) (hρD d₁ hd₁)
  have z₁N : d₁⁻¹ * (ρ * d₁ * ρ⁻¹) ∈ N :=
    hker _ z₁D (by rw [map_mul, map_inv, h₁]; exact inv_mul_cancel _)
  have w₂D : d₂ * (ρ * d₂ * ρ⁻¹) ∈ D := D.mul_mem hd₂ (hρD d₂ hd₂)
  have w₂N : d₂ * (ρ * d₂ * ρ⁻¹) ∈ N :=
    hker _ w₂D (by rw [map_mul, h₂]; exact mul_inv_cancel _)
  set z₁ := d₁⁻¹ * (ρ * d₁ * ρ⁻¹) with hz₁
  set w₂ := d₂ * (ρ * d₂ * ρ⁻¹) with hw₂
  have e₁ : ρ * d₁ * ρ⁻¹ = d₁ * z₁ := by rw [hz₁]; group
  have e₂ : ρ * d₂ * ρ⁻¹ = d₂⁻¹ * w₂ := by rw [hw₂]; group
  have hcD : ⁅d₁, d₂⁆ ∈ D := by
    simp only [commutatorElement_def]
    exact D.mul_mem (D.mul_mem (D.mul_mem hd₁ hd₂) (D.inv_mem hd₁)) (D.inv_mem hd₂)
  have hπc : π ⁅d₁, d₂⁆ = 1 := by
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (hπab d₁ hd₁.1 d₂ hd₂.1)
  have hcN : ⁅d₁, d₂⁆ ∈ N := hker _ hcD hπc
  have hc' : ⁅d₁, d₂⁻¹⁆ ∈ N := by
    have hD' : ⁅d₁, d₂⁻¹⁆ ∈ D := by
      simp only [commutatorElement_def]
      exact D.mul_mem (D.mul_mem (D.mul_mem hd₁ (D.inv_mem hd₂)) (D.inv_mem hd₁))
        (D.inv_mem (D.inv_mem hd₂))
    refine hker _ hD' ?_
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (hπab d₁ hd₁.1 d₂⁻¹ (X.inv_mem hd₂.1))
  have hρc : ρ * ⁅d₁, d₂⁆ * ρ⁻¹ = ⁅d₁, d₂⁆ := by rw [hRN ρ hρ _ hcN]; group
  have hconj : ρ * ⁅d₁, d₂⁆ * ρ⁻¹ = ⁅ρ * d₁ * ρ⁻¹, ρ * d₂ * ρ⁻¹⁆ := by
    simp only [commutatorElement_def]; group
  have hz₁d₂ : z₁ * (d₂⁻¹ * w₂) = (d₂⁻¹ * w₂) * z₁ :=
    hcen z₁ z₁N _ (D.mul_mem (D.inv_mem hd₂) w₂D)
  have hw₂d₁ : w₂ * d₁ = d₁ * w₂ := hcen w₂ w₂N d₁ hd₁
  have key : ⁅ρ * d₁ * ρ⁻¹, ρ * d₂ * ρ⁻¹⁆ = ⁅d₁, d₂⁻¹⁆ := by
    rw [e₁, e₂, commutator_mul_central_left hz₁d₂, commutator_mul_central_right hw₂d₁]
  have hinvc : ⁅d₁, d₂⁻¹⁆ = ⁅d₁, d₂⁆⁻¹ := by
    have hcomm : d₂ * ⁅d₁, d₂⁻¹⁆ = ⁅d₁, d₂⁻¹⁆ * d₂ := (hcen _ hc' d₂ hd₂).symm
    calc ⁅d₁, d₂⁻¹⁆ = d₂ * ⁅d₁, d₂⁻¹⁆ * d₂⁻¹ := by rw [hcomm]; group
      _ = ⁅d₁, d₂⁆⁻¹ := by simp only [commutatorElement_def]; group
  have hcc : ⁅d₁, d₂⁆ = ⁅d₁, d₂⁆⁻¹ := hρc.symm.trans (hconj.trans (key.trans hinvc))
  have hc2 : ⁅d₁, d₂⁆ ^ 2 = 1 := by
    calc ⁅d₁, d₂⁆ ^ 2 = ⁅d₁, d₂⁆ * ⁅d₁, d₂⁆ := sq _
      _ = ⁅d₁, d₂⁆ * ⁅d₁, d₂⁆⁻¹ := by rw [← hcc]
      _ = 1 := mul_inv_cancel _
  have hc3 : ⁅d₁, d₂⁆ ^ 3 = 1 := by
    have h13 : d₁ ^ 3 ∈ N :=
      hker _ (D.pow_mem hd₁ 3) (by rw [map_pow]; exact hexp d₁ hd₁.1)
    have hcomm13 : Commute d₁ ⁅d₁, d₂⁆ := by
      unfold Commute SemiconjBy
      exact (hcen _ hcN d₁ hd₁).symm
    have := hcomm13.commutatorElement_pow_left 3
    rw [this]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (hcen _ h13 d₂ hd₂)
  have hc1 : ⁅d₁, d₂⁆ = 1 := by
    calc ⁅d₁, d₂⁆ = ⁅d₁, d₂⁆ ^ 3 * (⁅d₁, d₂⁆ ^ 2)⁻¹ := by group
      _ = 1 := by rw [hc3, hc2]; group
  have hd12 : Commute d₁ d₂ := commutatorElement_eq_one_iff_mul_comm.mp hc1
  exact abelian_of_generators π hd₁ hd₂ hd12 hgen

theorem abelian_of_cyclic_image (π : A →* B) {X : Subgroup A}
    (hXD : X ≤ (X ⊓ π.ker) ⊔ (X ⊓ Subgroup.centralizer ((X ⊓ π.ker : Subgroup A) : Set A)))
    (hXN : X ≤ Subgroup.normalizer ((X ⊓ π.ker : Subgroup A) : Set A))
    (hcyc : ∃ γ ∈ X, ∀ x ∈ X, ∃ i : ℕ, π x = π γ ^ i) :
    ∀ a ∈ X ⊓ Subgroup.centralizer ((X ⊓ π.ker : Subgroup A) : Set A),
      ∀ b ∈ X ⊓ Subgroup.centralizer ((X ⊓ π.ker : Subgroup A) : Set A), a * b = b * a := by
  set N : Subgroup A := X ⊓ π.ker with hN
  set D : Subgroup A := X ⊓ Subgroup.centralizer (N : Set A) with hD
  obtain ⟨γ, hγX, hγ⟩ := hcyc
  have hDN : D ≤ Subgroup.normalizer (N : Set A) := inf_le_left.trans hXN
  have hmul : ((N ⊔ D : Subgroup A) : Set A) = (N : Set A) * (D : Set A) :=
    Subgroup.coe_mul_of_right_le_normalizer_left N D hDN
  have hγ' : γ ∈ (N : Set A) * (D : Set A) := by rw [← hmul]; exact hXD hγX
  obtain ⟨n₀, hn₀, d₀, hd₀, rfl⟩ := hγ'
  have hπn₀ : π n₀ = 1 := MonoidHom.mem_ker.mp hn₀.2
  refine abelian_of_generators π (d₁ := d₀) (d₂ := 1) hd₀ D.one_mem (Commute.one_right _) ?_
  intro d hd
  obtain ⟨i, hi⟩ := hγ d hd.1
  exact ⟨i, 0, by rw [hi, map_mul, hπn₀, one_mul]; simp⟩

end CFSG.Quasithin
