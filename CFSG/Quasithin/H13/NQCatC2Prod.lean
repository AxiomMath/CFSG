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
public import Mathlib.GroupTheory.NoncommCoprod
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Order.CompletePartialOrder
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

namespace CFSG.Quasithin.H13.NQCat.C2

open scoped commutatorElement

variable {A : Type*} [Group A]

structure CommPair (Q₁ Q₂ : Subgroup A) : Prop where
  comm : ∀ a ∈ Q₁, ∀ b ∈ Q₂, a * b = b * a
  inf_eq : Q₁ ⊓ Q₂ = ⊥

variable {Q₁ Q₂ : Subgroup A}

theorem CommPair.of_commutator (hc : ⁅Q₁, Q₂⁆ = ⊥) (hi : Q₁ ⊓ Q₂ = ⊥) : CommPair Q₁ Q₂ :=
  ⟨fun a ha b hb => by
    have : ⁅a, b⁆ ∈ ⁅Q₁, Q₂⁆ := Subgroup.commutator_mem_commutator ha hb
    rw [hc, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
    exact this, hi⟩

theorem CommPair.symm (h : CommPair Q₁ Q₂) : CommPair Q₂ Q₁ :=
  ⟨fun a ha b hb => (h.comm b hb a ha).symm, by rw [inf_comm]; exact h.inf_eq⟩

theorem CommPair.eq_of_mul_eq_mul (h : CommPair Q₁ Q₂) {a a' b b' : A} (ha : a ∈ Q₁)
    (ha' : a' ∈ Q₁) (hb : b ∈ Q₂) (hb' : b' ∈ Q₂) (he : a * b = a' * b') : a = a' ∧ b = b' := by
  have h1 : a'⁻¹ * a = b' * b⁻¹ := by
    calc a'⁻¹ * a = a'⁻¹ * (a * b) * b⁻¹ := by group
      _ = a'⁻¹ * (a' * b') * b⁻¹ := by rw [he]
      _ = b' * b⁻¹ := by group
  have h2 : a'⁻¹ * a ∈ Q₁ ⊓ Q₂ :=
    Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem ha') ha, h1 ▸ mul_mem hb' (inv_mem hb)⟩
  rw [h.inf_eq, Subgroup.mem_bot] at h2
  refine ⟨(inv_mul_eq_one.mp h2).symm, ?_⟩
  rw [h2] at h1
  exact (mul_inv_eq_one.mp h1.symm).symm

@[expose] noncomputable def CommPair.mulHom (h : CommPair Q₁ Q₂) : ↥Q₁ × ↥Q₂ →* A :=
  MonoidHom.noncommCoprod Q₁.subtype Q₂.subtype fun a b =>
    (h.comm a a.2 b b.2 : Commute (Q₁.subtype a) (Q₂.subtype b))

theorem CommPair.mulHom_injective (h : CommPair Q₁ Q₂) : Function.Injective h.mulHom := by
  intro x y hxy
  obtain ⟨h1, h2⟩ := h.eq_of_mul_eq_mul x.1.2 y.1.2 x.2.2 y.2.2 hxy
  exact Prod.ext (Subtype.ext h1) (Subtype.ext h2)

theorem CommPair.mulHom_range (h : CommPair Q₁ Q₂) : h.mulHom.range = Q₁ ⊔ Q₂ := by
  have := MonoidHom.noncommCoprod_range Q₁.subtype Q₂.subtype fun a b =>
    (h.comm a a.2 b b.2 : Commute (Q₁.subtype a) (Q₂.subtype b))
  rw [Subgroup.range_subtype, Subgroup.range_subtype] at this
  exact this

theorem CommPair.exists_mul (h : CommPair Q₁ Q₂) {x : A} (hx : x ∈ Q₁ ⊔ Q₂) :
    ∃ a ∈ Q₁, ∃ b ∈ Q₂, x = a * b := by
  rw [← h.mulHom_range] at hx
  obtain ⟨y, rfl⟩ := hx
  exact ⟨y.1, y.1.2, y.2, y.2.2, rfl⟩

@[expose] noncomputable def CommPair.prodEquiv (h : CommPair Q₁ Q₂) :
    ↥Q₁ × ↥Q₂ ≃* ↥(Q₁ ⊔ Q₂) :=
  (MonoidHom.ofInjective h.mulHom_injective).trans (MulEquiv.subgroupCongr h.mulHom_range)

theorem CommPair.coe_prodEquiv (h : CommPair Q₁ Q₂) (x : ↥Q₁ × ↥Q₂) :
    ((h.prodEquiv x : ↥(Q₁ ⊔ Q₂)) : A) = (x.1 : A) * x.2 := rfl

@[expose] noncomputable def CommPair.pr1 (h : CommPair Q₁ Q₂) : ↥(Q₁ ⊔ Q₂) →* A :=
  Q₁.subtype.comp ((MonoidHom.fst _ _).comp h.prodEquiv.symm.toMonoidHom)

@[expose] noncomputable def CommPair.pr2 (h : CommPair Q₁ Q₂) : ↥(Q₁ ⊔ Q₂) →* A :=
  Q₂.subtype.comp ((MonoidHom.snd _ _).comp h.prodEquiv.symm.toMonoidHom)

variable (h : CommPair Q₁ Q₂)
include h

theorem CommPair.pr1_mem (x : ↥(Q₁ ⊔ Q₂)) : h.pr1 x ∈ Q₁ := (h.prodEquiv.symm x).1.2

theorem CommPair.pr2_mem (x : ↥(Q₁ ⊔ Q₂)) : h.pr2 x ∈ Q₂ := (h.prodEquiv.symm x).2.2

theorem CommPair.pr1_mul_pr2 (x : ↥(Q₁ ⊔ Q₂)) : h.pr1 x * h.pr2 x = x := by
  have := h.coe_prodEquiv (h.prodEquiv.symm x)
  rw [MulEquiv.apply_symm_apply] at this
  exact this.symm

theorem CommPair.pr_eq {x : ↥(Q₁ ⊔ Q₂)} {a b : A} (ha : a ∈ Q₁) (hb : b ∈ Q₂)
    (hx : (x : A) = a * b) : h.pr1 x = a ∧ h.pr2 x = b := by
  have h1 := h.pr1_mul_pr2 x
  rw [hx] at h1
  exact h.eq_of_mul_eq_mul (h.pr1_mem x) ha (h.pr2_mem x) hb h1

omit h in
theorem CommPair.le_of_commute (h : CommPair Q₁ Q₂)
    (hZ : ∀ z ∈ Q₁, (∀ a ∈ Q₁, z * a = a * z) → z = 1)
    {N : Subgroup A} (hN : N ≤ Q₁ ⊔ Q₂) (hc : ∀ n ∈ N, ∀ a ∈ Q₁, n * a = a * n) : N ≤ Q₂ := by
  intro n hn
  obtain ⟨a, ha, b, hb, rfl⟩ := h.exists_mul (hN hn)
  have ha1 : a = 1 := by
    apply hZ a ha
    intro c hc'
    have h1 := hc _ hn c hc'
    have h2 : b * c = c * b := (h.comm c hc' b hb).symm
    calc a * c = a * b * c * b⁻¹ := by rw [mul_assoc a b c, h2]; group
      _ = c * (a * b) * b⁻¹ := by rw [h1]
      _ = c * a := by group
  rw [ha1, one_mul]
  exact hb

omit h in
theorem CommPair.eq_or_eq_of_simple (h : CommPair Q₁ Q₂) [IsSimpleGroup ↥Q₁]
    [IsSimpleGroup ↥Q₂] (hZ : ∀ z ∈ Q₁, (∀ a ∈ Q₁, z * a = a * z) → z = 1) {N : Subgroup A}
    [IsSimpleGroup ↥N] (hN : N ≤ Q₁ ⊔ Q₂) (hnorm : Q₁ ⊔ Q₂ ≤ Subgroup.normalizer (N : Set A)) :
    N = Q₁ ∨ N = Q₂ := by
  have hQ₁n : Q₁ ⊔ Q₂ ≤ Subgroup.normalizer (Q₁ : Set A) := by
    rw [sup_le_iff]
    refine ⟨Subgroup.le_normalizer, fun b hb => ?_⟩
    rw [Subgroup.mem_normalizer_iff]
    intro a
    constructor
    · intro ha
      rw [← h.comm a ha b hb, mul_inv_cancel_right]
      exact ha
    · intro ha
      have := h.comm (b * a * b⁻¹) ha b hb
      have e : a = b * a * b⁻¹ := by
        calc a = b⁻¹ * (b * a * b⁻¹ * b) := by group
          _ = b⁻¹ * (b * (b * a * b⁻¹)) := by rw [this]
          _ = b * a * b⁻¹ := by group
      rw [e]
      exact ha
  by_cases hI : N ⊓ Q₁ = ⊥
  ·
    right
    have hc : ∀ n ∈ N, ∀ a ∈ Q₁, n * a = a * n := by
      intro n hn a ha
      have h1 : n * a * n⁻¹ * a⁻¹ ∈ N ⊓ Q₁ := by
        refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
        · have : a * n⁻¹ * a⁻¹ ∈ N :=
            (Subgroup.mem_normalizer_iff.mp (hnorm (Subgroup.mem_sup_left ha)) _).mp
              (inv_mem hn)
          rw [mul_assoc, mul_assoc]
          exact mul_mem hn (by rw [← mul_assoc]; exact this)
        · have : n * a * n⁻¹ ∈ Q₁ :=
            (Subgroup.mem_normalizer_iff.mp (hQ₁n (hN hn)) _).mp ha
          exact mul_mem this (inv_mem ha)
      rw [hI, Subgroup.mem_bot] at h1
      calc n * a = n * a * n⁻¹ * a⁻¹ * (a * n) := by group
        _ = a * n := by rw [h1, one_mul]
    have hle := h.le_of_commute hZ hN hc
    have hNn : (N.subgroupOf Q₂).Normal := ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      exact (Subgroup.mem_normalizer_iff.mp (hnorm (Subgroup.mem_sup_right g.2)) n).mp hn⟩
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.subgroupOf Q₂) with h1 | h1
    · exfalso
      have hNb : N = ⊥ := by
        rw [eq_bot_iff]
        intro x hx
        have : (⟨x, hle hx⟩ : ↥Q₂) ∈ N.subgroupOf Q₂ := Subgroup.mem_subgroupOf.mpr hx
        rw [h1, Subgroup.mem_bot] at this
        rw [Subgroup.mem_bot]
        exact congrArg Subtype.val this
      exact (Subgroup.nontrivial_iff_ne_bot N).mp inferInstance hNb
    · exact le_antisymm hle (Subgroup.subgroupOf_eq_top.mp h1)
  ·
    left
    have hNn : ((N ⊓ Q₁).subgroupOf N).Normal := ⟨fun x hx g => by
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.mp hx
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        exact mul_mem (mul_mem g.2 hx1) (inv_mem g.2)
      · exact (Subgroup.mem_normalizer_iff.mp (hQ₁n (hN g.2)) _).mp hx2⟩
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((N ⊓ Q₁).subgroupOf N) with h1 | h1
    · exfalso
      apply hI
      rw [eq_bot_iff]
      intro x hx
      have : (⟨x, hx.1⟩ : ↥N) ∈ (N ⊓ Q₁).subgroupOf N := Subgroup.mem_subgroupOf.mpr hx
      rw [h1, Subgroup.mem_bot] at this
      rw [Subgroup.mem_bot]
      exact congrArg Subtype.val this
    · have hle : N ≤ Q₁ := fun x hx => by
        have : (⟨x, hx⟩ : ↥N) ∈ (N ⊓ Q₁).subgroupOf N := h1 ▸ Subgroup.mem_top _
        exact (Subgroup.mem_subgroupOf.mp this).2
      have hNn' : (N.subgroupOf Q₁).Normal := ⟨fun n hn g => by
        rw [Subgroup.mem_subgroupOf] at hn ⊢
        exact (Subgroup.mem_normalizer_iff.mp (hnorm (Subgroup.mem_sup_left g.2)) n).mp hn⟩
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.subgroupOf Q₁) with h2 | h2
      · exfalso
        apply hI
        rw [eq_bot_iff]
        intro x hx
        have : (⟨x, hx.2⟩ : ↥Q₁) ∈ N.subgroupOf Q₁ := Subgroup.mem_subgroupOf.mpr hx.1
        rw [h2, Subgroup.mem_bot] at this
        rw [Subgroup.mem_bot]
        exact congrArg Subtype.val this
      · exact le_antisymm hle (Subgroup.subgroupOf_eq_top.mp h2)

end CFSG.Quasithin.H13.NQCat.C2
