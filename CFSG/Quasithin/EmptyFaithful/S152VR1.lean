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
public import Mathlib.GroupTheory.IsPerfect
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

namespace CFSG.Quasithin.S152V

theorem mulAut_eq_one_of_central {X : Type*} [Group X] (hperf : Group.IsPerfect X) (a : MulAut X)
    (h : ∀ x, x⁻¹ * a x ∈ Subgroup.center X) : a = 1 := by
  let f : X →* Subgroup.center X :=
    { toFun := fun x => ⟨x⁻¹ * a x, h x⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := by
        intro x y
        apply Subtype.ext
        show (x * y)⁻¹ * a (x * y) = (x⁻¹ * a x) * (y⁻¹ * a y)
        have hc := Subgroup.mem_center_iff.1 (h x) y⁻¹
        calc (x * y)⁻¹ * a (x * y) = y⁻¹ * (x⁻¹ * a x) * a y := by rw [map_mul]; group
          _ = (x⁻¹ * a x) * y⁻¹ * a y := by rw [hc]
          _ = (x⁻¹ * a x) * (y⁻¹ * a y) := by rw [mul_assoc] }
  have hker : commutator X ≤ f.ker := Abelianization.commutator_subset_ker f
  rw [hperf.commutator_eq_top, top_le_iff] at hker
  apply MulEquiv.ext
  intro x
  have hx : x ∈ f.ker := hker ▸ Subgroup.mem_top x
  have h1 : x⁻¹ * a x = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hx)
  have h2 : a x = x := by
    calc a x = x * (x⁻¹ * a x) := by group
      _ = x := by rw [h1, mul_one]
  exact h2

@[expose] noncomputable def centerQuotAut (X : Type*) [Group X] :
    MulAut X →* MulAut (X ⧸ Subgroup.center X) where
  toFun a := QuotientGroup.congr (Subgroup.center X) (Subgroup.center X) a (Subgroup.map_center_eq a)
  map_one' := by
    apply MulEquiv.ext
    intro x
    refine QuotientGroup.induction_on x ?_
    intro y
    simp [QuotientGroup.congr]
  map_mul' := by
    intro a b
    apply MulEquiv.ext
    intro x
    refine QuotientGroup.induction_on x ?_
    intro y
    simp [QuotientGroup.congr]

theorem centerQuotAut_apply_mk {X : Type*} [Group X] (a : MulAut X) (x : X) :
    centerQuotAut X a (QuotientGroup.mk x) = QuotientGroup.mk (a x) := rfl

@[expose] noncomputable def inducedAut {X Γ : Type*} [Group X] [Group Γ]
    (ψ : (X ⧸ Subgroup.center X) ≃* Γ) : MulAut X →* MulAut Γ :=
  (MulAut.congr ψ).toMonoidHom.comp (centerQuotAut X)

theorem inducedAut_apply {X Γ : Type*} [Group X] [Group Γ] (ψ : (X ⧸ Subgroup.center X) ≃* Γ)
    (a : MulAut X) (x : X) : inducedAut ψ a (ψ (QuotientGroup.mk x)) = ψ (QuotientGroup.mk (a x)) := by
  simp [inducedAut, centerQuotAut_apply_mk, MulAut.congr_apply]

theorem exists_fixed_subgroup {X : Type*} [Group X] (hperf : Group.IsPerfect X) {Γ : Type*} [Group Γ]
    (ψ : (X ⧸ Subgroup.center X) ≃* Γ) (hZΓ : Subgroup.center Γ = ⊥)
    (hOut : ∀ α : MulAut Γ, α ^ 3 = 1 → ∃ g : Γ, α = MulAut.conj g) {E : Type*} [Group E]
    (hE : ∀ e : E, e ^ 3 = 1) (ρ : E →* MulAut X) (hρ : Function.Injective ρ) (β : MulAut Γ)
    (hβ : ∀ e : E, inducedAut ψ (ρ e) * β = β * inducedAut ψ (ρ e)) :
    ∃ H : Subgroup Γ, Nat.card H = Nat.card E ∧ (∀ g ∈ H, g ^ 3 = 1) ∧ ∀ g ∈ H, β g = g := by
  let ρb : E →* MulAut Γ := (inducedAut ψ).comp ρ
  have hρb_inj : Function.Injective ρb := by
    rw [injective_iff_map_eq_one]
    intro e he
    have hρe : ρ e = 1 := by
      refine mulAut_eq_one_of_central hperf (ρ e) fun x => ?_
      have h1 := congrArg (fun a : MulAut Γ => a (ψ (QuotientGroup.mk x))) he
      simp only [ρb, MonoidHom.comp_apply, inducedAut_apply, MulAut.one_apply] at h1
      have h2 : (QuotientGroup.mk (ρ e x) : X ⧸ Subgroup.center X) = QuotientGroup.mk x :=
        ψ.injective h1
      have h3 := inv_mem (QuotientGroup.eq.1 h2)
      have h4 : ((ρ e x)⁻¹ * x)⁻¹ = x⁻¹ * ρ e x := by group
      rwa [h4] at h3
    exact (injective_iff_map_eq_one ρ).1 hρ e hρe
  have hconjinj : Function.Injective (MulAut.conj : Γ →* MulAut Γ) := by
    rw [injective_iff_map_eq_one]
    intro c hc
    have hcz : c ∈ Subgroup.center Γ := by
      rw [Subgroup.mem_center_iff]
      intro y
      have h := MulEquiv.ext_iff.1 hc y
      simp only [MulAut.conj_apply, MulAut.one_apply] at h
      calc y * c = (c * y * c⁻¹) * c := by rw [h]
        _ = c * y := by group
    rw [hZΓ] at hcz
    exact Subgroup.mem_bot.1 hcz
  have hrange : ∀ e, ρb e ∈ (MulAut.conj : Γ →* MulAut Γ).range := by
    intro e
    obtain ⟨g, hg⟩ := hOut (ρb e) (by rw [← map_pow, hE e, map_one])
    exact ⟨g, hg.symm⟩
  let ρb' : E →* (MulAut.conj : Γ →* MulAut Γ).range := ρb.codRestrict _ hrange
  let eqv : Γ ≃* (MulAut.conj : Γ →* MulAut Γ).range := MonoidHom.ofInjective hconjinj
  let h : E →* Γ := eqv.symm.toMonoidHom.comp ρb'
  have hconj_h : ∀ e, MulAut.conj (h e) = ρb e := by
    intro e
    have h1 : eqv (h e) = ρb' e := by simp [h]
    exact congrArg Subtype.val h1
  have hh_inj : Function.Injective h := by
    intro e₁ e₂ he
    apply hρb_inj
    rw [← hconj_h e₁, ← hconj_h e₂, he]
  refine ⟨h.range, ?_, ?_, ?_⟩
  · exact Nat.card_congr (MonoidHom.ofInjective hh_inj).toEquiv.symm
  · rintro g ⟨e, rfl⟩
    rw [← map_pow, hE e, map_one]
  · rintro g ⟨e, rfl⟩
    apply hconjinj
    apply MulEquiv.ext
    intro w
    obtain ⟨y, rfl⟩ := β.surjective w
    have h1 := MulEquiv.ext_iff.1 (hβ e) y
    have hρbe : inducedAut ψ (ρ e) = MulAut.conj (h e) := (hconj_h e).symm
    rw [hρbe] at h1
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv] at h1 ⊢
    exact h1.symm

end CFSG.Quasithin.S152V
