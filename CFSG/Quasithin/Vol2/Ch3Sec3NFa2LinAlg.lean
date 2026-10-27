module

public import Mathlib.Algebra.Module.StablyFree.Basic
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
public import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.Quasithin.H13.NFa2

theorem finrank_le_card_mul_of_closure_eq_top {Γ : Type} [Group Γ]
    {X : Type} [AddCommGroup X] [Module (ZMod 2) X] [Finite X]
    (ρ : Γ →* (X ≃ₗ[ZMod 2] X)) (hfix : ∀ x : X, (∀ g, ρ g x = x) → x = 0)
    (S : Finset Γ) (hS : Subgroup.closure (S : Set Γ) = ⊤) (c : Γ)
    (hconj : ∀ s ∈ S, IsConj c s) :
    Module.finrank (ZMod 2) X ≤
      S.card * Module.finrank (ZMod 2) (LinearMap.range ((ρ c).toLinearMap - LinearMap.id)) := by
  haveI : Module.Finite (ZMod 2) X := Module.finite_iff_finite.mpr inferInstance
  obtain ⟨T, hT⟩ : ∃ T : Γ → Module.End (ZMod 2) X,
      ∀ s, T s = (ρ s).toLinearMap - LinearMap.id :=
    ⟨fun s => (ρ s).toLinearMap - LinearMap.id, fun s => rfl⟩
  rw [← hT c]
  have hTapp : ∀ s x, T s x = ρ s x - x := fun s x => by simp [hT]
  have hmul : ∀ (a b : Γ) (x : X), ρ (a * b) x = ρ a (ρ b x) := fun a b x => by
    rw [map_mul] <;> rfl
  have hinv1 : ∀ (h : Γ) (x : X), ρ h (ρ h⁻¹ x) = x := fun h x => by
    rw [← hmul, mul_inv_cancel, map_one] <;> rfl
  have hinv2 : ∀ (h : Γ) (x : X), ρ h⁻¹ (ρ h x) = x := fun h x => by
    rw [← hmul, inv_mul_cancel, map_one] <;> rfl
  have hrange : ∀ s ∈ S, Module.finrank (ZMod 2) (LinearMap.range (T s)) =
      Module.finrank (ZMod 2) (LinearMap.range (T c)) := by
    intro s hs
    obtain ⟨g, hg⟩ := isConj_iff.mp (hconj s hs)
    subst hg
    have hTs : ∀ x, T (g * c * g⁻¹) x = ρ g (T c (ρ g⁻¹ x)) := by
      intro x
      rw [hTapp, hTapp, map_sub, hinv1, hmul, hmul]
    have hrng : LinearMap.range (T (g * c * g⁻¹)) =
        (LinearMap.range (T c)).map (ρ g).toLinearMap := by
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨T c (ρ g⁻¹ x), ⟨ρ g⁻¹ x, rfl⟩, (hTs x).symm⟩
      · rintro ⟨z, ⟨w, rfl⟩, rfl⟩
        exact ⟨ρ g w, by simp only [hTs, hinv2, LinearEquiv.coe_toLinearMap]⟩
    rw [hrng, LinearEquiv.finrank_map_eq]
  have hquot : ∀ s ∈ S, Module.finrank (ZMod 2) (X ⧸ LinearMap.ker (T s)) =
      Module.finrank (ZMod 2) (LinearMap.range (T c)) := fun s hs => by
    rw [(LinearMap.quotKerEquivRange (T s)).finrank_eq, hrange s hs]
  have hL : Function.Injective
      (LinearMap.pi fun s : S => (LinearMap.ker (T s)).mkQ) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have hfixS : ∀ s ∈ S, ρ s x = x := by
      intro s hs
      have h := congrFun hx ⟨s, hs⟩
      simp only [LinearMap.pi_apply, Pi.zero_apply, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero, LinearMap.mem_ker, hTapp, sub_eq_zero] at h
      exact h
    have hcl : ∀ g ∈ Subgroup.closure (S : Set Γ), ρ g x = x := by
      intro g hg
      refine Subgroup.closure_induction (p := fun g _ => ρ g x = x) ?_ ?_ ?_ ?_ hg
      · intro s hs
        exact hfixS s hs
      · show ρ 1 x = x
        simp
      · intro a b _ _ ha hb
        have ha' : ρ a x = x := ha
        have hb' : ρ b x = x := hb
        show ρ (a * b) x = x
        rw [hmul, hb', ha']
      · intro a _ ha
        have ha' : ρ a x = x := ha
        show ρ a⁻¹ x = x
        have h := hinv2 a x
        rw [ha'] at h
        exact h
    have hall : ∀ g : Γ, ρ g x = x := fun g =>
      hcl g (by rw [hS]; exact Subgroup.mem_top g)
    exact hfix x hall
  have hcount : Module.finrank (ZMod 2) (∀ s : S, X ⧸ LinearMap.ker (T s)) =
      S.card * Module.finrank (ZMod 2) (LinearMap.range (T c)) := by
    have hs : ∀ s : S, Module.finrank (ZMod 2) (X ⧸ LinearMap.ker (T s)) =
        Module.finrank (ZMod 2) (LinearMap.range (T c)) := fun s => hquot s s.2
    rw [Module.finrank_pi_fintype]
    simp only [hs, Finset.sum_const, Finset.card_univ, Fintype.card_coe, smul_eq_mul]
  have hle := LinearMap.finrank_le_finrank_of_injective hL
  rw [hcount] at hle
  exact hle

end CFSG.Quasithin.H13.NFa2
