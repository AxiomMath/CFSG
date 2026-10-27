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

namespace CFSG.Quasithin

open scoped Matrix

namespace D37Lift

theorem exists_addSection {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (hA : ∀ a : A, a + a = 0) (p : A →+ B) (hp : Function.Surjective p) :
    ∃ s : B →+ A, ∀ b, p (s b) = b := by
  have hA2 : ∀ a : A, (2 : ℕ) • a = 0 := fun a => by rw [two_nsmul]; exact hA a
  have hB2 : ∀ b : B, (2 : ℕ) • b = 0 := by
    intro b
    obtain ⟨a, rfl⟩ := hp b
    rw [← map_nsmul, hA2, map_zero]
  let : Module (ZMod 2) A := AddCommGroup.zmodModule hA2
  let : Module (ZMod 2) B := AddCommGroup.zmodModule hB2
  obtain ⟨s, hs⟩ := LinearMap.exists_rightInverse_of_surjective (p.toZModLinearMap 2)
    (LinearMap.range_eq_top.2 hp)
  exact ⟨s.toAddMonoidHom, fun b => LinearMap.congr_fun hs b⟩

variable {GD GX A R : Type*} {d r : ℕ} [Group GD] [Group GX] [AddCommGroup A] [CommRing R]

structure LiftData (GD GX A R : Type*) (d r : ℕ) [Group GD] [Group GX] [AddCommGroup A]
    [CommRing R] where
  p : A →+ Matrix (Fin d) (Fin r) R
  ρ : GD →* Matrix.GeneralLinearGroup (Fin d) R
  σ : GX →* Matrix.GeneralLinearGroup (Fin r) R
  ag : GD → A →+ A
  ax : GX → A →+ A
  p_surj : Function.Surjective p
  ag_ax : ∀ g x a, ag g (ax x a) = ax x (ag g a)
  ag_fix : ∀ g a, p a = 0 → ag g a = a
  ax_fix : ∀ x a, p a = 0 → ax x a = a
  p_ag : ∀ g a, p (ag g a) = (ρ g : Matrix (Fin d) (Fin d) R) * p a
  p_ax : ∀ x a, p (ax x a) = p a * (σ x : Matrix (Fin r) (Fin r) R)ᵀ

namespace LiftData

variable (E : LiftData GD GX A R d r)

@[expose] def lmul (g : GD) : Matrix (Fin d) (Fin r) R →+ Matrix (Fin d) (Fin r) R :=
  AddMonoidHom.mk' (fun M => (E.ρ g : Matrix (Fin d) (Fin d) R) * M)
    (fun _ _ => Matrix.mul_add _ _ _)

@[expose] def rmul (x : GX) : Matrix (Fin d) (Fin r) R →+ Matrix (Fin d) (Fin r) R :=
  AddMonoidHom.mk' (fun M => M * (E.σ x : Matrix (Fin r) (Fin r) R)ᵀ)
    (fun _ _ => Matrix.add_mul _ _ _)

@[expose] def cochain (s : Matrix (Fin d) (Fin r) R →+ A) (g : GD) :
    Matrix (Fin d) (Fin r) R →+ A :=
  (E.ag g).comp s - s.comp (E.lmul g)

@[expose] def twist (s : Matrix (Fin d) (Fin r) R →+ A) (x : GX) :
    Matrix (Fin d) (Fin r) R →+ A :=
  (E.ax x).comp s - s.comp (E.rmul x)

theorem cochain_apply (s : Matrix (Fin d) (Fin r) R →+ A) (g : GD) (M : Matrix (Fin d) (Fin r) R) :
    E.cochain s g M = E.ag g (s M) - s ((E.ρ g : Matrix (Fin d) (Fin d) R) * M) := rfl

theorem twist_apply (s : Matrix (Fin d) (Fin r) R →+ A) (x : GX) (M : Matrix (Fin d) (Fin r) R) :
    E.twist s x M = E.ax x (s M) - s (M * (E.σ x : Matrix (Fin r) (Fin r) R)ᵀ) := rfl

theorem p_cochain {s : Matrix (Fin d) (Fin r) R →+ A} (hs : ∀ M, E.p (s M) = M) (g : GD)
    (M : Matrix (Fin d) (Fin r) R) : E.p (E.cochain s g M) = 0 := by
  rw [cochain_apply, map_sub, E.p_ag, hs, hs, sub_self]

theorem p_twist {s : Matrix (Fin d) (Fin r) R →+ A} (hs : ∀ M, E.p (s M) = M) (x : GX)
    (M : Matrix (Fin d) (Fin r) R) : E.p (E.twist s x M) = 0 := by
  rw [twist_apply, map_sub, E.p_ax, hs, hs, sub_self]

theorem cochain_sub_cochain {s : Matrix (Fin d) (Fin r) R →+ A} (hs : ∀ M, E.p (s M) = M)
    (g : GD) (x : GX) (M : Matrix (Fin d) (Fin r) R) :
    E.cochain s g M - E.cochain s g (M * (E.σ x : Matrix (Fin r) (Fin r) R)ᵀ) =
      E.twist s x M - E.twist s x ((E.ρ g : Matrix (Fin d) (Fin d) R) * M) := by
  have h1 : E.ag g (E.twist s x M) = E.twist s x M := E.ag_fix g _ (E.p_twist hs x M)
  have h2 : E.ax x (E.cochain s g M) = E.cochain s g M := E.ax_fix x _ (E.p_cochain hs g M)
  rw [twist_apply, map_sub, E.ag_ax] at h1
  rw [cochain_apply, map_sub] at h2
  rw [cochain_apply, cochain_apply, twist_apply, twist_apply, Matrix.mul_assoc]
  linear_combination (norm := abel_nf) h1 - h2

end LiftData

end D37Lift

end CFSG.Quasithin
