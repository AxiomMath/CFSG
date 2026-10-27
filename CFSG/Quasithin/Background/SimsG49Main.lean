module

public import CFSG.Quasithin.Background.SimsG4Defs
import CFSG.Quasithin.Background.SimsG41
import CFSG.Quasithin.Background.SimsG49
import CFSG.Quasithin.Background.SimsG49Orth
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
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

namespace CFSG.Quasithin.SimsG4

theorem g49 {F : Type} [Field F]
    [Finite F] [CharP F 2]
    (n : ℕ) (hn : Nat.card F = 2 ^ n)
    {V : Type} [AddCommGroup V] [Module F V] (B : LinearMap.BilinForm F V)
    (halt : ∀ x, B x x = 0) (hnd : ∀ x, (∀ y, B x y = 0) → x = 0) (hdim : Module.finrank F V = 4)
    (G₀ : Subgroup (V ≃ₗ[F] V)) (hSp : G₀ ≤ spGroup B) (hirr : IsIrredOnV G₀)
    (hD : (transvSet G₀).Nonempty) (hconn : (advGraph G₀).Connected) :
    (IsSimpleGroup ↥(fStarOf (transvGen G₀)) ∧
        (∃ x ∈ fStarOf (transvGen G₀), ∃ y ∈ fStarOf (transvGen G₀), x * y ≠ y * x) ∧
        (∃ i ∈ invSet B G₀, i ∈ fStarOf (transvGen G₀)) ∧
        IsIrredOnV (fStarOf (transvGen G₀))) ∨
      (∃ k : ℕ, 1 < k ∧ k ∣ n ∧
        Nonempty (↥(fStarOf (transvGen G₀)) ≃*
          (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 k) ×
            Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 k))) ∧
        G41Case2AtExponent n k B G₀) := by
  obtain ⟨hirrG, hprimG⟩ := transvGen_irred_prim_of_connected B halt hnd hdim G₀ hSp hirr hD
    (transv_orderOf_two_or_odd B halt hnd hdim G₀ hSp) hconn
  rcases weak_form n hn B halt hnd hdim G₀ hSp hirr hD with
    ⟨b, F₀, hb, hmem⟩ | ⟨Q, hQB, hQ⟩ | ⟨V₁, V₂, h1, h2, h3, hperm⟩
  ·
    have hT : transvGen G₀ = G₀ := (case1_of_subfield n hn B halt hnd hdim G₀ b F₀ hb hmem).1
    exact Or.inl (g49_case1 n hn B halt hnd hdim G₀ hSp hirr (hT ▸ hprimG) hD b F₀ hb hmem)
  ·
    exact G49.orth_case n hn B halt hnd hdim G₀ hSp hirr hD hirrG hprimG Q hQB hQ
  ·
    exact absurd hconn (not_connected_of_imprimitive B halt hnd hdim G₀ hSp hirr hD
      (imprimitive_of_decW B hdim G₀ V₁ V₂ h1 h2 h3 hperm))

end CFSG.Quasithin.SimsG4
