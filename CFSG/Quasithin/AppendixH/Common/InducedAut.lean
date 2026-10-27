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

namespace CFSG.ASVolI.AppH

theorem exists_induced_mulAut {K Q : Type*} [Group K] [Group Q] (α : K →* Q)
    (hα : Function.Surjective α) (σ : MulAut K) (hσ : ∀ k, α (σ k) = 1 ↔ α k = 1) :
    ∃ ρ : MulAut Q, ∀ k, ρ (α k) = α (σ k) := by
  have hker : α.ker ≤ (α.comp σ.toMonoidHom).ker := fun k hk => by
    rw [MonoidHom.mem_ker] at hk ⊢
    exact (hσ k).mpr hk
  let f : Q →* Q := MonoidHom.liftOfRightInverse α (Function.surjInv hα)
    (Function.rightInverse_surjInv hα) ⟨α.comp σ.toMonoidHom, hker⟩
  have hf : ∀ k, f (α k) = α (σ k) := fun k =>
    MonoidHom.liftOfRightInverse_comp_apply α (Function.surjInv hα)
      (Function.rightInverse_surjInv hα) ⟨α.comp σ.toMonoidHom, hker⟩ k
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro q hq
    obtain ⟨k, rfl⟩ := hα q
    rw [hf] at hq
    exact (hσ k).mp hq
  have hsurj : Function.Surjective f := by
    intro q
    obtain ⟨k', rfl⟩ := hα q
    obtain ⟨k, rfl⟩ := σ.surjective k'
    exact ⟨α k, hf k⟩
  exact ⟨MulEquiv.ofBijective f ⟨hinj, hsurj⟩, fun k => hf k⟩

theorem exists_hom_induced {K Q Γ : Type*} [Group K] [Group Q] [Group Γ] (α : K →* Q)
    (hα : Function.Surjective α) (ι : Γ →* MulAut K) (hι : ∀ γ k, α (ι γ k) = 1 ↔ α k = 1) :
    ∃ ρ : Γ →* MulAut Q, ∀ γ k, ρ γ (α k) = α (ι γ k) := by
  choose ρ₀ hρ₀ using fun γ => exists_induced_mulAut α hα (ι γ) (hι γ)
  refine ⟨MonoidHom.mk' ρ₀ fun γ γ' => ?_, hρ₀⟩
  ext q
  obtain ⟨k, rfl⟩ := hα q
  rw [MulAut.mul_apply, hρ₀, hρ₀, hρ₀, map_mul, MulAut.mul_apply]

end CFSG.ASVolI.AppH
