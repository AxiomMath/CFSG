module

public import CFSG.LocalAnalysis.StandardType.GGE6ThreeCentralizer1585

public section

namespace CFSG.StandardType.E6Centralizer1585

open CFSG CFSG.Assembly CFSG.StandardType
open CFSG.StandardType.GGK0MarkedKacIface1587
open CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley
open CFSG.LieType.AlgebraicGroups
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

@[expose] def charKilled (τ : Tag) (Omega : Type) [Field Omega]
    (N : Submodule ℤ (Fin τ.rank → ℤ)) : Subgroup (Fin τ.rank → Omegaˣ) where
  carrier := {b | ∀ v ∈ N, rootChar b v = 1}
  mul_mem' := by
    intro a b ha hb v hv
    have h : rootChar (a * b) v = rootChar a v * rootChar b v := by
      simp only [rootChar, Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib]
    rw [h, ha v hv, hb v hv, mul_one]
  one_mem' := by
    intro v _
    simp [rootChar]
  inv_mem' := by
    intro a ha v hv
    have h : rootChar a⁻¹ v = (rootChar a v)⁻¹ := by
      simp only [rootChar, Pi.inv_apply, inv_zpow', zpow_neg, Finset.prod_inv_distrib]
    rw [h, ha v hv, inv_one]

@[expose] def kernelLattice
    {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    {lab : LargeEvenLabel} {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
    (ρ : MarkedRationalKacRealization Omega lab p R I phi) :
    Submodule ℤ (Fin ρ.tau.rank → ℤ) :=
  Submodule.span ℤ (kernelRoots (rootCharHom ρ.a))

@[expose] def frobDefect
    {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    {lab : LargeEvenLabel} {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
    (ρ : MarkedRationalKacRealization Omega lab p R I phi) :
    Submodule ℤ (Fin ρ.tau.rank → ℤ) :=
  LinearMap.range (ρ.frobLinear.toLinearMap - ((2 ^ lab.n : ℕ) : ℤ) • LinearMap.id)

@[expose] def E6RowCokerCyclic (Omega : Type) [Field Omega] [IsAlgClosed Omega]
    [CharP Omega 2]
    (row : LargeEvenLabel → LargeEvenLabel → Prop) : Prop :=
  ∀ (lab : LargeEvenLabel) (R : Type) [Group R] (I : Set (MulAut R)) (phi : MulAut R)
    (ρ : MarkedRationalKacRealization Omega lab 3 R I phi)
    (j : Fin ρ.row.D.orbits.length),
    LargeEvenInLambda2 lab → (∀ k, k = j) → ρ.row.D.orbits[j].qs = true →
    row lab ρ.row.D.orbits[j].lab →
    Finite ((Fin ρ.tau.rank → ℤ) ⧸ (kernelLattice ρ ⊔ frobDefect ρ)) ∧
      IsAddCyclic ((Fin ρ.tau.rank → ℤ) ⧸ (kernelLattice ρ ⊔ frobDefect ρ))

end CFSG.StandardType.E6Centralizer1585

end
