module

public import CFSG.LocalAnalysis.StandardType.PhanEStdFrob

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.LieType.Universal CFSG.LieType.RootSystem

structure ChevModel2 {K : Type*} [Group K] (D : UniversalRootDatum K) (n : Fin D.rank → K)
    (H : Fin D.rank → Subgroup K) (Fld : Type) [Field Fld] where
  x : (Fin D.rank → ℤ) → Fld → K
  x_mem : ∀ γ ∈ D.roots, ∀ g, g ∈ D.rootGroup γ ↔ ∃ c, x γ c = g
  x_add : ∀ γ ∈ D.roots, ∀ c d, x γ (c + d) = x γ c * x γ d
  x_inj : ∀ γ ∈ D.roots, Function.Injective (x γ)
  nm_conj : ∀ i, ∀ γ ∈ D.roots, ∀ c,
    n i * x γ c * (n i)⁻¹ =
      x (weylAction D.isFiniteType ((coxeterMatrix D.isFiniteType).toCoxeterSystem.simple i) γ) c
  nm_sq : ∀ i, n i * n i = 1
  hh : Fin D.rank → (Fldˣ →* K)
  hh_range : ∀ i, (hh i).range = H i
  hh_conj : ∀ i (t : Fldˣ), ∀ γ ∈ D.roots, ∀ c,
    hh i t * x γ c * (hh i t)⁻¹ = x γ (((t ^ (∑ j, D.cartan i j * γ j) : Fldˣ) : Fld) * c)
  nm_def : ∀ i, n i =
    x (Pi.single i 1) 1 * x (-Pi.single i 1) (-1) * x (Pi.single i 1) 1
  hh_def : ∀ i (t : Fldˣ), hh i t =
    (x (Pi.single i 1) t * x (-Pi.single i 1) (-((t⁻¹ : Fldˣ) : Fld)) * x (Pi.single i 1) t) *
      (n i)⁻¹

structure ChevModel2.PhiCompat {K : Type*} [Group K] {D : UniversalRootDatum K}
    {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K} {Fld : Type} [Field Fld]
    (M : ChevModel2 D n H Fld) {w₀ : (coxeterMatrix D.isFiniteType).Group}
    (F : FrobData D n H w₀) (θ : Fld →+* Fld) where
  ρ : (Fin D.rank → ℤ) → (Fin D.rank → ℤ)
  ρ_single : ∀ i, ρ (Pi.single i 1) = Pi.single (F.op i) 1
  ρ_mem : ∀ γ ∈ D.roots, ρ γ ∈ D.roots
  phi_x : ∀ γ ∈ D.roots, ∀ c, F.φ (M.x γ c) = M.x (ρ γ) (θ c)

end CFSG.ClassicalInvolution.Phan.PhanE
