module

public import CFSG.LocalAnalysis.StandardType.GGK0MarkedKacIface1587

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

@[expose] noncomputable def innDiag {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    {lab : LargeEvenLabel} {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
    (ρ : MarkedRationalKacRealization Omega lab p R I phi) : Subgroup (MulAut R) :=
  ρ.modelAction.range

@[expose]
noncomputable def centralizerGroup {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    {lab : LargeEvenLabel} {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
    (ρ : MarkedRationalKacRealization Omega lab p R I phi) : Subgroup (MulAut R) :=
  innDiag ρ ⊓ Subgroup.centralizer ({phi} : Set (MulAut R))

@[expose]
noncomputable def component {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    {lab : LargeEvenLabel} {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
    (ρ : MarkedRationalKacRealization Omega lab p R I phi)
    (j : Fin ρ.row.D.orbits.length) : Subgroup R :=
  coreFactor ρ.setup ρ.iota ρ.a (ρ.repr j)

@[expose] noncomputable def connectedCentralizer {Omega : Type} [Field Omega] [IsAlgClosed Omega]
    [CharP Omega 2]
    {lab : LargeEvenLabel} {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
    (ρ : MarkedRationalKacRealization Omega lab p R I phi) : Subgroup (ModGL ρ.tau Omega) :=
  Subgroup.closure (Set.range (fun b : Fin ρ.tau.rank → Omegaˣ => rootDiagUnit ρ.tau b)) ⊔
    rootSpan ρ.tau Omega (kernelRoots (rootCharHom ρ.a))

@[expose]
noncomputable def connectedCentre {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    {lab : LargeEvenLabel} {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
    (ρ : MarkedRationalKacRealization Omega lab p R I phi) : Subgroup (ModGL ρ.tau Omega) :=
  (Subgroup.center (connectedCentralizer ρ)).map (connectedCentralizer ρ).subtype

@[expose]
noncomputable def fullCentre {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    {lab : LargeEvenLabel} {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
    (ρ : MarkedRationalKacRealization Omega lab p R I phi) : Subgroup (MulAut R) :=
  ((connectedCentre ρ ⊓ ρ.setup.D.model).subgroupOf ρ.setup.D.model).map ρ.modelAction

@[expose] def MarkedCentreExplicit1585 (Omega : Type) [Field Omega] [IsAlgClosed Omega]
    [CharP Omega 2] : Prop :=
  ∀ (lab : LargeEvenLabel) (p : ℕ) (R : Type) [Group R] (I : Set (MulAut R)) (phi : MulAut R)
    (ρ : MarkedRationalKacRealization Omega lab p R I phi) (g : ModGL ρ.tau Omega),
    (g ∈ connectedCentre ρ ∧ g ∈ ρ.setup.D.model) ↔
      (g ∈ ρ.setup.D.model ∧ ∃ b : Fin ρ.tau.rank → Omegaˣ, rootDiagUnit ρ.tau b = g ∧
        ∀ v ∈ kernelRoots (rootCharHom ρ.a), rootChar b v = 1)

@[expose] def GGE6ThreeCompanionOn1585 (Omega : Type) [Field Omega] [IsAlgClosed Omega]
    [CharP Omega 2]
    (row : LargeEvenLabel → LargeEvenLabel → Prop) : Prop :=
  ∀ (lab : LargeEvenLabel) (R : Type) [Group R] (I : Set (MulAut R)) (phi : MulAut R)
    (ρ : MarkedRationalKacRealization Omega lab 3 R I phi)
    (j : Fin ρ.row.D.orbits.length),
    LargeEvenInLambda2 lab → (∀ k, k = j) → ρ.row.D.orbits[j].qs = true →
    row lab ρ.row.D.orbits[j].lab →
    Subgroup.center (component ρ j) = ⊥ ∧
    ∀ u ∈ centralizerGroup ρ,
      (∃ d ∈ component ρ j, ∀ x ∈ component ρ j, u x = d * x * d⁻¹) ↔
        ∃ d ∈ component ρ j, ∃ s ∈ fullCentre ρ, u = MulAut.conj d * s

@[expose] def GGE6ThreeFullCentreCyclicOn1585 (Omega : Type) [Field Omega] [IsAlgClosed Omega]
    [CharP Omega 2]
    (row : LargeEvenLabel → LargeEvenLabel → Prop) : Prop :=
  ∀ (lab : LargeEvenLabel) (R : Type) [Group R] (I : Set (MulAut R)) (phi : MulAut R)
    (ρ : MarkedRationalKacRealization Omega lab 3 R I phi)
    (j : Fin ρ.row.D.orbits.length),
    LargeEvenInLambda2 lab → (∀ k, k = j) → ρ.row.D.orbits[j].qs = true →
    row lab ρ.row.D.orbits[j].lab → IsCyclic (fullCentre ρ)

end CFSG.StandardType.E6Centralizer1585

end
