module

public import CFSG.LocalAnalysis.StandardType.GGE6ThreeCentralizer1585
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeRows1585
public import CFSG.LocalAnalysis.StandardType.GGFamCentralizerBridge

public section

namespace CFSG.StandardType.S2MathAs1E6Companion1625

open CFSG CFSG.Assembly CFSG.StandardType
open CFSG.StandardType.GGK0MarkedKacIface1587
open CFSG.StandardType.E6Centralizer1585
open CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley
open CFSG.LieType.AlgebraicGroups
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

@[expose] noncomputable def conn {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    {lab : LargeEvenLabel} {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
    (ρ : MarkedRationalKacRealization Omega lab p R I phi) : Subgroup (MulAut R) :=
  ((connectedCentralizer ρ ⊓ ρ.setup.D.model).subgroupOf ρ.setup.D.model).map ρ.modelAction

@[expose] noncomputable def innerComponent {Omega : Type} [Field Omega] [IsAlgClosed Omega]
    [CharP Omega 2]
    {lab : LargeEvenLabel} {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
    (ρ : MarkedRationalKacRealization Omega lab p R I phi)
    (j : Fin ρ.row.D.orbits.length) : Subgroup (MulAut R) :=
  (component ρ j).map (MulAut.conj : R →* MulAut R)

@[expose] noncomputable def geomCentralizer {Omega : Type} [Field Omega] [IsAlgClosed Omega]
    [CharP Omega 2]
    {lab : LargeEvenLabel} {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
    (ρ : MarkedRationalKacRealization Omega lab p R I phi) : Subgroup (ModGL ρ.tau Omega) :=
  adjointGroup ρ.tau Omega ⊓
    Subgroup.centralizer ({rootDiagUnit ρ.tau ρ.a} : Set (ModGL ρ.tau Omega))

@[expose] noncomputable def kernelSpan {Omega : Type} [Field Omega] [IsAlgClosed Omega]
    [CharP Omega 2]
    {lab : LargeEvenLabel} {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
    (ρ : MarkedRationalKacRealization Omega lab p R I phi) : Subgroup (ModGL ρ.tau Omega) :=
  rootSpan ρ.tau Omega (kernelRoots (rootCharHom ρ.a))

@[expose] def innerOn {R : Type} [Group R] (D : Subgroup R) (u : MulAut R) : Prop :=
  ∃ d ∈ D, ∀ x ∈ D, u x = d * x * d⁻¹

structure B1At {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    {lab : LargeEvenLabel} {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
    (ρ : MarkedRationalKacRealization Omega lab p R I phi)
    (j : Fin ρ.row.D.orbits.length) (gIndex rIndex : ℕ) : Prop where
  centralizerGroup_eq :
    centralizerGroup ρ =
      ((geomCentralizer ρ ⊓ ρ.setup.D.model).subgroupOf ρ.setup.D.model).map ρ.modelAction
  connectedCentralizer_le : connectedCentralizer ρ ≤ geomCentralizer ρ
  normal_connectedCentralizer :
    ((connectedCentralizer ρ).subgroupOf (geomCentralizer ρ)).Normal
  geometric_relIndex : (connectedCentralizer ρ).relIndex (geomCentralizer ρ) = gIndex
  conn_le : conn ρ ≤ centralizerGroup ρ
  innerComponent_le : innerComponent ρ j ≤ conn ρ
  normal_conn : ((conn ρ).subgroupOf (centralizerGroup ρ)).Normal
  rational_relIndex : (conn ρ).relIndex (centralizerGroup ρ) = rIndex
  invariant_component :
    ∀ u ∈ centralizerGroup ρ, ∀ x : R, x ∈ component ρ j ↔ u x ∈ component ρ j

@[expose] def B3At {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    {lab : LargeEvenLabel} {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
    (ρ : MarkedRationalKacRealization Omega lab p R I phi)
    (j : Fin ρ.row.D.orbits.length) : Prop :=
  ∀ u ∈ centralizerGroup ρ, u ∉ conn ρ → ¬ innerOn (component ρ j) u

structure B1BruhatAt {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    {lab : LargeEvenLabel} {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
    (ρ : MarkedRationalKacRealization Omega lab p R I phi)
    (j : Fin ρ.row.D.orbits.length) : Prop where
  geomCentralizer_eq :
    geomCentralizer ρ =
      (CFSG.StandardType.LayerSixE.famCentralizer
        ({ρ.a} : Set (Fin ρ.tau.rank → Omegaˣ))).map (adjointGroup ρ.tau Omega).subtype
  bruhat :
    ∀ g ∈ geomCentralizer ρ,
      ∃ w ∈ CFSG.RankThree.PartOne.KE8F.famStabilizer
          ({ρ.a} : Set (Fin ρ.tau.rank → Omegaˣ)),
      ∃ h ∈ torusGroup ρ.tau Omega,
      ∃ u ∈ rootSpan ρ.tau Omega
          (CFSG.RankThree.PartOne.KE8F.famKernel
              ({ρ.a} : Set (Fin ρ.tau.rank → Omegaˣ)) ∩
            {α | IsRoot ρ.tau α ∧ 0 < height α}),
      ∃ v ∈ rootSpan ρ.tau Omega
          (CFSG.RankThree.PartOne.KE8F.famKernel
              ({ρ.a} : Set (Fin ρ.tau.rank → Omegaˣ)) ∩
            inversionSet w),
        g = h * u * canonicalRep (coxeterSystem ρ.tau) Omega w * v

@[expose] def B1On (Omega : Type) [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    (row : LargeEvenLabel → LargeEvenLabel → Prop) (gIndex rIndex : ℕ) : Prop :=
  ∀ (lab : LargeEvenLabel) (R : Type) [Group R] (I : Set (MulAut R)) (phi : MulAut R)
    (ρ : MarkedRationalKacRealization Omega lab 3 R I phi)
    (j : Fin ρ.row.D.orbits.length),
    LargeEvenInLambda2 lab → (∀ k, k = j) → ρ.row.D.orbits[j].qs = true →
    row lab ρ.row.D.orbits[j].lab →
    B1At ρ j gIndex rIndex ∧ B1BruhatAt ρ j

@[expose] def B3On (Omega : Type) [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    (row : LargeEvenLabel → LargeEvenLabel → Prop) : Prop :=
  ∀ (lab : LargeEvenLabel) (R : Type) [Group R] (I : Set (MulAut R)) (phi : MulAut R)
    (ρ : MarkedRationalKacRealization Omega lab 3 R I phi)
    (j : Fin ρ.row.D.orbits.length),
    LargeEvenInLambda2 lab → (∀ k, k = j) → ρ.row.D.orbits[j].qs = true →
    row lab ρ.row.D.orbits[j].lab →
    B3At ρ j

end CFSG.StandardType.S2MathAs1E6Companion1625

end
