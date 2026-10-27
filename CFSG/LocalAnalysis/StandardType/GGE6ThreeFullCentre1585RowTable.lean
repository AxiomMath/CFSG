module

public import CFSG.LocalAnalysis.StandardType.GGE6ThreeFullCentre1585NodeDefs
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeRows1585

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

@[expose] def E6RowDataR1 (s rho : List ℕ) : Prop :=
  (s = [0, 1, 0, 0, 0, 0, 2] ∨ s = [0, 2, 0, 0, 0, 0, 1]) ∧ (rho = [0, 1, 2, 3, 4, 5, 6])

@[expose] def E6RowTableR1 : Prop :=
  ∀ {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    (lab : LargeEvenLabel) (R : Type) [Group R] (I : Set (MulAut R)) (phi : MulAut R)
    (ρ : MarkedRationalKacRealization Omega lab 3 R I phi)
    (j : Fin ρ.row.D.orbits.length),
    LargeEvenInLambda2 lab → (∀ k, k = j) → ρ.row.D.orbits[j].qs = true →
    GGE6ThreeR1Labels1585 lab ρ.row.D.orbits[j].lab →
    ρ.row.T = .E6 ∧ E6RowDataR1 ρ.row.s ρ.row.rho

@[expose] def E6RowDataR3 (s rho : List ℕ) : Prop :=
  (s = [0, 0, 0, 0, 1, 0, 0]) ∧ (rho = [1, 6, 3, 5, 4, 2, 0] ∨ rho = [6, 0, 5, 2, 4, 3, 1])

@[expose] def E6RowTableR3 : Prop :=
  ∀ {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    (lab : LargeEvenLabel) (R : Type) [Group R] (I : Set (MulAut R)) (phi : MulAut R)
    (ρ : MarkedRationalKacRealization Omega lab 3 R I phi)
    (j : Fin ρ.row.D.orbits.length),
    LargeEvenInLambda2 lab → (∀ k, k = j) → ρ.row.D.orbits[j].qs = true →
    GGE6ThreeR3Labels1585 lab ρ.row.D.orbits[j].lab →
    ρ.row.T = .E6 ∧ E6RowDataR3 ρ.row.s ρ.row.rho

@[expose] def E6RowDataR4 (s rho : List ℕ) : Prop :=
  (s = [0, 0, 0, 0, 0, 1, 1]) ∧ (rho = [0, 1, 2, 3, 4, 5, 6])

@[expose] def E6RowTableR4 : Prop :=
  ∀ {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    (lab : LargeEvenLabel) (R : Type) [Group R] (I : Set (MulAut R)) (phi : MulAut R)
    (ρ : MarkedRationalKacRealization Omega lab 3 R I phi)
    (j : Fin ρ.row.D.orbits.length),
    LargeEvenInLambda2 lab → (∀ k, k = j) → ρ.row.D.orbits[j].qs = true →
    GGE6ThreeR4Labels1585 lab ρ.row.D.orbits[j].lab →
    ρ.row.T = .E6 ∧ E6RowDataR4 ρ.row.s ρ.row.rho

@[expose] def E6RowDataR16 (s rho : List ℕ) : Prop :=
  (s = [1, 1, 0, 0, 0, 0, 1]) ∧ (rho = [1, 6, 3, 5, 4, 2, 0] ∨ rho = [6, 0, 5, 2, 4, 3, 1])

@[expose] def E6RowTableR16 : Prop :=
  ∀ {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    (lab : LargeEvenLabel) (R : Type) [Group R] (I : Set (MulAut R)) (phi : MulAut R)
    (ρ : MarkedRationalKacRealization Omega lab 3 R I phi)
    (j : Fin ρ.row.D.orbits.length),
    LargeEvenInLambda2 lab → (∀ k, k = j) → ρ.row.D.orbits[j].qs = true →
    GGE6ThreeR16Labels1585 lab ρ.row.D.orbits[j].lab →
    ρ.row.T = .E6 ∧ E6RowDataR16 ρ.row.s ρ.row.rho

@[expose] def E6RowDataR4Opp (s rho : List ℕ) : Prop :=
  (s = [0, 0, 0, 0, 0, 1, 1]) ∧ (rho = [1, 0, 3, 2, 4, 5, 6])

@[expose] def E6RowTableR4Opp : Prop :=
  ∀ {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    (lab : LargeEvenLabel) (R : Type) [Group R] (I : Set (MulAut R)) (phi : MulAut R)
    (ρ : MarkedRationalKacRealization Omega lab 3 R I phi)
    (j : Fin ρ.row.D.orbits.length),
    LargeEvenInLambda2 lab → (∀ k, k = j) → ρ.row.D.orbits[j].qs = true →
    GGE6ThreeR4OppLabels1585 lab ρ.row.D.orbits[j].lab →
    ρ.row.T = .E6 ∧ E6RowDataR4Opp ρ.row.s ρ.row.rho

@[expose] def E6RowDataR16Opp (s rho : List ℕ) : Prop :=
  (s = [1, 1, 0, 0, 0, 0, 1]) ∧ (rho = [0, 6, 2, 5, 4, 3, 1])

@[expose] def E6RowTableR16Opp : Prop :=
  ∀ {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    (lab : LargeEvenLabel) (R : Type) [Group R] (I : Set (MulAut R)) (phi : MulAut R)
    (ρ : MarkedRationalKacRealization Omega lab 3 R I phi)
    (j : Fin ρ.row.D.orbits.length),
    LargeEvenInLambda2 lab → (∀ k, k = j) → ρ.row.D.orbits[j].qs = true →
    GGE6ThreeR16OppLabels1585 lab ρ.row.D.orbits[j].lab →
    ρ.row.T = .E6 ∧ E6RowDataR16Opp ρ.row.s ρ.row.rho

end CFSG.StandardType.E6Centralizer1585

end
