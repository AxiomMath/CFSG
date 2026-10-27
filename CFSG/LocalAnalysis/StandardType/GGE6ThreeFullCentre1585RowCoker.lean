module

public import CFSG.LocalAnalysis.StandardType.GGE6ThreeFullCentre1585RowTable
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeFullCentre1585NodeIso

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

@[expose] def NodeCokerCyclicR1 : Prop :=
  ∀ {lab : LargeEvenLabel} {p : ℕ} (row : KacRow lab p), row.T = .E6 →
    E6RowDataR1 row.s row.rho → ∀ ε q : ℤ, (ε = 1 ∨ ε = -1) → 2 ≤ q →
      Finite (nodeCoker row ε q) ∧ IsAddCyclic (nodeCoker row ε q)

@[expose] def NodeCokerCyclicR3 : Prop :=
  ∀ {lab : LargeEvenLabel} {p : ℕ} (row : KacRow lab p), row.T = .E6 →
    E6RowDataR3 row.s row.rho → ∀ ε q : ℤ, (ε = 1 ∨ ε = -1) → 2 ≤ q →
      Finite (nodeCoker row ε q) ∧ IsAddCyclic (nodeCoker row ε q)

@[expose] def NodeCokerCyclicR4 : Prop :=
  ∀ {lab : LargeEvenLabel} {p : ℕ} (row : KacRow lab p), row.T = .E6 →
    E6RowDataR4 row.s row.rho → ∀ ε q : ℤ, (ε = 1 ∨ ε = -1) → 2 ≤ q →
      Finite (nodeCoker row ε q) ∧ IsAddCyclic (nodeCoker row ε q)

@[expose] def NodeCokerCyclicR16 : Prop :=
  ∀ {lab : LargeEvenLabel} {p : ℕ} (row : KacRow lab p), row.T = .E6 →
    E6RowDataR16 row.s row.rho → ∀ ε q : ℤ, (ε = 1 ∨ ε = -1) → 2 ≤ q →
      Finite (nodeCoker row ε q) ∧ IsAddCyclic (nodeCoker row ε q)

@[expose] def NodeCokerCyclicR4Opp : Prop :=
  ∀ {lab : LargeEvenLabel} {p : ℕ} (row : KacRow lab p), row.T = .E6 →
    E6RowDataR4Opp row.s row.rho → ∀ ε q : ℤ, (ε = 1 ∨ ε = -1) → 2 ≤ q →
      Finite (nodeCoker row ε q) ∧ IsAddCyclic (nodeCoker row ε q)

@[expose] def NodeCokerCyclicR16Opp : Prop :=
  ∀ {lab : LargeEvenLabel} {p : ℕ} (row : KacRow lab p), row.T = .E6 →
    E6RowDataR16Opp row.s row.rho → ∀ ε q : ℤ, (ε = 1 ∨ ε = -1) → 2 ≤ q →
      Finite (nodeCoker row ε q) ∧ IsAddCyclic (nodeCoker row ε q)

theorem e6RowCokerCyclic_of_pieces
    (Omega : Type) [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    (row : LargeEvenLabel → LargeEvenLabel → Prop) (Data : List ℕ → List ℕ → Prop)
    (hD : ∀ (lab : LargeEvenLabel) (R : Type) [Group R] (I : Set (MulAut R)) (phi : MulAut R)
      (ρ : MarkedRationalKacRealization Omega lab 3 R I phi) (j : Fin ρ.row.D.orbits.length),
      LargeEvenInLambda2 lab → (∀ k, k = j) → ρ.row.D.orbits[j].qs = true →
      row lab ρ.row.D.orbits[j].lab → ρ.row.T = .E6 ∧ Data ρ.row.s ρ.row.rho)
    (hC : ∀ {lab : LargeEvenLabel} {p : ℕ} (r : KacRow lab p), r.T = .E6 → Data r.s r.rho →
      ∀ ε q : ℤ, (ε = 1 ∨ ε = -1) → 2 ≤ q →
        Finite (nodeCoker r ε q) ∧ IsAddCyclic (nodeCoker r ε q)) :
    E6RowCokerCyclic Omega row := by
  intro lab R _ I phi ρ j hlab hj hqs hrow
  obtain ⟨hT, hdata⟩ := hD lab R I phi ρ j hlab hj hqs hrow
  obtain ⟨e⟩ := coker_equiv_nodeCoker ρ
  have hε : ρ.epsilon = 1 ∨ ρ.epsilon = -1 := by
    rw [ρ.epsilon_eq]
    split_ifs <;> simp
  have hq : (2 : ℤ) ≤ ((2 ^ lab.n : ℕ) : ℤ) := by
    have h1 : 1 ≤ lab.n := hlab.1
    have h2 : 2 ^ 1 ≤ 2 ^ lab.n := Nat.pow_le_pow_right (by norm_num) h1
    exact_mod_cast h2
  obtain ⟨hfin, hcyc⟩ := hC ρ.row hT hdata ρ.epsilon _ hε hq
  haveI := hfin
  exact ⟨Finite.of_equiv _ e.symm.toEquiv, (AddEquiv.isAddCyclic e).mpr hcyc⟩

theorem e6RowCokerCyclicR1_of_pieces
    (Omega : Type) [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    (hD : E6RowTableR1) (hC : NodeCokerCyclicR1) :
    E6RowCokerCyclic Omega GGE6ThreeR1Labels1585 :=
  e6RowCokerCyclic_of_pieces Omega _ E6RowDataR1
    (fun lab R _ I phi ρ j h1 h2 h3 h4 => hD lab R I phi ρ j h1 h2 h3 h4) hC

theorem e6RowCokerCyclicR3_of_pieces
    (Omega : Type) [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    (hD : E6RowTableR3) (hC : NodeCokerCyclicR3) :
    E6RowCokerCyclic Omega GGE6ThreeR3Labels1585 :=
  e6RowCokerCyclic_of_pieces Omega _ E6RowDataR3
    (fun lab R _ I phi ρ j h1 h2 h3 h4 => hD lab R I phi ρ j h1 h2 h3 h4) hC

theorem e6RowCokerCyclicR4_of_pieces
    (Omega : Type) [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    (hD : E6RowTableR4) (hC : NodeCokerCyclicR4) :
    E6RowCokerCyclic Omega GGE6ThreeR4Labels1585 :=
  e6RowCokerCyclic_of_pieces Omega _ E6RowDataR4
    (fun lab R _ I phi ρ j h1 h2 h3 h4 => hD lab R I phi ρ j h1 h2 h3 h4) hC

theorem e6RowCokerCyclicR16_of_pieces
    (Omega : Type) [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    (hD : E6RowTableR16) (hC : NodeCokerCyclicR16) :
    E6RowCokerCyclic Omega GGE6ThreeR16Labels1585 :=
  e6RowCokerCyclic_of_pieces Omega _ E6RowDataR16
    (fun lab R _ I phi ρ j h1 h2 h3 h4 => hD lab R I phi ρ j h1 h2 h3 h4) hC

theorem e6RowCokerCyclicR4Opp_of_pieces
    (Omega : Type) [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    (hD : E6RowTableR4Opp) (hC : NodeCokerCyclicR4Opp) :
    E6RowCokerCyclic Omega GGE6ThreeR4OppLabels1585 :=
  e6RowCokerCyclic_of_pieces Omega _ E6RowDataR4Opp
    (fun lab R _ I phi ρ j h1 h2 h3 h4 => hD lab R I phi ρ j h1 h2 h3 h4) hC

theorem e6RowCokerCyclicR16Opp_of_pieces
    (Omega : Type) [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    (hD : E6RowTableR16Opp) (hC : NodeCokerCyclicR16Opp) :
    E6RowCokerCyclic Omega GGE6ThreeR16OppLabels1585 :=
  e6RowCokerCyclic_of_pieces Omega _ E6RowDataR16Opp
    (fun lab R _ I phi ρ j h1 h2 h3 h4 => hD lab R I phi ρ j h1 h2 h3 h4) hC

end CFSG.StandardType.E6Centralizer1585

end
