module

public import CFSG.LocalAnalysis.StandardType.GGE6ThreeFullCentre1585Defs

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

abbrev NodeLat {lab : LargeEvenLabel} {p : ℕ} (row : KacRow lab p) : Type :=
  Fin row.diagram.marks.length → ℤ

@[expose] def nodeMarks {lab : LargeEvenLabel} {p : ℕ} (row : KacRow lab p) : NodeLat row :=
  fun i => (row.diagram.marks.getD i.val 0 : ℤ)

@[expose] def nodePermMap {lab : LargeEvenLabel} {p : ℕ} (row : KacRow lab p) :
    NodeLat row →ₗ[ℤ] NodeLat row :=
  LinearMap.funLeft ℤ ℤ row.nodePerm.symm

@[expose] def zeroNodeLattice {lab : LargeEvenLabel} {p : ℕ} (row : KacRow lab p) :
    Submodule ℤ (NodeLat row) :=
  Submodule.span ℤ {v | ∃ i : Fin row.diagram.marks.length,
    row.s.getD i.val 0 = 0 ∧ v = Pi.single i 1}

@[expose] def nodeDefect {lab : LargeEvenLabel} {p : ℕ} (row : KacRow lab p) (ε q : ℤ) :
    Submodule ℤ (NodeLat row) :=
  LinearMap.range (ε • nodePermMap row - q • LinearMap.id)

@[expose] def nodeSub {lab : LargeEvenLabel} {p : ℕ} (row : KacRow lab p) (ε q : ℤ) :
    Submodule ℤ (NodeLat row) :=
  Submodule.span ℤ {nodeMarks row} ⊔ zeroNodeLattice row ⊔ nodeDefect row ε q

abbrev nodeCoker {lab : LargeEvenLabel} {p : ℕ} (row : KacRow lab p) (ε q : ℤ) :
    Type :=
  NodeLat row ⧸ nodeSub row ε q

end CFSG.StandardType.E6Centralizer1585

end
