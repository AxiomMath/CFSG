module

public import CFSG.Quasithin.Background.A3ComponentsCore
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.F1Models
public import CFSG.Quasithin.H13.Statements
public import CFSG.Quasithin.H13.U3Basic
public import CFSG.Quasithin.SteinbergCBU3Frame
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.U3

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.SteinbergCB
open scoped IsMulCommutative

@[expose] def U3LineComponentExclusion : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (z : G) [IsElementaryAbelian 2 V],
    QTH13 G T L → LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1 → QTU3InternalFrame T L V z →
    ∀ b : LinearMap.BilinForm (ZMod 2) (Additive V), b.Nondegenerate → b.IsAlt →
      (∀ (n : normalizer (V : Set G)) (x y : Additive V),
        b (u3ConjLin V _ le_rfl n x) (u3ConjLin V _ le_rfl n y) = b x y) →
      ∀ (u v : G) (hu : u ∈ V) (hv : v ∈ V),
        b (Additive.ofMul ⟨u, hu⟩) (Additive.ofMul ⟨v, hv⟩) ≠ 0 →
        ∀ K ∈ cComp (centralizer ({u, v} : Set G)),
          CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) → K ≤ normalizer (L : Set G)

end CFSG.Quasithin.H13.U3
