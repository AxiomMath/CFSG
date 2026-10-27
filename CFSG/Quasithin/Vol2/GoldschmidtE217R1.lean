module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.GLS.IVK.Statements.Sec1
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasicBase
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.E2Pair
public import CFSG.Quasithin.Vol2.Ch3E213MG41W
public import CFSG.Quasithin.Vol2.Ch3E213MOLFacts
public import CFSG.Quasithin.Vol2.Ch3E213MP6BD

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique B6 E2 Ch3E213M CFSG.GH74.GLS.IVK CFSG.GH74.GLS

namespace E217R1

structure R1Leaves : Prop where
  a38 : CFSG.QuasithinUnique.Vol2Native.A38ForSQTKCat
  irr : IrrStatement
  g41 : FactSp4TransvW
  cTwo : FactSp4CTwo
  ivk12 : IVK_1_2_general
  ivk13a : IVK_1_3a
  ivk13b : IVK_1_3b
  coat : ∀ (F : Type) [Field F] [Finite F], L2Field F → 11 ≤ Nat.card F →
    ∀ (L : Type) [Group L] [Finite L], (L ≃* L2 F) → ∀ u : L, orderOf u = 2 →
      IsCoatom (Subgroup.centralizer ({u} : Set L))
  outerInv : OL.KFactL3U3OuterInv
  noQuad : OL.KFactL33NoQuadFour

variable {G : Type} [Group G] [Finite G] {H T M V : Subgroup G}

end E217R1

end CFSG.Quasithin
