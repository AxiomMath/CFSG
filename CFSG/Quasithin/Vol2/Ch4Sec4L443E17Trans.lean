module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.QuasithinUnique.CompNormSylow
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.Module
public import CFSG.Quasithin.Vol2.Ch4Sec4L443EFact

public section

namespace CFSG.Quasithin.H13.Ch4.E443

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.H13
open CFSG.Blueprint
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T M L B Tp VB : Subgroup G}

theorem isFFModule_of_le {V : Type*} [CommGroup V] {X Y : Subgroup (MulAut V)} (hXY : X ≤ Y)
    (h : IsFFModule X) : IsFFModule Y := by
  obtain ⟨A, hA, hrest⟩ := h
  exact ⟨A, hA.trans hXY, hrest⟩

end CFSG.Quasithin.H13.Ch4.E443
