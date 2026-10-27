module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.SteinbergCBConstantWeight
public import CFSG.Quasithin.SteinbergCBDeletedModule
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin.H13.A7

open Equiv Equiv.Perm Subgroup CFSG.Open CFSG.Quasithin.SteinbergCB

section Escape

variable {G : Type} [Group G] {T L V : Subgroup G} {ψ : V ≃* Multiplicative (evenWeight 7)}

@[expose] def vecFour : Fin 7 → ZMod 2 :=
  Pi.single 2 1 + Pi.single 3 1 + Pi.single 4 1 + Pi.single 5 1

end Escape

section Minimal

variable {G : Type} [Group G]

end Minimal

end CFSG.Quasithin.H13.A7
