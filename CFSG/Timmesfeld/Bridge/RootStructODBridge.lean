module

public import CFSG.Timmesfeld.Bridge.RootStructOD
public import CFSG.Timmesfeld.Bridge.RootStructBridge

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld

theorem exceptionalNoLeviPlaneStep_holds : Moufang.ExceptionalNoLeviPlaneStep :=
  exceptionalNoLeviPlaneStep_of_oppositeDeterminesStep oppositeDeterminesStep

theorem caseICommPQInput_holds : Moufang.CaseICommPQInput :=
  caseICommPQInput_of_oppositeDetermines oppositeDeterminesStep

theorem nCoreStep_of_nCoreStepLarge (hL : NCoreStepLarge) : NCoreStep :=
  nCoreStep_of_oppositeDetermines oppositeDeterminesStep hL

end CFSG.Timmesfeld.Bridge
