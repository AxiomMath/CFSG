module

public import CFSG.Milestones.ASVolI.F48.Rest.G23Inputs
public import CFSG.Milestones.ASVolI.F48.Rest.G23Pres
public import Mathlib

public section

namespace CFSG.KC.G23F48

open CFSG.ASVolI

@[expose] def frameOK (FV : List (Array ℕ)) (W cs : Array ℕ) : Bool :=
  FV.length == 15 && W.size == 196 && cs.size == 14 &&
    ((List.range 14).all fun i => burnsideF48t_g23MulVec W FV[i]! == burnsideF48t_g23Unit i) &&
    burnsideF48t_g23MulVec W FV[14]! == cs &&
    (List.range 14).all fun i => cs[i]! == 1 || cs[i]! == 2

end CFSG.KC.G23F48
