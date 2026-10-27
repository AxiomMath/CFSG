module

public import CFSG.Sporadic.Schreier.LyModelSchreier
public import CFSG.LocalAnalysis.ComponentClassification.SporadicSchreierDispatch

public section

namespace CFSG.Sporadic.LySchreier

open CFSG.Blueprint CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ComponentClassification.SporadicSchreierDispatch

theorem outer_Ly_isSolvable :
    Group.IsSolvable (Outer NativeSporadic.Ly) :=
  model_schreier NativeSporadic.Ly ⟨MulEquiv.refl _⟩

theorem sporadicSchreierCase_Ly :
    SporadicSchreierCase .Ly :=
  sporadicSchreierCase_of_outer outer_Ly_isSolvable

end CFSG.Sporadic.LySchreier
