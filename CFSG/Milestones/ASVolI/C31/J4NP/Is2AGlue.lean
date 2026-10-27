module

public import CFSG.Milestones.ASVolI.C31.J4NP.Is2AAffH
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ASVolI

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.J4Tree.Native CFSG.ASVolI
open CFSG.Quasithin.J4Loc (z0)

theorem burnsideJ4NP_Is2A_iff_affine_H
    {x : J} (hx : x ∈ Hj) (hsq : x * x = 1) (hne : x ≠ 1) :
    burnsideJ4NP_Is2A x ↔ burnsideJ4NP_affine2A (burnsideJ4NP_enc ⟨x, hx⟩) = true := by
  rw [burnsideJ4NP_Is2A_iff_isConj]
  exact burnsideJ4NP_is2A_iff_affine_H hx hsq hne

end CFSG.ASVolI
