module

public import CFSG.Milestones.ASVolI.C31.J4NP.Is2AAffBase
public import Certificates.Certificate7853

public section

namespace CFSG.ASVolI

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT
open CFSG.J4Tree.Native CFSG.ASVolI
open CFSG.Quasithin.J4Loc (z0)

theorem burnsideJ4NP_is2A_iff_affine_H
    {x : J} (hx : x ∈ Hj) (hsq : x * x = 1) (hne : x ≠ 1) :
    IsConj x z0 ↔ burnsideJ4NP_affine2A (burnsideJ4NP_enc ⟨x, hx⟩) = true := by
  rw [← burnsideJ4NP_Is2A_iff_isConj, Certificates.certificate7853 x hx hsq hne,
    burnsideJ4NP_encJ_of_mem hx]
  rfl

end CFSG.ASVolI
