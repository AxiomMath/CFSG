module

public import CFSG.Blueprint.NativeSporadic
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import CFSG.Sporadic.Bridge.LySurj

public section

namespace Certificates

open TauCeti in
theorem certificate8160 : Nonempty (SporadicName.Ly.Group ≃* CFSG.Blueprint.NativeSporadic.Ly) :=
  CFSG.Sporadic.Bridge.Ly.nonempty_mulEquiv.map MulEquiv.symm

end Certificates
