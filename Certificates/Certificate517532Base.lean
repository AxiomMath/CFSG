module

public import Certificates.Data.AE6CertBTri
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6S

@[expose] public section

namespace Certificates

open CFSG.ClassicalInvolution.Generic CFSG.EvenSmallLie.OmegaEight
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6S
open scoped Pointwise

@[expose] noncomputable def ae6TriStab (l : Fin 3) : Subgroup AE6Om :=
  (MulAction.stabilizer (Equiv.Perm (Fin 360))
    ({x : Fin 360 | x.val ∈ AE6CertB.triB l} : Set (Fin 360))).comap omegaT.subtype

end Certificates

