module

public import Certificates.Data.S7G23Insp
import Certificates.Kernel.G2Three.InspFinal

public section

namespace Certificates

open Certificates.S7G23Insp in
theorem certificate543001 : c0 () = true ∧ c1 () = true ∧ c2 () = true ∧ c3 () = true ∧ c4 () = true :=
  CFSG.KD.G2Three.ok543001

end Certificates
