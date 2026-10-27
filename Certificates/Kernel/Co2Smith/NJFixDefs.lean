module

public import Certificates.Kernel.Co2Smith.WDefs
public import Certificates.Data.Kernel.Co1F2
public import Certificates.Kernel.SporSch.Co2M.Seeds
public import CFSG.Sporadic.Co2Smith.GlNJData

public section

namespace CertificateChecks.KernelCo2Smith

open CFSG.KC.Co2InvS CFSG.KC.Co2Smith CFSG.Sporadic.Co2Smith.Native CFSG.KS.Co2M
open CertificateChecks.KernelSporSch.Co2M

@[expose] noncomputable def fixVK (A : Nat) : Nat :=
  let T := CFSG.KC.Co1F2.trK 22 A
  ((List.range 2300).filter fun i =>
    Nat.beq (CFSG.KC.M1F2.vmF 22 T (VG (PV 0) i)) (VG (PV 0) i)).length

@[expose] noncomputable def njFixK (lo n : Nat) : Bool :=
  (List.range n).all fun j => (lo + j) == 0 || glNJOm.contains (lo + j) ||
    fixVK (jcK (lo + j)) != 284

end CertificateChecks.KernelCo2Smith
