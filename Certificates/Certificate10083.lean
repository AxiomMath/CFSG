module

public import Certificates.Data.CFSGNative.Co2Smith.SeedValid
import Certificates.Kernel.Co2SmithS.Seeds
public import CFSG.Sporadic.Co2Smith.CheckInputs

public section

open CFSG.Sporadic.Co2Smith

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.Co2Smith in
theorem certificate10083 :
    Native.seedsValidOK seedRowsArr = true := by
  unfold Native.seedsValidOK
  rw [KernelCo2SmithS.seeds_get 0 (by omega), KernelCo2SmithS.seeds_get 1 (by omega),
    CFSG.KC.Co2SmithS.validM_unpack, CFSG.KC.Co2SmithS.validM_unpack]
  rfl

end Certificates
