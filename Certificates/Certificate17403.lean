module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431SporAux.Fi23PinThirteenInputs
import Certificates.Kernel.Fi23Pin13.Glue

public section

namespace Certificates

open CertificateChecks

theorem certificate17403 : CFSG.HardMathSupport.Dickson.Sec6.I1431.Fi23PinNative.fi23Pin13OK
    (CFSG.Sporadic.Fi23.Native.orbitData ()) = true := by
  rw [CFSG.KD.Fi23K.orbitData_eq']
  exact KernelFi23Pin13.pin13_ok

end Certificates
