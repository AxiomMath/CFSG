module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431SporAux.Fi23ThirteenInputs
import Certificates.Certificate9206
import Certificates.Certificate9111
import Certificates.Kernel.Fi23Five.Glue

public section

namespace Certificates

open CertificateChecks

open CFSG.HardMathSupport.Dickson.Sec6.I1431.Fi23ThirteenNative in
theorem certificate17220 : fi23ThirteenOK (CFSG.Sporadic.Fi23.Native.orbitData ()) = true := by
  rw [CFSG.KD.Fi23K.orbitData_eq']
  exact KernelFi23Five.thirteen_ok

end Certificates
