module

public import CFSG.Sporadic.FischerOddCore.Fi23WitCheckInputs
import Certificates.Kernel.Fi23R.Fact2075

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.FischerOddCore CFSG.Sporadic.Th.Native CFSG.Perm.Native in
open CFSG.Sporadic.Fi23.Native in
theorem certificate2075 : fi23WitChecks (orbitData ()) = true := by
  rw [CFSG.KD.Fi23K.orbitData_eq']
  exact KernelFi23R.wit_ok

end Certificates
