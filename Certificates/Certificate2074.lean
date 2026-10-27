module

public import CFSG.Sporadic.FischerOddCore.Fi23UniqCheckInputs
import Certificates.Kernel.Fi23R.Fact2074

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.FischerOddCore CFSG.Sporadic.Th.Native CFSG.Perm.Native in
open CFSG.Sporadic.Fi23.Native in
theorem certificate2074 : (fi23UniqOK (orbitData ()) = true)
    ∧ (fi23TripOK (orbitData ()) = true) :=
  ⟨by rw [CFSG.KD.Fi23K.orbitData_eq']; exact KernelFi23R.uniq_ok,
    by rw [CFSG.KD.Fi23K.orbitData_eq']; exact KernelFi23R.trip_ok⟩

end Certificates
