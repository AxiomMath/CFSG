module

public import CFSG.Quasithin.Recognition.St84.J2VtxInputs
import Certificates.Kernel.Sporadic.OddCore.J2VtxF

public section

namespace Certificates

open CFSG.Quasithin.F112R.St84.J2Model in
theorem certificate733001 : (a1OK = true) ∧ (a2OK = true) ∧ (a3OK = true) ∧
    (b0OK = true) ∧ (b1OK = true) ∧ (b2OK = true) ∧ (b3OK = true) ∧
    (b4OK = true) ∧ (b5OK = true) :=
  CertificateChecks.KernelSpor.J2Vtx.j2vtx_all

end Certificates
