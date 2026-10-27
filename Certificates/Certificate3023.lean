
module

public import Certificates.Certificate3023Base
import all Certificates.Certificate3023Base

public import CFSG.Monster.B.TwoA.Census.CosetEnumCheckInputs
import all CFSG.Monster.B.TwoA.Census.CosetEnumCheckInputs

namespace CertificateChecks.Batch3023

open CFSG.KC.KDense CFSG.KLie.CT CFSG.Monster.B CFSG.KC.SortTree CFSG.KC.Bfs
  CFSG.Monster.B.TwoA.Census CertificateChecks.Coset3023

end CertificateChecks.Batch3023

public section

namespace Certificates

open CertificateChecks

open CFSG.Monster.B.Rep4371 CFSG.Monster.B.TwoA.Census in
theorem certificate3023 : (Native.CosetEnum.countSq (tT 1) (tD 1) (wP 1) = 69632)
    ∧ (Native.CosetEnum.countSq (tT 2) (tD 2) (wP 2) = 8192)
    ∧ (Native.CosetEnum.countSq (tT 6) (tD 6) (wP 6) = 0)
    ∧ (classCheck = true)
    ∧ (class17Check = true)
    ∧ (class2Check = true) :=
  ⟨CertificateChecks.Batch3023.count_1, CertificateChecks.Batch3023.count_2, CertificateChecks.Batch3023.count_6, CertificateChecks.Batch3023.classCheck_ok,
    CertificateChecks.Batch3023.class17Check_ok, CertificateChecks.Batch3023.class2Check_ok⟩

end Certificates
