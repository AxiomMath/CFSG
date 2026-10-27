module

public import CFSG.Monster.B.Dyadic.CTIBK
import Certificates.Kernel.BabyMonster.CTIB.CaseB

public section

namespace Certificates

open CertificateChecks

theorem certificate3113 : CFSG.Monster.B.Dyadic.FactCaseB :=
  KernelBM.CTIB.factCaseB_of

end Certificates
