module

public import CFSG.Monster.B.TwoA.Fischer.CertRemOrbitInputs
public import Certificates.Data.Kernel.MonsterB.Rem3069
import Certificates.Kernel.MonsterB.Rem3069.K00
import Certificates.Kernel.MonsterB.Rem3069.K01
import Certificates.Kernel.MonsterB.Rem3069.K02
import Certificates.Kernel.MonsterB.Rem3069.K03
import Certificates.Kernel.MonsterB.Rem3069.K04
import Certificates.Kernel.MonsterB.Rem3069.K05
import Certificates.Kernel.MonsterB.Rem3069.K06
import Certificates.Kernel.MonsterB.Rem3069.K07
import Certificates.Kernel.MonsterB.Rem3069.K08
import Certificates.Kernel.MonsterB.Rem3069.K09
import Certificates.Kernel.MonsterB.Rem3069.K10
import Certificates.Kernel.MonsterB.Rem3069.K11
import Certificates.Kernel.MonsterB.Rem3069.K12
import Certificates.Kernel.MonsterB.Rem3069.K13
import Certificates.Kernel.MonsterB.Rem3069.K14
import Certificates.Kernel.MonsterB.Rem3069.K15
import Certificates.Kernel.MonsterB.Rem3069.Neg
meta import Certificates.Kernel.LocalQT.Tc.Gen
public import Certificates.Kernel.MonsterB.Rem3069.Data
import Certificates.Kernel.LocalQT.Tc.Gen

#kqb_all CertificateChecks.KernelMonB.R3069.K CertificateChecks.KernelMonB.R3069.chk 695

public section

namespace Certificates

open CertificateChecks

theorem certificate3069 : ∃ R : Nat → Nat, ∀ c < 695, CFSG.KC.Rem3069.chunkOK R c = true :=
  ⟨KernelMonB.R3069.RT, KernelMonB.R3069.K.all⟩

end Certificates
