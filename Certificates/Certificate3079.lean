
module

public import Certificates.Certificate3079Base

public import CFSG.Monster.B.TwoA.Unitary.Orbit1408Inputs
public import CFSG.Certificates.Kernel.MonsterB.U6OrbSound
public import Certificates.Kernel.MonsterB.Co2Vecs
public import Certificates.Kernel.MonsterB.Tau1408Data
public import CFSG.Monster.B.TwoA.Unitary.NData
public import CFSG.Monster.B.TwoA.Unitary.Orbit1408Data
import CFSG.Certificates.Kernel.Common.Harness

public section

open CFSG.Monster.B.Co2 CFSG.Monster.B.TwoA.Unitary CFSG.Monster.B.TwoA.Census
open CFSG.KC.U6Orb CFSG.KLie.CT CertificateChecks.KernelMonB CertificateChecks.Tau1408

namespace CertificateChecks.Batch3079

open CFSG.Monster.B.Co2 CFSG.Monster.B.TwoA.Unitary CFSG.Monster.B.TwoA.Census
open CFSG.KC.U6Orb CFSG.KLie.CT CertificateChecks.KernelMonB CertificateChecks.Tau1408

set_option maxRecDepth 100000

end CertificateChecks.Batch3079

namespace Certificates

open CertificateChecks.Batch3079 in
open CFSG.Monster.B.Co2 CFSG.Monster.B.TwoA.Unitary CFSG.Monster.B.TwoA.Census in
theorem certificate3079 : (∀ j < 891, Native.vectors.contains (6144 ^^^ n6VecArr[j]!) = true ∧
       6144 ^^^ n6VecArr[j]! < 2 ^ 22 ∧ 6144 ^^^ n6VecArr[j]! ≠ 6144)
    ∧ (∀ i < 1408, Native.vectors.contains o14VecArr[i]! = true ∧
       o14VecArr[i]! ≠ 6144)
    ∧ (∀ i < 1408, ∀ j < 891, o14VecArr[i]! ≠ 6144 ^^^ n6VecArr[j]!)
    ∧ (natCertOK genAct 17 (fun a => decide (a < 2 ^ 22)) 60 tauCert = true)
    ∧ (tauCert.pts = o14VecArr) :=
  ⟨shift_codes, tau_codes, disjoint, orbit.1, orbit.2⟩

end Certificates
