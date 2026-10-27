
module

public import Certificates.Certificate3041Base

public import CFSG.Monster.B.TwoA.Unitary.OrbitInputs
public import CFSG.Certificates.Kernel.MonsterB.U6OrbSound
public import CFSG.Monster.B.TwoA.Unitary.NData
import CFSG.Certificates.Kernel.Common.Harness

public section

open CFSG.Monster.B.TwoA.Unitary CFSG.Monster.B.Co2 CFSG.Monster.B.TwoA.Census
open CFSG.KC.U6Orb CFSG.KLie.CT

namespace CertificateChecks.Batch3041

open CFSG.Monster.B.TwoA.Unitary CFSG.Monster.B.Co2 CFSG.Monster.B.TwoA.Census
open CFSG.KC.U6Orb CFSG.KLie.CT

set_option maxRecDepth 100000

end CertificateChecks.Batch3041

namespace Certificates

open CertificateChecks.Batch3041 in
open CFSG.Monster.B.TwoA.Unitary CFSG.Monster.B.Co2 CFSG.Monster.B.TwoA.Census in
theorem certificate3041 : (∀ j < 891, n6VecArr[j]! < 2 ^ 22)
    ∧ (∀ i < 891, ∀ j < 891, n6VecArr[i]! = n6VecArr[j]! → i = j)
    ∧ (∀ k < 17, ∀ j < 891, (n6PermsArr[k]!)[j]! < 891)
    ∧ (∀ k < 17, ∀ j < 891,
       Native.actD 22 n6RowArr[k]! n6VecArr[j]! = n6VecArr[(n6PermsArr[k]!)[j]!]!)
    ∧ (natCertOK genAct 17 (fun a => decide (a < 2 ^ 22)) 31 orbitCert = true)
    ∧ (orbitCert.pts = n6VecArr) := by
  refine ⟨fun j hj => vec_lt kVec j (by rw [kSizes.1]; exact hj),
    fun i hi j hj => vec_inj (nodupM_spec _ _ kDist).1 i (by rw [kSizes.1]; exact hi) j (by rw [kSizes.1]; exact hj),
    fun k hk j hj => ?_, perm_act, orbit.1, orbit.2⟩
  exact ((perm_lt kPerm k (by rw [kSizes.2.1]; exact hk)).2 j hj)

end Certificates
