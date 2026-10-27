
module

public import CFSG.Monster.B.TwoA.Unitary.OrbitInputs
public import CFSG.Certificates.Kernel.MonsterB.U6OrbSound
public import CFSG.Monster.B.TwoA.Unitary.NData
import CFSG.Certificates.Kernel.Common.Harness

@[expose] public section

open CFSG.Monster.B.TwoA.Unitary CFSG.Monster.B.Co2 CFSG.Monster.B.TwoA.Census
open CFSG.KC.U6Orb CFSG.KLie.CT

namespace CertificateChecks.Batch3041

set_option maxRecDepth 100000

theorem kVec : boundL (pw2 22) n6VecArr.toList = true := by quickRfl

theorem kDist : nodupM n6VecArr.toList 0 = true := by quickRfl

theorem kPerm : shapeL 891 891 n6PermsArr.toList = true := by quickRfl

theorem kRow : shapeL 22 (pw2 22) n6RowArr.toList = true := by quickRfl

theorem kEdge : edgeLOK n6VecArr.toList n6RowArr.toList (packP 891 10 n6PermsArr.toList)
    (permTab 891 10) 891 17 = true := by quickRfl

theorem kReplay : replayDOK (packP 891 10 n6PermsArr.toList) (permTab 891 10) 17 891 = true := by
  quickRfl

theorem kSizes : n6VecArr.size = 891 ∧ n6PermsArr.size = 17 ∧ n6RowArr.size = 17 ∧
    n6VecArr[0]! = 31 := by
  decide +kernel

theorem edges : ∀ i < 891, ∀ k < 17, permTab 891 10 (packP 891 10 n6PermsArr.toList) i k < 891 ∧
    n6VecArr[permTab 891 10 (packP 891 10 n6PermsArr.toList) i k]! =
      Native.actD 22 n6RowArr[k]! n6VecArr[i]! :=
  edge_sound kSizes.1 kSizes.2.2.1 kVec kRow kEdge

theorem perm_act : ∀ k < 17, ∀ j < 891,
    Native.actD 22 n6RowArr[k]! n6VecArr[j]! = n6VecArr[(n6PermsArr[k]!)[j]!]! := by
  intro k hk j hj
  have e := (edges j hj k hk).2
  rw [packP_get (by norm_num) kPerm (by rw [kSizes.2.1]; exact hk) hj] at e
  exact e.symm

theorem orbit : natCertOK genAct 17 (fun a => decide (a < 2 ^ 22)) 31 orbitCert = true ∧
    orbitCert.pts = n6VecArr :=
  bfs_sound (act := genAct) (fuel := 900) (fun _ _ => rfl) kSizes.1 (by norm_num) kSizes.2.2.1
    kSizes.2.2.2 (by norm_num) kVec (nodupM_spec _ _ kDist).1 kRow kEdge kReplay

end CertificateChecks.Batch3041

namespace Certificates

end Certificates
