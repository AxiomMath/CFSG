module

public import Certificates.Kernel.MonsterB.Tower3049Bind
public import Certificates.Kernel.MonsterB.Tower3049Checks
public import Certificates.Kernel.MonsterB.Tower3049Inv
public import Certificates.Kernel.MonsterB.Tower3049Gens
import Mathlib.Tactic.IntervalCases

public section

open CFSG.Monster.B.Max2.Native CFSG.KC.Tower CertificateChecks.Tower3049

namespace CertificateChecks.Batch3049

open CFSG.Monster.B.Max2.Native CFSG.KC.Tower CertificateChecks.Tower3049

set_option maxRecDepth 100000

theorem bind : NodeBind DA DB Certificates.Tw3049T :=
  ⟨dag_get, node_chk, inv_ok, r1_eq, r2_eq⟩

theorem lv (i : Nat) {S : Nat → Nat}
    (hlen : levelOffsets[i + 1]! - levelOffsets[i]! = towerLevels[i]!.2)
    (hoff : levelOffsets[i + 1]! ≤ 4802) (hbase : towerLevels[i]!.1 < 2 ^ 22)
    {off b len : Nat} {bs : List Nat} (ho : levelOffsets[i]! = off) (hb : towerLevels[i]!.1 = b)
    (hl : towerLevels[i]!.2 = len) (hbs : ((List.range i).map fun k => towerLevels[k]!.1) = bs)
    (hpt : ∀ k < len, ptK V W Certificates.Tw3049T off b bs k = true)
    (hsrt : ∀ m < len, srtK V S off len m = true) :
    levelOK (towerPointsAll ()) (nodeMats ()) i = true := by
  subst ho hb hl hbs
  exact levelOK_of bind pts_get hlen hoff hbase hpt hsrt

theorem levels_ok : levelsOK () = true := by
  unfold levelsOK
  rw [List.all_eq_true]
  intro i hi
  have hi' := List.mem_range.1 hi
  interval_cases i
  · exact lv 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) pt_chk0 srt_chk0
  · exact lv 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) pt_chk1 srt_chk1
  · exact lv 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) pt_chk2 srt_chk2
  · exact lv 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) pt_chk3 srt_chk3
  · exact lv 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) pt_chk4 srt_chk4
  · exact lv 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) pt_chk5 srt_chk5

theorem towerCheck_eq_true_0 : towerCheck = true := by
  unfold towerCheck
  rw [sizesOK_of bind, gens_ok, nodesOK_of bind, levels_ok, shape_ok]
  rfl

end CertificateChecks.Batch3049

namespace Certificates

open CertificateChecks

open CFSG.Monster.B.Max2.Native in
theorem certificate3049 : towerCheck = true :=
  CertificateChecks.Batch3049.towerCheck_eq_true_0

end Certificates
