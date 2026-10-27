module

public import CFSG.Monster.B.Fischer.HexadStabInputs
public import CFSG.Certificates.Kernel.MonsterB.U6OrbSound
import CFSG.Certificates.Kernel.Common.Harness

public section

open CFSG.Monster.B.TwoA.Census CFSG.Monster.B.Fischer CFSG.KC.U6Orb

namespace CertificateChecks.Batch3030

open CFSG.Monster.B.TwoA.Census CFSG.Monster.B.Fischer CFSG.KC.U6Orb

set_option maxRecDepth 100000

theorem kPts : (List.range 77).all
    (natPointOK actAB 2 (fun m => decide (m < 2 ^ 22)) blockCert) = true := by quickRfl

theorem kHead : (blockCert.pts.size == 77 && blockCert.pts[0]! == 63) = true := by quickRfl

theorem kDist : nodupM blockCert.pts.toList 0 = true := by quickRfl

end CertificateChecks.Batch3030

namespace Certificates

open CertificateChecks.Batch3030 in
open CFSG.Monster.B.TwoA.Census CFSG.Monster.B.Fischer in
theorem certificate3030 : natCertOK actAB 2 (fun m => decide (m < 2 ^ 22)) 63 blockCert = true := by
  have h := kHead
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  simp only [natCertOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, h.1, h.2]
  exact ⟨⟨by norm_num, kPts⟩,
    CFSG.KC.Bfs.pairwise_lt_mergeSort (nodupM_spec _ _ kDist).1⟩

end Certificates
