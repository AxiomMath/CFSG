module

public import Certificates.Data.Kernel.Bounds.Table
public import CFSG.Certificates.Kernel.Bounds.McCov.Route
public import CFSG.Certificates.CosetTablePresented
import Certificates.Kernel.Bounds.Assemble
import CFSG.Certificates.Kernel.Bounds.McCov.All
import CFSG.Certificates.Kernel.Bounds.McCov.T2vK000
import CFSG.Certificates.Kernel.Bounds.McCov.T2vK001
import CFSG.Certificates.Kernel.Bounds.McCov.T2vK002

public section

#kb_cert CFSG.KBRoute.McCov T2 McCov_T2v include_bytes "../../../CFSG/Certificates/Kernel/Bounds/McCov/data/McCov_T2v.meta" 17392 12814432063599842300 CFSG.KBRoute.McCov.rels2

namespace CertificateChecks.KernelCover.McCov

open CFSG.CosetTable CFSG.KC.MiscCoset CFSG.SectionRank.Native CFSG.KBRoute.McCov

theorem t2 : CFSG.KBRoute.McCov.T2.ok = true := by kb_assemble McCov_T2v

theorem pres_card : Finite (PG 7 mclPresWords) ∧ Nat.card (PG 7 mclPresWords) ≤ 14580 * 4 := by
  have h := t2
  unfold CFSG.KBRoute.McCov.T2.ok at h
  have hi := zpowers_index_le_of_tableOk mclPresWords rfl h (by decide) top2 [(0, true)]
    (by decide +kernel)
  exact card_le_of_zpowers_index mclPresWords [(0, true)] (by norm_num) (by decide +kernel) hi

end CertificateChecks.KernelCover.McCov

end
