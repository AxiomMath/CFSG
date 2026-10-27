module

public import Certificates.Data.Kernel.Bounds.Table
public import CFSG.Certificates.Kernel.Bounds.J3Cov.Route
public import CFSG.Certificates.CosetTablePresented
import Certificates.Kernel.Bounds.Assemble
import CFSG.Certificates.Kernel.Bounds.J3Cov.All
import CFSG.Certificates.Kernel.Bounds.J3Cov.T1vK000
import CFSG.Certificates.Kernel.Bounds.J3Cov.T2vK000

public section

#kb_cert CFSG.KBRoute.J3Cov T1 J3Cov_T1v include_bytes "../../../CFSG/Certificates/Kernel/Bounds/J3Cov/data/J3Cov_T1v.meta" 1555 2933350278563230335 CFSG.KBRoute.J3Cov.rels1

#kb_cert CFSG.KBRoute.J3Cov T2 J3Cov_T2v include_bytes "../../../CFSG/Certificates/Kernel/Bounds/J3Cov/data/J3Cov_T2v.meta" 395 12510794691574565412 CFSG.KBRoute.J3Cov.rels2

namespace CertificateChecks.KernelCover.J3Cov

open CFSG.CosetTable CFSG.KC.MiscCoset CFSG.SectionRank.Native CFSG.KBRoute.J3Cov

theorem t1 : CFSG.KBRoute.J3Cov.T1.ok = true := by kb_assemble J3Cov_T1v

theorem t2 : CFSG.KBRoute.J3Cov.T2.ok = true := by kb_assemble J3Cov_T2v

theorem gamma_card : Finite (PG 6 j3GammaWords) ∧ Nat.card (PG 6 j3GammaWords) ≤ 729 * 8 := by
  have h := t1
  unfold CFSG.KBRoute.J3Cov.T1.ok at h
  have hi := zpowers_index_le_of_tableOk j3GammaWords rfl h (by decide) top1 [(0, true)]
    (by decide +kernel)
  exact card_le_of_zpowers_index j3GammaWords [(0, true)] (by norm_num) (by decide +kernel) hi

theorem n_card : Finite (PG 6 nWords) ∧ Nat.card (PG 6 nWords) ≤ 243 * 8 := by
  have h := t2
  unfold CFSG.KBRoute.J3Cov.T2.ok at h
  have hi := zpowers_index_le_of_tableOk nWords rfl h (by decide) top2 [(0, true)]
    (by decide +kernel)
  exact card_le_of_zpowers_index nWords [(0, true)] (by norm_num) (by decide +kernel) hi

end CertificateChecks.KernelCover.J3Cov

end
