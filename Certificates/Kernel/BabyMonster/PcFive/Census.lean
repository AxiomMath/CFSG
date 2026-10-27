module

public import CFSG.Certificates.Kernel.BabyMonster.PcFive.Cover
public import Certificates.Kernel.BabyMonster.PcFive.Check0
public import Certificates.Kernel.BabyMonster.PcFive.Check1
public import Certificates.Kernel.BabyMonster.PcFive.Check2
public import Certificates.Kernel.BabyMonster.PcFive.Check3
public import Certificates.Kernel.BabyMonster.PcFive.Fus

public section

namespace CertificateChecks.KernelBM.PcFive

open CFSG.KC.BM.PcFive CFSG.KC.BM.PcFiveD

theorem censusFact : CensusFact := by
  have hC : ∀ k < 16, chunkOK rep 152 (1000 * k) (chunks.getD k []) = true := by
    intro k hk
    interval_cases k
    exacts [t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15]
  exact census_fact (elem_of_chunks hC tlen) tfus

theorem phiOK_true : phiOK () = true := tphi

end CertificateChecks.KernelBM.PcFive

end
