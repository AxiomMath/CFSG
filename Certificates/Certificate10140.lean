module

public import Certificates.Data.M22Klein
import CFSG.Certificates.Kernel.PermCent.SmallBSound
import Certificates.Kernel.PermCent.K10140
public import Certificates.Data.Kernel.PermCent.SmallB

public section

open CFSG.LocalAnalysis.GLTheoremA.KD1426M22 CFSG.Certificates.Kernel.PkCV

namespace Certificates

open CertificateChecks

private theorem kleinOK_eq: m22KleinOK () = M22B.kleinC := by
  rw [m22KleinOK.eq_1, M22B.kleinC.eq_1]
  simp only [← ev_evCodesB, ev_mul', ev_inv', ev_pow', one_eq_ev, ne_eq, ev_eq_iff]

theorem certificate10140 : CFSG.LocalAnalysis.GLTheoremA.KD1426M22.m22KleinOK () = true := by
  rw [kleinOK_eq]
  exact KernelPermCent.k10140

end Certificates
