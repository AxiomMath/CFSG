module

public import Certificates.Kernel.Co1M.D10066
public import Certificates.Data.Kernel.Co1M.CoTwoAut66
public import Certificates.Data.Kernel.Co1M.TwoBK
public import Certificates.Kernel.VecCert.Co1.Data
public meta import Certificates.Kernel.Co1B.GenTri2045
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.Co1B.GenTri2045

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1M

open CFSG.KD.Co1M CFSG.KC.CoTwoAut CFSG.KC.SortTree CFSG.KC.Co1F2 CFSG.KC.M1F2 CFSG.KLie.CT
  CFSG.KC.Co1M CFSG.KC.VecK

@[expose] noncomputable def T366 : List (Nat → Nat) :=
  [recT t30L66 6 40, recT t31L66 6 47, recT t32L66 6 47, recT t33L66 6 45]

@[expose] noncomputable def T466 : List (Nat → Nat) :=
  [recT t40L66 6 46, recT t41L66 6 46, recT t42L66 6 40]

@[expose] noncomputable def cov3F66 (s : Nat) : Bool :=
  covK T366 Sz366 (recT p3L66 6 20) (lk CertificateChecks.KernelVec.Co1.Pt 32) 98280
    (Nat.mul s 4096) 4096

@[expose] noncomputable def cov4F66 (s : Nat) : Bool :=
  covK T466 Sz466 (recT p4L66 6 20) (lk CertificateChecks.KernelVec.Co1.Pt 32) 98280
    (Nat.mul s 4096) 4096

theorem k66_gens : andB (Nat.beq (wK [R0v66, R1v66] W3a66) (getL 0 G366 0))
    (andB (Nat.beq (wK [R0v66, R1v66] W3b66) (getL 0 G366 1))
    (andB (Nat.beq (wK [R0v66, R1v66] W4a66) (getL 0 G466 0))
      (Nat.beq (wK [R0v66, R1v66] W4b66) (getL 0 G466 1)))) = true := by quickRfl

theorem k66_tr : andB (allN 2 fun l => Nat.beq (trK 24 (getL 0 G366 l)) (getL 0 GT366 l))
    (allN 2 fun l => Nat.beq (trK 24 (getL 0 G466 l)) (getL 0 GT466 l)) = true := by quickRfl

theorem k66_fix : andB (allN 2 fun l => Nat.beq (vmF 24 (getL 0 GT366 l) 14717452) 14717452)
    (allN 2 fun l => Nat.beq (vmF 24 (getL 0 GT466 l) 10075731) 10075731) = true := by quickRfl

theorem k66_neg : (notB (Nat.beq (wK [R0v66, R1v66] W3b66) (getL 0 G366 0)) &&
    notB (Nat.beq (vmF 24 (getL 0 GT366 0) 10075731) 10075731) &&
    notB (covK T366 Sz366 (fun i => Nat.xor (recT p3L66 6 20 i) 8)
      (lk CertificateChecks.KernelVec.Co1.Pt 32) 98280 100 1)) = true := by quickRfl

end CertificateChecks.KernelCo1M

#kc_slices CertificateChecks.KernelCo1M.C3x66 CertificateChecks.KernelCo1M.cov3F66 24
#kc_slices CertificateChecks.KernelCo1M.C4x66 CertificateChecks.KernelCo1M.cov4F66 24

end
