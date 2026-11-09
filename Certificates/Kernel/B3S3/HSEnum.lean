module

import CFSG.Certificates.Kernel.BfsPinRunSl
public import Certificates.Kernel.B3S3.HSData
public import Certificates.Kernel.B3S3.GenL
public import Certificates.Kernel.B3S3.GenSl
public import Certificates.Kernel.SporSch.Th.GenV4
public meta import Certificates.Kernel.B3S3.Gen
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.BfsPinSliceSound

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelB3S3.HS

open CFSG.HardMathSupport.Solomon.Coordinator.B3S3

meta def pts0 : Array (Array Nat) := (CFSG.KC.BfsGen.search 3850 12 hsS3C0Gens).1

meta def w0 : List Nat × List Nat := CFSG.KC.B3S3Gen.convWit 3850 pts0 [2, 5] [1]

meta def wj : List Nat := w0.1

meta def wr : List Nat := w0.2

end CertificateChecks.KernelB3S3.HS

end

set_option Elab.async false

#kb3_enum_l CertificateChecks.KernelB3S3.HS.EQ
  CFSG.HardMathSupport.Solomon.Coordinator.B3S3.hsS3QGens
  CFSG.HardMathSupport.Solomon.Coordinator.B3S3.hsS3C0Base 3850 12
#kb3_enum_sl CertificateChecks.KernelB3S3.HS.E0
  CFSG.HardMathSupport.Solomon.Coordinator.B3S3.hsS3C0Gens
  CFSG.HardMathSupport.Solomon.Coordinator.B3S3.hsS3C0Base 3850 12 20
#kss_natlist CertificateChecks.KernelB3S3.HS.WJ CertificateChecks.KernelB3S3.HS.wj
#kss_natlist CertificateChecks.KernelB3S3.HS.WR CertificateChecks.KernelB3S3.HS.wr

public section

namespace CertificateChecks.KernelB3S3.HS

open CFSG.KC.Enum CFSG.KS CFSG.KC.BfsPin

theorem E0.ok : bfsK 3850 12 E0.ng E0.G E0.N E0.T E0.E E0.S = true :=
  bfsK_of_slices (L := 20) (K := 18) (C := E0.C) (by decide) (by norm_num) (by quickRfl) E0.g
    E0.csAll E0.t0 E0.dist (Nat.eq_of_beq_eq_true E0.c0) (Nat.eq_of_beq_eq_true E0.cK) E0.rsAll

theorem bQE : ∀ j < 2, Nat.beq (EQ.G j) (QG.F j) = true := by
  intro j hj
  interval_cases j <;> quickRfl

theorem bG : ∀ j < 4, Nat.beq (E0.G j) (GG.F j) = true := by
  intro j hj
  interval_cases j <;> quickRfl

theorem n0 : Nat.beq EQ.N 9 = true ∧ Nat.beq E0.N 360 = true ∧ Nat.beq E0.ng 4 = true ∧
    Nat.beq EQ.ng 2 = true := ⟨by quickRfl, by quickRfl, by quickRfl, by quickRfl⟩

end CertificateChecks.KernelB3S3.HS

end
