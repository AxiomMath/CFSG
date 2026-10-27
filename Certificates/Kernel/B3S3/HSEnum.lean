module

public import Certificates.Kernel.B3S3.HSData
public import Certificates.Kernel.B3S3.GenL
public import Certificates.Kernel.SporSch.Th.GenV4
public meta import Certificates.Kernel.B3S3.Gen
import CFSG.Certificates.Kernel.Common.Harness

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
#kb3_enum_l CertificateChecks.KernelB3S3.HS.E0
  CFSG.HardMathSupport.Solomon.Coordinator.B3S3.hsS3C0Gens
  CFSG.HardMathSupport.Solomon.Coordinator.B3S3.hsS3C0Base 3850 12
#kss_natlist CertificateChecks.KernelB3S3.HS.WJ CertificateChecks.KernelB3S3.HS.wj
#kss_natlist CertificateChecks.KernelB3S3.HS.WR CertificateChecks.KernelB3S3.HS.wr

public section

namespace CertificateChecks.KernelB3S3.HS

open CFSG.KC.Enum CFSG.KS

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
