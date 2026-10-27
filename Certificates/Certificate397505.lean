module

public import Certificates.Data.TwinPerpSmSp1WitM22
public import Certificates.Data.TwinPerpSmSp1WitJ2
public import Certificates.Data.TwinPerpSmSp1WitL34
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicM22Tests
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutCheckInputs
import Certificates.Kernel.Q8Wit.Final
import Certificates.Kernel.Q8Wit.J2Glue
import Certificates.Kernel.Q8Wit.M22Code
import Certificates.Kernel.Q8Wit.M22Glue

public section

namespace Certificates

open CertificateChecks

theorem certificate397505 :
    (TwinPerpSmSp1.q8WitCheck TwinPerpSmSp1.m22Wit = true ∧
      CFSG.Monster.B.Co2.Native.allLt TwinPerpSmSp1.m22Wit.xg.size (fun l =>
        CFSG.ComponentClassification.RankTwoSporadic.M22.m22InX TwinPerpSmSp1.m22Wit.xg[l]!) = true ∧
      CFSG.Monster.B.Co2.Native.allLt TwinPerpSmSp1.m22Wit.syl.pg.size (fun l =>
        CFSG.ComponentClassification.RankTwoSporadic.M22.pairA TwinPerpSmSp1.m22Wit.syl.pg[l]!) =
          true) ∧
    (TwinPerpSmSp1.q8WitCheck TwinPerpSmSp1.j2Wit = true ∧
      CFSG.Monster.B.Co2.Native.allLt TwinPerpSmSp1.j2Wit.xg.size (fun l =>
        CFSG.ComponentClassification.J2Cover.inP TwinPerpSmSp1.j2Wit.xg[l]!) = true) ∧
    (TwinPerpSmSp1.q8WitCheck TwinPerpSmSp1.l34Wit = true ∧ TwinPerpSmSp1.l34SqCheck () = true ∧
      TwinPerpSmSp1.l34CentCheck () = true) :=
  ⟨⟨KernelQ8W.M22.q8Wit_true, KernelQ8W.M22.inX, KernelQ8W.M22.pairS⟩,
    ⟨KernelQ8W.J2.q8Wit_true, KernelQ8W.j2InP_true⟩,
    ⟨KernelQ8W.L34.q8Wit_true, KernelQ8W.l34Sq_true, KernelQ8W.l34Cent_true⟩⟩

end Certificates
