module

public import Certificates.Data.E6WeylMinors
import Certificates.Kernel.E6Div.Assembly

public section

namespace Certificates

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6 Certificates.E6WeylMinors in
theorem certificate715001 : ∀ w : WeylGroup Tag.E6,
    (weylMatrix w * weylMatrix w = 1 ∨
        SmallMinor 3 (weylMatrix w + 1) ∧ SmallMinor 2 (weylMatrix w - 1)) ∧
    (weylMatrix w * rhoMatrix * (weylMatrix w * rhoMatrix) = 1 ∨
        SmallMinor 3 (weylMatrix w * rhoMatrix - 1) ∧ SmallMinor 2 (weylMatrix w * rhoMatrix + 1)) :=
  CertificateChecks.KernelE6Div.e6div_holds

end Certificates
