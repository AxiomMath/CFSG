
module

public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.EightTenFour.A7Data
public import CFSG.Quasithin.Background.C1Basic
import Certificates.Kernel.A7Rad.Glue

public section

namespace Certificates

open CertificateChecks

open CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.EightTenFour in
theorem certificate134003 : IsSimpleGroup A7 → ∀ P : Subgroup A7, CFSG.Quasithin.IsTwoRadicalIn ⊤ P →
    ∃ H : Subgroup A7, IsSimpleGroup ↥H ∧ (∃ a ∈ H, ∃ b ∈ H, a * b ≠ b * a) ∧ P ≤ H ∧
      ¬ 2 ∣ (P.subgroupOf H).index :=
  fun hA7 P hrad => KernelA7Rad.a7Good hA7 P hrad

end Certificates
