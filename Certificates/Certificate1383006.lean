module

public import CFSG.OddTranspositions.PartThree.Eleven.Minus.PermCheck
import Certificates.Kernel.MinusEnum.TableFacts

public section

namespace Certificates

open CertificateChecks

open CFSG.OddTranspositions.PartThree in
theorem certificate1383006 : minusTableCheck () = true ∧ minusEnumCheck () = true :=
  ⟨KernelMinusEnum.tabCheck, KernelMinusEnum.enumCheck⟩

end Certificates
