module

public import CFSG.OddTranspositions.PartThree.Eleven.Plus.PermCheck
import Certificates.Kernel.PlusFactors.TableFacts

public section

namespace Certificates

open CertificateChecks

open CFSG.OddTranspositions.PartThree in
theorem certificate1383001 : plusTableCheck () = true ∧ plusEnumCheck () = true :=
  ⟨KernelPlusF.tabCheck, KernelPlusF.enumCheck⟩

end Certificates
