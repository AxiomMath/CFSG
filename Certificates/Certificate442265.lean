module

public import Certificates.Data.Asc82SwapCheck
public import CFSG.LieType.Multipliers.U43Data
import Certificates.Kernel.U43Swap.Final

public section

namespace Certificates

open CertificateChecks

open CFSG.LieType.Multipliers.U43 in
theorem certificate442265 : Asc82Swap.swapTCheck 820 CFSG.LieType.Multipliers.U43.tabA CFSG.LieType.Multipliers.U43.tabB = true ∧
    Asc82Swap.oddCentCheck 820 CFSG.LieType.Multipliers.U43.tabA CFSG.LieType.Multipliers.U43.tabB = true :=
  ⟨KernelU43Swap.swap_ok KernelU43Swap.swTables, KernelU43Swap.oddCent_ok KernelU43Swap.oddCentFact⟩

end Certificates
