module

public import Certificates.Data.U43Model
public import CFSG.LieType.Multipliers.U43Data
public import CFSG.Quasithin.H13.GoldschmidtU43ModInputs
import Certificates.Kernel.U43Mod.Glue

public section

namespace Certificates

open CertificateChecks

open CFSG.KGroups.U43 CFSG.LieType.Multipliers.U43 CFSG.Quasithin.H13.U43 in
theorem certificate4158 : orbCheck 820 CFSG.LieType.Multipliers.U43.tabA CFSG.LieType.Multipliers.U43.tabB = true ∧ h4Check 820 CFSG.LieType.Multipliers.U43.tabA CFSG.LieType.Multipliers.U43.tabB rels4Codes = true ∧
    sylCheck 820 CFSG.LieType.Multipliers.U43.tabA CFSG.LieType.Multipliers.U43.tabB = true ∧ modelCheck 820 CFSG.LieType.Multipliers.U43.tabA CFSG.LieType.Multipliers.U43.tabB rels5Codes = true :=
  ⟨KernelU43Mod.orb_ok, KernelU43Mod.h4_ok, KernelU43Mod.syl_ok, KernelU43Mod.model_ok⟩

end Certificates
