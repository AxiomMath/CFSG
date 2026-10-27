module

public import Certificates.Kernel.D4.EnumA
public import Certificates.Kernel.D4.EnumL
public import Certificates.Data.Kernel.HeDihK
public import Certificates.Data.Kernel.K426K

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelD4

open CFSG.KC.Enum CFSG.KC.HeDih CFSG.KC.K426K
open CFSG.HardMathSupport.Dickson.Bal207.Fam3D42 CFSG.HardMathSupport.Dickson.I271.L28Presentation

theorem gL : Nat.beq (EL.G 0) (evalWK 2457 12 EA.G lWordA) = true ∧
    Nat.beq (EL.G 1) (evalWK 2457 12 EA.G lWordB) = true ∧ Nat.beq EL.ng 2 = true ∧
    Nat.beq EL.N 504 = true :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem derL : derivedLeK 2457 12 EL.N EA.ng EL.ng EL.T EL.S EA.G EL.G = true := by
  decide +kernel

theorem memL : allN EL.ng (fun l => memIdxK EA.N EA.T EA.S (EL.G l)) = true := by
  decide +kernel

theorem relL : l28Words.all (fun wd => Nat.beq (evalWK 2457 12 EL.G wd) (pidn 2457 12)) = true := by
  decide +kernel

end CertificateChecks.KernelD4

end
