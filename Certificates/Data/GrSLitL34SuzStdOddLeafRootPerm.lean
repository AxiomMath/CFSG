module

public import Certificates.Data.GrSLitL34SuzStdOddLeafRootCheck
public import CFSG.Sporadic.SuzOddCore.CTIFirst
public import CFSG.Sporadic.HeldB.Common

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG.Sporadic.SuzOddCore

@[expose] noncomputable def suzRootPerm
    (j : ℕ) : Equiv.Perm (Fin 42) :=
  ((suzRootWords.getD j []).map dperm).prod

end CFSG.ComponentClassification.GrSLit.L34Sec5S

end
