module

public import Certificates.Certificate21120
public import Certificates.Certificate21121
public import Certificates.Certificate21122
public import Certificates.Certificate21123
public import Certificates.Certificate21124
public import CFSG.Sporadic.Co2Smith.GlDataInputs
import Certificates.Kernel.Co2Smith.Chain
import Certificates.Kernel.Co2Smith.ChainMData
import Certificates.Kernel.Sporadic.RawGenSplitP
import Certificates.Kernel.Sporadic.RawGenSchO
import Certificates.Kernel.Sporadic.RawGenSchOJ
import Certificates.Kernel.Co2Smith.Psi
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.InvariantMerge
public import CFSG.Sporadic.Co2Smith.Cat

public section

namespace CFSG.Sporadic.Co2Smith

theorem glElem_check : Native.glElemOK = true :=
  Certificates.certificate21120

theorem glRefineC0_check :
    GlOrbitFacts [Native.glPermArr Native.glAl, Native.glPermArr Native.glGa]
      (Native.glWit0.map (·.1)) (Native.glWit1.map (·.1)) (Native.glWit2.map (·.1))
      [(1172, Native.glWit0Pts 1), (1348, Native.glWit0Pts 2)] :=
  Certificates.certificate21121

theorem glRefineCz_check :
    GlOrbitFacts [Native.glPermArr Native.glAl, Native.glPermArr Native.glGa,
      Native.glPermArr Native.glZ] (Native.glWitZ0.map (·.1)) (Native.glWitZ1.map (·.1))
      (Native.glWitZ2.map (·.1)) [] :=
  Certificates.certificate21122

theorem glWit_check : Native.glWitOK = true :=
  Certificates.certificate21123

theorem glChainN_check : Native.glChainNOK = true :=
  Certificates.certificate21124

end CFSG.Sporadic.Co2Smith
