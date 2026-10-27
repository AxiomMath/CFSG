module

public import Certificates.Kernel.E27J3Syl.KS
public import Certificates.Kernel.E27J3Syl.DW
public import Certificates.Kernel.SporSch.PairJ3.Chain
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option Elab.async false

namespace CFSG.KD.E27J3S

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CertificateChecks.KernelSporSch

theorem c131001_sw0 : wordEqK 6156 13 (mask 13) (pidn 6156 13) PJ3.S PJ3.SI 5 (SW.getD 0 [])
    (SY.F 0) = true := by
  quickRfl

theorem c131001_sw1 : wordEqK 6156 13 (mask 13) (pidn 6156 13) PJ3.S PJ3.SI 5 (SW.getD 1 [])
    (SY.F 1) = true := by
  quickRfl

theorem c131001_sw2 : wordEqK 6156 13 (mask 13) (pidn 6156 13) PJ3.S PJ3.SI 5 (SW.getD 2 [])
    (SY.F 3) = true := by
  quickRfl

theorem c131001_sw3 : wordEqK 6156 13 (mask 13) (pidn 6156 13) PJ3.S PJ3.SI 5 (SW.getD 3 [])
    (SY.F 4) = true := by
  quickRfl

theorem c131001_sw4 : wordEqK 6156 13 (mask 13) (pidn 6156 13) PJ3.S PJ3.SI 5 (SW.getD 4 [])
    (SY.F 6) = true := by
  quickRfl

theorem c131001_sw5 : wordEqK 6156 13 (mask 13) (pidn 6156 13) PJ3.S PJ3.SI 5 (SW.getD 5 [])
    (SY.F 7) = true := by
  quickRfl

theorem c131001_wb0 : jWB CFSG.HardMathSupport.Foote.E27.j3WordG1 (SY.F 0) = true := by
  quickRfl

theorem c131001_wb1 : jWB CFSG.HardMathSupport.Foote.E27.j3WordG2 (SY.F 1) = true := by
  quickRfl

theorem c131001_wb2 : jWB CFSG.HardMathSupport.Foote.E27.j3WordA1 (SY.F 3) = true := by
  quickRfl

theorem c131001_wb3 : jWB CFSG.HardMathSupport.Foote.E27.j3WordB1 (SY.F 4) = true := by
  quickRfl

theorem c131001_wb4 : jWB CFSG.HardMathSupport.Foote.E27.j3WordA2 (SY.F 6) = true := by
  quickRfl

theorem c131001_wb5 : jWB CFSG.HardMathSupport.Foote.E27.j3WordB2 (SY.F 7) = true := by
  quickRfl

end CFSG.KD.E27J3S

end
