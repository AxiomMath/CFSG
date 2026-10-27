module

public import Certificates.Kernel.SporSch.Mathieu.Gen
public import CFSG.Quasithin.Recognition.St84.AutJ2VtxInputs
public meta import CFSG.Quasithin.Recognition.St84.AutJ2VtxInputs
public import Certificates.Kernel.AutJ2Vtx.ChainWords
public meta import Certificates.Kernel.AutJ2Vtx.ChainWords
import CFSG.Certificates.Kernel.Common.Harness
public meta import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutOddCore
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutOddCore
public meta import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions
public import CFSG.Sporadic.J2
public meta import CFSG.Sporadic.J2
public import CFSG.Sporadic.SmallOddCore.LocalSpec
public meta import CFSG.Sporadic.SmallOddCore.LocalSpec
public meta import CFSG.Sporadic.Th.F2Spec
public import CFSG.Sporadic.Th.F2Spec

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelAJC

open CFSG.KS.SporSch.MOCG CFSG.Quasithin.F112R.St84.AutJ2Model

meta def aj (k : Nat) : Array Nat := ((autJ2Tbls.getD k #[]).toList.map UInt32.toNat).toArray

meta def ajs (ks : List Nat) : Array (Array Nat) := (ks.map aj).toArray


meta def sS : Array (Array Nat) := strongOf 315 (ajs [0, 1, 2]) wS
meta def sW : Array (Array Nat) := strongOf 315 (ajs [0, 1, 2, 6]) wW
meta def sX1 : Array (Array Nat) := strongOf 315 (ajs [0, 1, 2, 7]) wX1
meta def sQ2 : Array (Array Nat) := strongOf 315 (ajs [8, 9, 10, 11]) wQ2
meta def sA : Array (Array Nat) := strongOf 315 (ajs [21, 20, 18, 19]) wA
meta def sQ1 : Array (Array Nat) := strongOf 315 (ajs [14, 15, 16, 17]) wQ1

meta def bS : Array Nat := #[1, 3]
meta def bW : Array Nat := #[1, 2, 3]
meta def bX1 : Array Nat := #[0, 1, 3]
meta def bQ2 : Array Nat := #[1]
meta def bA : Array Nat := #[0, 1]
meta def bQ1 : Array Nat := #[1, 3]

end CertificateChecks.KernelAJC

#ks_rawchain CertificateChecks.KernelAJC.AJS 315 9 315 CertificateChecks.KernelAJC.sS
  CertificateChecks.KernelAJC.bS 3 CertificateChecks.KernelAJC.wS

#ks_rawchain CertificateChecks.KernelAJC.AJW 315 9 315 CertificateChecks.KernelAJC.sW
  CertificateChecks.KernelAJC.bW 4 CertificateChecks.KernelAJC.wW

#ks_rawchain CertificateChecks.KernelAJC.AJX1 315 9 315 CertificateChecks.KernelAJC.sX1
  CertificateChecks.KernelAJC.bX1 4 CertificateChecks.KernelAJC.wX1

#ks_rawchain CertificateChecks.KernelAJC.AJQ2 315 9 315 CertificateChecks.KernelAJC.sQ2
  CertificateChecks.KernelAJC.bQ2 4 CertificateChecks.KernelAJC.wQ2

#ks_rawchain CertificateChecks.KernelAJC.AJA 315 9 315 CertificateChecks.KernelAJC.sA
  CertificateChecks.KernelAJC.bA 4 CertificateChecks.KernelAJC.wA

#ks_rawchain CertificateChecks.KernelAJC.AJQ1 315 9 315 CertificateChecks.KernelAJC.sQ1
  CertificateChecks.KernelAJC.bQ1 4 CertificateChecks.KernelAJC.wQ1

namespace CertificateChecks.KernelAJC

open CFSG.KC.Enum CFSG.KS.SporSch.MOC

theorem kNS : Nat.beq (ordK AJS.LR 2) 256 = true := by quickRfl
theorem kNW : Nat.beq (ordK AJW.LR 3) 3840 = true := by quickRfl
theorem kNX1 : Nat.beq (ordK AJX1.LR 3) 2304 = true := by quickRfl
theorem kNQ2 : Nat.beq (ordK AJQ2.LR 1) 32 = true := by quickRfl
theorem kNA : Nat.beq (ordK AJA.LR 2) 36 = true := by quickRfl
theorem kNQ1 : Nat.beq (ordK AJQ1.LR 2) 64 = true := by quickRfl

end CertificateChecks.KernelAJC

end
