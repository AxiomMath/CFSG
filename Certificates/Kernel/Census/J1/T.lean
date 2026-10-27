module

public import Certificates.Kernel.Census.J1.Data
import all Certificates.Kernel.Census.J1.Data
import all Certificates.Data.CFSGNative.MonsterB.Co2Chain
import all Certificates.Data.Kernel.Census.Packed
import all Certificates.Data.Kernel.Census.PackedF
import all CFSG.Certificates.Kernel.Enum.Defs
import all Mathlib.Data.List.Sort
import all Init.Data.Nat.Fold
import all Init.Data.Range.Basic
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelCensus.J1

open CFSG.KC.Census CFSG.KC.Enum

set_option maxRecDepth 1000000

theorem kGv : j1GP.toList.all (pvalid 3080 12) = true := by quickRfl

theorem kSlp : pslpOK 3080 12 j1GP j1Prog = true := by quickRfl

theorem kS : penumOK 3080 12 j1SG [0, 1, 2] j1CS = true := by quickRfl

theorem kX : ((List.range j1GP.size).all fun k => pvalid 3080 12 j1GP[k]!) = true := by quickRfl

theorem kG : ((List.range j1SG.size).all fun k => inXP j1SG[k]!) = true := by quickRfl

theorem kNs : Nat.beq j1Nodes.size 7 = true := by quickRfl

theorem kCs : Nat.beq j1CS.pts.size 8 = true := by quickRfl

theorem kPL : Nat.beq j1Prog.length 459 = true := by quickRfl

theorem kRS : Nat.beq j1RegsP.size 463 = true := by quickRfl

theorem kGS : Nat.beq j1GP.size 2 = true := by quickRfl

theorem kI0 : Nat.beq j1RegsP[2]! (pinv 3080 12 j1GP[0]!) = true := by quickRfl

theorem kI1 : Nat.beq j1RegsP[3]! (pinv 3080 12 j1GP[1]!) = true := by quickRfl

theorem kIdx : pslpIdxOK (2 * j1GP.size) j1Prog = true := by quickRfl

theorem kGs : (Nat.beq j1RegsP[0]! j1GP[0]! && Nat.beq j1RegsP[1]! j1GP[1]!) = true := by quickRfl

theorem kT0 : (List.range' 0 60).all stepF = true := by quickRfl
theorem kT60 : (List.range' 60 60).all stepF = true := by quickRfl
theorem kT120 : (List.range' 120 60).all stepF = true := by quickRfl
theorem kT180 : (List.range' 180 60).all stepF = true := by quickRfl
theorem kT240 : (List.range' 240 60).all stepF = true := by quickRfl
theorem kT300 : (List.range' 300 60).all stepF = true := by quickRfl
theorem kT360 : (List.range' 360 60).all stepF = true := by quickRfl
theorem kTt : (List.range' 420 39).all stepF = true := by quickRfl

end CertificateChecks.KernelCensus.J1

end
