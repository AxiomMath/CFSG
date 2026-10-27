module

public import Certificates.Kernel.Co2Cent.Data
public import Certificates.Kernel.Co2Cent.CentData
public import Certificates.Kernel.Co2Cent.CentBData
public import Certificates.Kernel.Co2Cent.CentLData
public import Certificates.Data.Kernel.OrbRow.CentB
public import Certificates.Data.Kernel.OrbRow.CentL
public import Certificates.Data.U42Presentation
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CFSG.KD.Co2Cent

open CFSG.KC.Enum CFSG.KC.OrbRow CFSG.KC.PGrp

@[expose] noncomputable def u42N : List (List (Nat × Bool)) :=
  CFSG.HardMathSupport.Dickson.I271.U42Presentation.u42Words.map
    (List.map fun l => (l.1.val, l.2))

@[expose] noncomputable def oUV (i : Nat) : Nat := nIf(Nat.beq i 0, 2, 5)

theorem ch17351_lx : bAnd(powIdK 2300 12 4095 xB 3, movesK 2300 12 4095 xB) = true := by
  quickRfl

theorem ch17351_lw : bAnd(wordEqK 2300 12 SB 17 (getS MB 0) (getS SL 0) (getLs WU 0),
    bAnd(wordEqK 2300 12 SB 17 (getS MB 0) (getS SL 1) (getLs WU 1),
      wordEqK 2300 12 SB 17 (getS MB 0) xB (getLs WU 2))) = true := by
  quickRfl

theorem ch17351_lc : lvCommK 2300 12 4095 SL 6 3 xB = true := by
  quickRfl

theorem ch17351_lr : relK 2300 12 SL oUV u42N = true := by
  quickRfl

theorem ch17351_lf : bAnd(movLvK 12 4095 SL 6 (getS ML 1) 2 FB,
    allN 6 (fun i => bIf(Nat.beq i 1, true, inD (getS DL 0) (getS BB i)))) = true := by
  quickRfl

end CFSG.KD.Co2Cent

end
