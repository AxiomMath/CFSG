module

public import Certificates.Kernel.Co1M.K73D
public import Certificates.Data.Kernel.Co1M.Odd73F
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CFSG.KD.Co1M

open CFSG.KC.Co1F2 CFSG.KC.M1F2 CFSG.KD.Co1Odd CFSG.KLie.CT CFSG.KC.Odd73 CFSG.KC.SortTree
  CFSG.KC.InvFam

theorem z73_z0 : (treeOK71 Z0G Z0P Z0Par Z0Lab 384 && distinctL Z0P && canonL Z0P &&
    Z0G == [getL 0 R73 77, getL 0 R73 78, getL 0 R73 79, getL 0 R73 80]) = true := by quickRfl

theorem z73_faith : (faithK (trK 24 (getL 0 R73 27)) (trK 24 (getL 0 R73 73)) Z1P FV1 &&
    faithK (trK 24 (getL 0 R73 27)) (trK 24 (getL 0 R73 76)) Z2P FV2) = true := by quickRfl

theorem z73_aux : (allN 4 (fun c => Nat.beq (preA (A73tab 0) c) 0) &&
    allN 4 (fun c => Nat.beq (preA (A73tab 182919) c) (getL 0 [7168, 2048, 28672, 759] c))) =
    true := by quickRfl

theorem z73_canon : canonL R73 = true := by quickRfl

theorem z73_t1 : andB (Nat.blt 168617 182919) (andB (Nat.beq (valF 576 (S73tab 168617))
    (getL 0 R73 86)) (Nat.beq (clsA (A73tab 168617)) 5)) = true := by quickRfl

theorem z73_neg : (!chunksK (act73 R73) 14 (getL 0 R73 86) S73tab 182919 576 4 18 64 2691 1 &&
    !allN 1 (fun c => auxRun73 R73 S73tab (fun i => A73tab (i + 1)) 576 4 18 (c * 64) 64) &&
    !faithK (trK 24 (getL 0 R73 27)) (trK 24 (getL 0 R73 76)) Z2P (FV2.set 5 (FV2.getD 4 0 + 1)) &&
    !treeOK71 Z0G Z0P Z0Par Z0Lab 383 &&
    !allN 4 (fun c => Nat.beq (preA (A73tab 182919) c) (getL 0 [7168, 2048, 28671, 759] c))) =
    true := by quickRfl

end CFSG.KD.Co1M

end
