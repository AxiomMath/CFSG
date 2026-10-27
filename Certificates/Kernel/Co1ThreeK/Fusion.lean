module

public import Certificates.Kernel.Co1ThreeK.DataQ
public import Certificates.Kernel.Co1ThreeK.Coset
public import Certificates.Data.Kernel.Co1Three.QModel
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1ThreeK

open CFSG.KC.Enum CFSG.KC.Co1Cl CFSG.KC.Co1B CFSG.KC.Co1F2 CFSG.KS.SporSch.M24
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1T

@[expose] noncomputable def QB : List (List Nat) := [getLL CS.NR 3, getLL CS.NR 4]

theorem kQRel : (Nat.beq (lenL FM.RL) 54 && relQK 729 27 12 9 CS.Q FM.RL) = true := by quickRfl

theorem kQTab : (Nat.beq (TS 12) oneK && tabQK 3 6 729 27 CS.TR QB FM.RL CS.W FM.TT) = true := by
  quickRfl

theorem kQAdd : adtQK FM.ADT = true := by quickRfl

theorem kQAct : atQK 27 FM.ADT CS.TR FM.AT = true := by quickRfl

theorem kQGC : (Nat.beq (lenL FM.GC) 8 && allN 8 fun g => Nat.blt (getL 0 FM.GC g) 19683) = true :=
  by quickRfl

theorem kQRep : (Nat.beq (lenL FM.RP) 42 && Nat.beq (lenL Data.repRoot) 42 &&
    allN 42 fun i => strictB (getL 0 FM.RP i) fun r => strictB (getL 0 Data.repRoot i) fun j =>
      bAnd(Nat.blt r 19683, bAnd(Nat.blt j 3, bAnd(lettersK 75 (getLL Data.repConj i),
        strictB (wordWK L.M L.MI (getLL Data.repConj i)) fun n =>
          Nat.beq (mulWK n (mdlK TS 3 729 12 (getLL EG 0) r)) (mulWK (R.M j) n))))) = true := by
  quickRfl

end CertificateChecks.KernelCo1ThreeK

end
