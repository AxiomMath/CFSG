module

public import Certificates.Kernel.BabyMonster.RegTab
public import CFSG.Certificates.Kernel.BabyMonster.Max15.All
public import CFSG.Certificates.Kernel.BabyMonster.Max15.CheckSq
public import CFSG.Certificates.Kernel.BabyMonster.Seeds.Check0
public import CFSG.Certificates.Kernel.BabyMonster.Seeds.Check2
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BFiveAInputs
public import CFSG.Certificates.Kernel.BabyMonster.Max15.Check0
public import CFSG.Certificates.Kernel.BabyMonster.Max15.Check1
public import CFSG.Certificates.Kernel.BabyMonster.Max15.Check2
public import CFSG.Certificates.Kernel.BabyMonster.Max15.Check3
public import CFSG.Certificates.Kernel.BabyMonster.Max15.Check4
public import CFSG.Certificates.Kernel.BabyMonster.Max15.Check5
public import Certificates.Data.CFSGNative.MonsterB.IntertwinerCheck

public section

namespace CertificateChecks.KernelBM.Max15Run

open CFSG.KC.BM CFSG.KC.BM.Reg CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Native

theorem max15_regs : RegsOK (max15Prog ()) [(1, some Seeds.A1), (2, some Seeds.A2)] true [1, 2]
    [Max15.g1, Max15.g2] := by
  bm_reg_cert [CFSG.KC.BM.Max15, CFSG.KC.BM.Seeds]

theorem max15_g1 (a b : GL (Fin 4370) (ZMod 2)) (ha : (a : Mat) = stripMat Seeds.A1)
    (hb : (b : Mat) = stripMat Seeds.A2) :
    ((CFSG.Monster.B.Pinned.runG (max15Prog ()) a b 1 : GL (Fin 4370) (ZMod 2)) : Mat) =
      stripMat Max15.g1 :=
  max15_regs.runG a b ha hb 0 (by decide)

theorem max15_g2 (a b : GL (Fin 4370) (ZMod 2)) (ha : (a : Mat) = stripMat Seeds.A1)
    (hb : (b : Mat) = stripMat Seeds.A2) :
    ((CFSG.Monster.B.Pinned.runG (max15Prog ()) a b 2 : GL (Fin 4370) (ZMod 2)) : Mat) =
      stripMat Max15.g2 :=
  max15_regs.runG a b ha hb 1 (by decide)

end CertificateChecks.KernelBM.Max15Run

end
