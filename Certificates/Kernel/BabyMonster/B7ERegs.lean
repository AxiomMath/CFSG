module

public import Certificates.Kernel.BabyMonster.RegTab
public import CFSG.Certificates.Kernel.BabyMonster.Seven.All
public import CFSG.Certificates.Kernel.BabyMonster.SevenElem.Check0
public import CFSG.Certificates.Kernel.BabyMonster.SevenGen.Order
public import CFSG.Certificates.Kernel.BabyMonster.B7Reg.All
public import CFSG.Certificates.Kernel.BabyMonster.Seeds.Check0
public import CFSG.Certificates.Kernel.BabyMonster.Seeds.Check2
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSevenElementsInputs
public import CFSG.Certificates.Kernel.BabyMonster.B7Reg.Check0
public import CFSG.Certificates.Kernel.BabyMonster.B7Reg.Check1
public import CFSG.Certificates.Kernel.BabyMonster.B7Reg.Check2
public import CFSG.Certificates.Kernel.BabyMonster.Seven.Check0
public import CFSG.Certificates.Kernel.BabyMonster.Seven.Check1
public import CFSG.Certificates.Kernel.BabyMonster.Seven.Check10
public import CFSG.Certificates.Kernel.BabyMonster.Seven.Check2
public import CFSG.Certificates.Kernel.BabyMonster.Seven.Check3
public import CFSG.Certificates.Kernel.BabyMonster.Seven.Check4
public import CFSG.Certificates.Kernel.BabyMonster.Seven.Check5
public import CFSG.Certificates.Kernel.BabyMonster.Seven.Check6
public import CFSG.Certificates.Kernel.BabyMonster.Seven.Check7
public import CFSG.Certificates.Kernel.BabyMonster.Seven.Check8
public import CFSG.Certificates.Kernel.BabyMonster.Seven.Check9

public section

namespace CertificateChecks.KernelBM.B7ERegs

open CFSG.KC.BM CFSG.KC.BM.Reg CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Native

set_option maxRecDepth 100000

theorem b7E_regs : RegsOK (b7EProg ()) [(1, some Seeds.A1), (2, some Seeds.A2)] true
    [2, 5, 7, 11, 6, 16] [B7Reg.a0, Seven.x, B7Reg.yb, Seven.t1, B7Reg.t2b, B7Reg.eb] := by
  bm_reg_cert [CFSG.KC.BM.B7Reg, CFSG.KC.BM.Seven, CFSG.KC.BM.SevenElem, CFSG.KC.BM.SevenGen,
    CFSG.KC.BM.Seeds]

theorem a0_eq : B7Reg.a0 = Seven.al := rfl

theorem yb_eq : B7Reg.yb = Seven.y := rfl

theorem t2b_eq : B7Reg.t2b = Seven.t2 := rfl

theorem eb_eq : B7Reg.eb = Seven.e3 := rfl

end CertificateChecks.KernelBM.B7ERegs

end
