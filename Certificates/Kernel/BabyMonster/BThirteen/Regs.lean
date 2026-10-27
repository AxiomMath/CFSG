module

public import Certificates.Kernel.BabyMonster.RegTabMat
public import CFSG.Certificates.Kernel.BabyMonster.BThirteen.All
public import CFSG.Certificates.Kernel.BabyMonster.Seeds.Check0
public import CFSG.Certificates.Kernel.BabyMonster.Seeds.Check2
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThirteenInputs
public import CFSG.Certificates.Kernel.BabyMonster.BThirteen.Check0
public import CFSG.Certificates.Kernel.BabyMonster.BThirteen.Check1
public import CFSG.Certificates.Kernel.BabyMonster.BThirteen.Check10
public import CFSG.Certificates.Kernel.BabyMonster.BThirteen.Check11
public import CFSG.Certificates.Kernel.BabyMonster.BThirteen.Check12
public import CFSG.Certificates.Kernel.BabyMonster.BThirteen.Check13
public import CFSG.Certificates.Kernel.BabyMonster.BThirteen.Check14
public import CFSG.Certificates.Kernel.BabyMonster.BThirteen.Check15
public import CFSG.Certificates.Kernel.BabyMonster.BThirteen.Check16
public import CFSG.Certificates.Kernel.BabyMonster.BThirteen.Check17
public import CFSG.Certificates.Kernel.BabyMonster.BThirteen.Check18
public import CFSG.Certificates.Kernel.BabyMonster.BThirteen.Check19
public import CFSG.Certificates.Kernel.BabyMonster.BThirteen.Check2
public import CFSG.Certificates.Kernel.BabyMonster.BThirteen.Check20
public import CFSG.Certificates.Kernel.BabyMonster.BThirteen.Check21
public import CFSG.Certificates.Kernel.BabyMonster.BThirteen.Check22
public import CFSG.Certificates.Kernel.BabyMonster.BThirteen.Check23
public import CFSG.Certificates.Kernel.BabyMonster.BThirteen.Check24
public import CFSG.Certificates.Kernel.BabyMonster.BThirteen.Check25
public import CFSG.Certificates.Kernel.BabyMonster.BThirteen.Check26
public import CFSG.Certificates.Kernel.BabyMonster.BThirteen.Check3
public import CFSG.Certificates.Kernel.BabyMonster.BThirteen.Check4
public import CFSG.Certificates.Kernel.BabyMonster.BThirteen.Check5
public import CFSG.Certificates.Kernel.BabyMonster.BThirteen.Check6
public import CFSG.Certificates.Kernel.BabyMonster.BThirteen.Check7
public import CFSG.Certificates.Kernel.BabyMonster.BThirteen.Check8
public import CFSG.Certificates.Kernel.BabyMonster.BThirteen.Check9
public import CFSG.Certificates.Kernel.BabyMonster.BThirteen.Ne
public import CFSG.Certificates.Kernel.BabyMonster.BThirteen.RkT1
public import CFSG.Certificates.Kernel.BabyMonster.BThirteen.RkT2
public import CFSG.Certificates.Kernel.BabyMonster.BThirteen.RkT4
public import CFSG.Certificates.Kernel.BabyMonster.BThirteen.Wf

public section

namespace CertificateChecks.KernelBM.BThirteen

open CFSG.KC.BM CFSG.KC.BM.Reg CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Native

theorem b13_regs : RegsOK (b13Prog ()) [(1, some Seeds.A1), (2, some Seeds.A2)] true
    [31, 32, 44, 45, 46, 81] [BThirteen.X, BThirteen.S, BThirteen.T2, BThirteen.T4, BThirteen.T5,
      BThirteen.G] := by
  bm_reg_cert_mat [CFSG.KC.BM.BThirteen, CFSG.KC.BM.Seeds]

end CertificateChecks.KernelBM.BThirteen

end
