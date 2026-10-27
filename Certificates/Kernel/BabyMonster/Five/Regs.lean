module

public import Certificates.Kernel.BabyMonster.RegTabTwin
public import CFSG.Certificates.Kernel.BabyMonster.Five.All
public import CFSG.Certificates.Kernel.BabyMonster.Seeds.Check0
public import CFSG.Certificates.Kernel.BabyMonster.Seeds.Check2
public import Certificates.Data.CFSGNative.MonsterB.Primes
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check0
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check1
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check10
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check11
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check12
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check13
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check14
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check15
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check16
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check17
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check18
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check19
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check2
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check20
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check21
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check22
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check23
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check24
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check25
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check26
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check27
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check28
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check29
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check3
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check30
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check31
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check32
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check33
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check34
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check35
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check36
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check37
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check38
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check39
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check4
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check40
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check41
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check42
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check43
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check44
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check45
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check46
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check47
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check48
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check49
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check5
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check50
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check51
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check52
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check53
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check54
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check55
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check56
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check57
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check58
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check59
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check6
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check60
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check61
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check62
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check63
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check64
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check65
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check66
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check67
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check68
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check69
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check7
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check70
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check71
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check72
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check73
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check74
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check75
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check8
public import CFSG.Certificates.Kernel.BabyMonster.Five.Check9

public section

namespace CertificateChecks.KernelBM.Five

open CFSG.KC.BM CFSG.KC.BM.Reg CFSG.Monster.B.Primes.Native

theorem five_regs : RegsOK fiveProg [(1, some Seeds.A1), (2, some Seeds.A2)] true [1, 2]
    [CFSG.KC.BM.Five.f85, CFSG.KC.BM.Five.f86] := by
  bm_reg_cert_twin [CFSG.KC.BM.Five, CFSG.KC.BM.Seeds]

end CertificateChecks.KernelBM.Five

end
