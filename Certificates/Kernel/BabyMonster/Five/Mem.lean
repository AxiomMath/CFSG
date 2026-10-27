module

public import Certificates.Kernel.BabyMonster.MemChain
public import Certificates.Kernel.BabyMonster.Chain2
public import CFSG.Certificates.Kernel.BabyMonster.Five.All
public import CFSG.Certificates.Kernel.BabyMonster.Seeds.All
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
public import CFSG.Certificates.Kernel.BabyMonster.Seeds.Check0
public import CFSG.Certificates.Kernel.BabyMonster.Seeds.Check1
public import CFSG.Certificates.Kernel.BabyMonster.Seeds.Check2
public import CFSG.Certificates.Kernel.BabyMonster.Seeds.Check3
public import CFSG.Certificates.Kernel.BabyMonster.Seeds.Check4

public section

namespace CFSG.KC.BM.FiveMem

open CFSG.KC.BM CFSG.KC.BM.MemChain

local notation "sm" => stripMat

variable {S : Submonoid (Matrix (Fin 4370) (Fin 4370) (ZMod 2))}

theorem five_mem (hA1 : sm Seeds.A1 ∈ S) (hA2 : sm Seeds.A2 ∈ S) :
    sm Five.f85 ∈ S ∧ sm Five.f86 ∈ S := by
  have m_f0 : sm Five.f0 ∈ S := mem1 Seeds.wf_A1 Seeds.wf_A2 Five.wf_f0 hA1 hA2 (by bm_strips2 CFSG.KC.BM.Five.cf0 69)
  have m_f1 : sm Five.f1 ∈ S := mem1 Five.wf_f0 Seeds.wf_A2 Five.wf_f1 m_f0 hA2 (by bm_strips2 CFSG.KC.BM.Five.cf1 69)
  have m_f2 : sm Five.f2 ∈ S := mem1 Five.wf_f0 Five.wf_f0 Five.wf_f2 m_f0 m_f0 (by bm_strips2 CFSG.KC.BM.Five.cf2 69)
  have m_f3 : sm Five.f3 ∈ S := mem1 Five.wf_f2 Five.wf_f2 Five.wf_f3 m_f2 m_f2 (by bm_strips2 CFSG.KC.BM.Five.cf3 69)
  have m_f4 : sm Five.f4 ∈ S := mem1 Five.wf_f3 Five.wf_f1 Five.wf_f4 m_f3 m_f1 (by bm_strips2 CFSG.KC.BM.Five.cf4 69)
  have m_f5 : sm Five.f5 ∈ S := mem1 Five.wf_f4 Five.wf_f4 Five.wf_f5 m_f4 m_f4 (by bm_strips2 CFSG.KC.BM.Five.cf5 69)
  have m_f6 : sm Five.f6 ∈ S := mem1 Five.wf_f4 Five.wf_f5 Five.wf_f6 m_f4 m_f5 (by bm_strips2 CFSG.KC.BM.Five.cf6 69)
  have m_f7 : sm Five.f7 ∈ S := mem1 Five.wf_f6 Five.wf_f6 Five.wf_f7 m_f6 m_f6 (by bm_strips2 CFSG.KC.BM.Five.cf7 69)
  have m_f8 : sm Five.f8 ∈ S := mem1 Five.wf_f7 Five.wf_f7 Five.wf_f8 m_f7 m_f7 (by bm_strips2 CFSG.KC.BM.Five.cf8 69)
  have m_f9 : sm Five.f9 ∈ S := mem1 Five.wf_f8 Five.wf_f8 Five.wf_f9 m_f8 m_f8 (by bm_strips2 CFSG.KC.BM.Five.cf9 69)
  have m_f10 : sm Five.f10 ∈ S := mem1 Seeds.wf_A1 Five.wf_f9 Five.wf_f10 hA1 m_f9 (by bm_strips2 CFSG.KC.BM.Five.cf10 69)
  have m_f11 : sm Five.f11 ∈ S := mem1 Five.wf_f10 Five.wf_f10 Five.wf_f11 m_f10 m_f10 (by bm_strips2 CFSG.KC.BM.Five.cf11 69)
  have m_f12 : sm Five.f12 ∈ S := mem1 Five.wf_f11 Five.wf_f4 Five.wf_f12 m_f11 m_f4 (by bm_strips2 CFSG.KC.BM.Five.cf12 69)
  have m_f13 : sm Five.f13 ∈ S := mem1 Five.wf_f12 Five.wf_f4 Five.wf_f13 m_f12 m_f4 (by bm_strips2 CFSG.KC.BM.Five.cf13 69)
  have m_f14 : sm Five.f14 ∈ S := mem1 Five.wf_f12 Five.wf_f12 Five.wf_f14 m_f12 m_f12 (by bm_strips2 CFSG.KC.BM.Five.cf14 69)
  have m_f15 : sm Five.f15 ∈ S := mem1 Five.wf_f13 Five.wf_f12 Five.wf_f15 m_f13 m_f12 (by bm_strips2 CFSG.KC.BM.Five.cf15 69)
  have m_f16 : sm Five.f16 ∈ S := mem1 Five.wf_f14 Five.wf_f15 Five.wf_f16 m_f14 m_f15 (by bm_strips2 CFSG.KC.BM.Five.cf16 69)
  have m_f17 : sm Five.f17 ∈ S := mem1 Five.wf_f16 Five.wf_f16 Five.wf_f17 m_f16 m_f16 (by bm_strips2 CFSG.KC.BM.Five.cf17 69)
  have m_f18 : sm Five.f18 ∈ S := mem1 Five.wf_f16 Five.wf_f17 Five.wf_f18 m_f16 m_f17 (by bm_strips2 CFSG.KC.BM.Five.cf18 69)
  have m_f19 : sm Five.f19 ∈ S := mem1 Five.wf_f17 Five.wf_f18 Five.wf_f19 m_f17 m_f18 (by bm_strips2 CFSG.KC.BM.Five.cf19 69)
  have m_f20 : sm Five.f20 ∈ S := mem1 Five.wf_f12 Five.wf_f13 Five.wf_f20 m_f12 m_f13 (by bm_strips2 CFSG.KC.BM.Five.cf20 69)
  have m_f21 : sm Five.f21 ∈ S := mem1 Five.wf_f20 Five.wf_f20 Five.wf_f21 m_f20 m_f20 (by bm_strips2 CFSG.KC.BM.Five.cf21 69)
  have m_f22 : sm Five.f22 ∈ S := mem1 Five.wf_f4 Five.wf_f21 Five.wf_f22 m_f4 m_f21 (by bm_strips2 CFSG.KC.BM.Five.cf22 69)
  have m_f23 : sm Five.f23 ∈ S := mem1 Five.wf_f22 Five.wf_f22 Five.wf_f23 m_f22 m_f22 (by bm_strips2 CFSG.KC.BM.Five.cf23 69)
  have m_f24 : sm Five.f24 ∈ S := mem1 Five.wf_f23 Five.wf_f23 Five.wf_f24 m_f23 m_f23 (by bm_strips2 CFSG.KC.BM.Five.cf24 69)
  have m_f25 : sm Five.f25 ∈ S := mem1 Five.wf_f13 Five.wf_f21 Five.wf_f25 m_f13 m_f21 (by bm_strips2 CFSG.KC.BM.Five.cf25 69)
  have m_f26 : sm Five.f26 ∈ S := mem1 Five.wf_f25 Five.wf_f20 Five.wf_f26 m_f25 m_f20 (by bm_strips2 CFSG.KC.BM.Five.cf26 69)
  have m_f27 : sm Five.f27 ∈ S := memI Five.wf_f26 Five.wf_f27 m_f26 (by bm_strips2 CFSG.KC.BM.Five.cf27 69)
  have m_f28 : sm Five.f28 ∈ S := mem1 Five.wf_f27 Five.wf_f24 Five.wf_f28 m_f27 m_f24 (by bm_strips2 CFSG.KC.BM.Five.cf28 69)
  have m_f29 : sm Five.f29 ∈ S := mem1 Five.wf_f28 Five.wf_f26 Five.wf_f29 m_f28 m_f26 (by bm_strips2 CFSG.KC.BM.Five.cf29 69)
  have m_f30 : sm Five.f30 ∈ S := mem1 Five.wf_f19 Five.wf_f29 Five.wf_f30 m_f19 m_f29 (by bm_strips2 CFSG.KC.BM.Five.cf30 69)
  have m_f30_sq1 : sm Five.f30_sq1 ∈ S := mem1 Five.wf_f30 Five.wf_f30 Five.wf_f30_sq1 m_f30 m_f30 (by bm_strips2 CFSG.KC.BM.Five.cf30_sq1 69)
  have m_f30_sq2 : sm Five.f30_sq2 ∈ S := mem1 Five.wf_f30_sq1 Five.wf_f30_sq1 Five.wf_f30_sq2 m_f30_sq1 m_f30_sq1 (by bm_strips2 CFSG.KC.BM.Five.cf30_sq2 69)
  have m_f31 : sm Five.f31 ∈ S := mem1 Five.wf_f30 Five.wf_f29 Five.wf_f31 m_f30 m_f29 (by bm_strips2 CFSG.KC.BM.Five.cf31 69)
  have m_f32 : sm Five.f32 ∈ S := mem1 Five.wf_f31 Five.wf_f29 Five.wf_f32 m_f31 m_f29 (by bm_strips2 CFSG.KC.BM.Five.cf32 69)
  have m_f33 : sm Five.f33 ∈ S := mem1 Five.wf_f32 Five.wf_f29 Five.wf_f33 m_f32 m_f29 (by bm_strips2 CFSG.KC.BM.Five.cf33 69)
  have m_f33_sq1 : sm Five.f33_sq1 ∈ S := mem1 Five.wf_f33 Five.wf_f33 Five.wf_f33_sq1 m_f33 m_f33 (by bm_strips2 CFSG.KC.BM.Five.cf33_sq1 69)
  have m_f33_sq2 : sm Five.f33_sq2 ∈ S := mem1 Five.wf_f33_sq1 Five.wf_f33_sq1 Five.wf_f33_sq2 m_f33_sq1 m_f33_sq1 (by bm_strips2 CFSG.KC.BM.Five.cf33_sq2 69)
  have m_f33_sq3 : sm Five.f33_sq3 ∈ S := mem1 Five.wf_f33_sq2 Five.wf_f33_sq2 Five.wf_f33_sq3 m_f33_sq2 m_f33_sq2 (by bm_strips2 CFSG.KC.BM.Five.cf33_sq3 69)
  have m_f33_sq4 : sm Five.f33_sq4 ∈ S := mem1 Five.wf_f33_sq3 Five.wf_f33_sq3 Five.wf_f33_sq4 m_f33_sq3 m_f33_sq3 (by bm_strips2 CFSG.KC.BM.Five.cf33_sq4 69)
  have m_f34 : sm Five.f34 ∈ S := mem2 Five.wf_f31 Five.wf_f31 Five.wf_f31 Five.wf_f34 m_f31 m_f31 m_f31 (by bm_strips2 CFSG.KC.BM.Five.cf34 69)
  have m_f35 : sm Five.f35 ∈ S := mem1 Five.wf_f32 Five.wf_f32 Five.wf_f35 m_f32 m_f32 (by bm_strips2 CFSG.KC.BM.Five.cf35 69)
  have m_f36 : sm Five.f36 ∈ S := mem1 Five.wf_f30 Five.wf_f30 Five.wf_f36 m_f30 m_f30 (by bm_strips2 CFSG.KC.BM.Five.cf36 69)
  have m_f37 : sm Five.f37 ∈ S := mem1 Five.wf_f36 Five.wf_f35 Five.wf_f37 m_f36 m_f35 (by bm_strips2 CFSG.KC.BM.Five.cf37 69)
  have m_f37_sq1 : sm Five.f37_sq1 ∈ S := mem1 Five.wf_f37 Five.wf_f37 Five.wf_f37_sq1 m_f37 m_f37 (by bm_strips2 CFSG.KC.BM.Five.cf37_sq1 69)
  have m_f37_sq2 : sm Five.f37_sq2 ∈ S := mem1 Five.wf_f37_sq1 Five.wf_f37_sq1 Five.wf_f37_sq2 m_f37_sq1 m_f37_sq1 (by bm_strips2 CFSG.KC.BM.Five.cf37_sq2 69)
  have m_f38 : sm Five.f38 ∈ S := mem1 Five.wf_f37 Five.wf_f37_sq2 Five.wf_f38 m_f37 m_f37_sq2 (by bm_strips2 CFSG.KC.BM.Five.cf38 69)
  have m_f39 : sm Five.f39 ∈ S := mem1 Five.wf_f33_sq2 Five.wf_f33_sq4 Five.wf_f39 m_f33_sq2 m_f33_sq4 (by bm_strips2 CFSG.KC.BM.Five.cf39 69)
  have m_f40 : sm Five.f40 ∈ S := mem1 Five.wf_f30_sq1 Five.wf_f30_sq2 Five.wf_f40 m_f30_sq1 m_f30_sq2 (by bm_strips2 CFSG.KC.BM.Five.cf40 69)
  have m_f41 : sm Five.f41 ∈ S := mem1 Five.wf_f39 Five.wf_f40 Five.wf_f41 m_f39 m_f40 (by bm_strips2 CFSG.KC.BM.Five.cf41 69)
  have m_f42 : sm Five.f42 ∈ S := memI Five.wf_f41 Five.wf_f42 m_f41 (by bm_strips2 CFSG.KC.BM.Five.cf42 69)
  have m_f43 : sm Five.f43 ∈ S := mem1 Five.wf_f42 Five.wf_f38 Five.wf_f43 m_f42 m_f38 (by bm_strips2 CFSG.KC.BM.Five.cf43 69)
  have m_f44 : sm Five.f44 ∈ S := mem1 Five.wf_f43 Five.wf_f41 Five.wf_f44 m_f43 m_f41 (by bm_strips2 CFSG.KC.BM.Five.cf44 69)
  have m_f45 : sm Five.f45 ∈ S := mem1 Five.wf_f34 Five.wf_f44 Five.wf_f45 m_f34 m_f44 (by bm_strips2 CFSG.KC.BM.Five.cf45 69)
  have m_f46 : sm Five.f46 ∈ S := mem1 Five.wf_f45 Five.wf_f44 Five.wf_f46 m_f45 m_f44 (by bm_strips2 CFSG.KC.BM.Five.cf46 69)
  have m_f47 : sm Five.f47 ∈ S := mem1 Five.wf_f45 Five.wf_f46 Five.wf_f47 m_f45 m_f46 (by bm_strips2 CFSG.KC.BM.Five.cf47 69)
  have m_f48 : sm Five.f48 ∈ S := mem1 Five.wf_f45 Five.wf_f47 Five.wf_f48 m_f45 m_f47 (by bm_strips2 CFSG.KC.BM.Five.cf48 69)
  have m_f48_sq1 : sm Five.f48_sq1 ∈ S := mem1 Five.wf_f48 Five.wf_f48 Five.wf_f48_sq1 m_f48 m_f48 (by bm_strips2 CFSG.KC.BM.Five.cf48_sq1 69)
  have m_f48_sq2 : sm Five.f48_sq2 ∈ S := mem1 Five.wf_f48_sq1 Five.wf_f48_sq1 Five.wf_f48_sq2 m_f48_sq1 m_f48_sq1 (by bm_strips2 CFSG.KC.BM.Five.cf48_sq2 69)
  have m_f49 : sm Five.f49 ∈ S := mem1 Five.wf_f48_sq1 Five.wf_f48_sq2 Five.wf_f49 m_f48_sq1 m_f48_sq2 (by bm_strips2 CFSG.KC.BM.Five.cf49 69)
  have m_f50 : sm Five.f50 ∈ S := memI Five.wf_f34 Five.wf_f50 m_f34 (by bm_strips2 CFSG.KC.BM.Five.cf50 69)
  have m_f51 : sm Five.f51 ∈ S := mem1 Five.wf_f49 Five.wf_f50 Five.wf_f51 m_f49 m_f50 (by bm_strips2 CFSG.KC.BM.Five.cf51 69)
  have m_f52 : sm Five.f52 ∈ S := mem1 Five.wf_f49 Five.wf_f34 Five.wf_f52 m_f49 m_f34 (by bm_strips2 CFSG.KC.BM.Five.cf52 69)
  have m_f53 : sm Five.f53 ∈ S := mem1 Five.wf_f51 Five.wf_f52 Five.wf_f53 m_f51 m_f52 (by bm_strips2 CFSG.KC.BM.Five.cf53 69)
  have m_f54 : sm Five.f54 ∈ S := mem1 Five.wf_f53 Five.wf_f53 Five.wf_f54 m_f53 m_f53 (by bm_strips2 CFSG.KC.BM.Five.cf54 69)
  have m_f55 : sm Five.f55 ∈ S := mem1 Five.wf_f34 Five.wf_f54 Five.wf_f55 m_f34 m_f54 (by bm_strips2 CFSG.KC.BM.Five.cf55 69)
  have m_f56 : sm Five.f56 ∈ S := memI Five.wf_f44 Five.wf_f56 m_f44 (by bm_strips2 CFSG.KC.BM.Five.cf56 69)
  have m_f57 : sm Five.f57 ∈ S := mem1 Five.wf_f49 Five.wf_f56 Five.wf_f57 m_f49 m_f56 (by bm_strips2 CFSG.KC.BM.Five.cf57 69)
  have m_f58 : sm Five.f58 ∈ S := mem2 Five.wf_f49 Five.wf_f49 Five.wf_f49 Five.wf_f58 m_f49 m_f49 m_f49 (by bm_strips2 CFSG.KC.BM.Five.cf58 69)
  have m_f59 : sm Five.f59 ∈ S := mem1 Five.wf_f58 Five.wf_f44 Five.wf_f59 m_f58 m_f44 (by bm_strips2 CFSG.KC.BM.Five.cf59 69)
  have m_f60 : sm Five.f60 ∈ S := mem1 Five.wf_f57 Five.wf_f59 Five.wf_f60 m_f57 m_f59 (by bm_strips2 CFSG.KC.BM.Five.cf60 69)
  have m_f61 : sm Five.f61 ∈ S := mem1 Five.wf_f60 Five.wf_f60 Five.wf_f61 m_f60 m_f60 (by bm_strips2 CFSG.KC.BM.Five.cf61 69)
  have m_f62 : sm Five.f62 ∈ S := mem1 Five.wf_f44 Five.wf_f61 Five.wf_f62 m_f44 m_f61 (by bm_strips2 CFSG.KC.BM.Five.cf62 69)
  have m_f63 : sm Five.f63 ∈ S := mem1 Five.wf_f55 Five.wf_f62 Five.wf_f63 m_f55 m_f62 (by bm_strips2 CFSG.KC.BM.Five.cf63 69)
  have m_f64 : sm Five.f64 ∈ S := mem1 Five.wf_f63 Five.wf_f62 Five.wf_f64 m_f63 m_f62 (by bm_strips2 CFSG.KC.BM.Five.cf64 69)
  have m_f65 : sm Five.f65 ∈ S := mem1 Five.wf_f63 Five.wf_f64 Five.wf_f65 m_f63 m_f64 (by bm_strips2 CFSG.KC.BM.Five.cf65 69)
  have m_f66 : sm Five.f66 ∈ S := mem1 Five.wf_f63 Five.wf_f65 Five.wf_f66 m_f63 m_f65 (by bm_strips2 CFSG.KC.BM.Five.cf66 69)
  have m_f66_sq1 : sm Five.f66_sq1 ∈ S := mem1 Five.wf_f66 Five.wf_f66 Five.wf_f66_sq1 m_f66 m_f66 (by bm_strips2 CFSG.KC.BM.Five.cf66_sq1 69)
  have m_f66_sq2 : sm Five.f66_sq2 ∈ S := mem1 Five.wf_f66_sq1 Five.wf_f66_sq1 Five.wf_f66_sq2 m_f66_sq1 m_f66_sq1 (by bm_strips2 CFSG.KC.BM.Five.cf66_sq2 69)
  have m_f66_sq3 : sm Five.f66_sq3 ∈ S := mem1 Five.wf_f66_sq2 Five.wf_f66_sq2 Five.wf_f66_sq3 m_f66_sq2 m_f66_sq2 (by bm_strips2 CFSG.KC.BM.Five.cf66_sq3 69)
  have m_f67p0 : sm Five.f67p0 ∈ S := mem1 Five.wf_f66 Five.wf_f66_sq1 Five.wf_f67p0 m_f66 m_f66_sq1 (by bm_strips2 CFSG.KC.BM.Five.cf67p0 69)
  have m_f67p1 : sm Five.f67p1 ∈ S := mem1 Five.wf_f67p0 Five.wf_f66_sq2 Five.wf_f67p1 m_f67p0 m_f66_sq2 (by bm_strips2 CFSG.KC.BM.Five.cf67p1 69)
  have m_f67 : sm Five.f67 ∈ S := mem1 Five.wf_f67p1 Five.wf_f66_sq3 Five.wf_f67 m_f67p1 m_f66_sq3 (by bm_strips2 CFSG.KC.BM.Five.cf67 69)
  have m_f68 : sm Five.f68 ∈ S := mem1 Five.wf_f67 Five.wf_f9 Five.wf_f68 m_f67 m_f9 (by bm_strips2 CFSG.KC.BM.Five.cf68 69)
  have m_f69 : sm Five.f69 ∈ S := mem1 Seeds.wf_A1 Five.wf_f68 Five.wf_f69 hA1 m_f68 (by bm_strips2 CFSG.KC.BM.Five.cf69 69)
  have m_f69_sq1 : sm Five.f69_sq1 ∈ S := mem1 Five.wf_f69 Five.wf_f69 Five.wf_f69_sq1 m_f69 m_f69 (by bm_strips2 CFSG.KC.BM.Five.cf69_sq1 69)
  have m_f69_sq2 : sm Five.f69_sq2 ∈ S := mem1 Five.wf_f69_sq1 Five.wf_f69_sq1 Five.wf_f69_sq2 m_f69_sq1 m_f69_sq1 (by bm_strips2 CFSG.KC.BM.Five.cf69_sq2 69)
  have m_f69_sq3 : sm Five.f69_sq3 ∈ S := mem1 Five.wf_f69_sq2 Five.wf_f69_sq2 Five.wf_f69_sq3 m_f69_sq2 m_f69_sq2 (by bm_strips2 CFSG.KC.BM.Five.cf69_sq3 69)
  have m_f69_sq4 : sm Five.f69_sq4 ∈ S := mem1 Five.wf_f69_sq3 Five.wf_f69_sq3 Five.wf_f69_sq4 m_f69_sq3 m_f69_sq3 (by bm_strips2 CFSG.KC.BM.Five.cf69_sq4 69)
  have m_f70 : sm Five.f70 ∈ S := mem1 Five.wf_f69 Five.wf_f69_sq4 Five.wf_f70 m_f69 m_f69_sq4 (by bm_strips2 CFSG.KC.BM.Five.cf70 69)
  have m_f71 : sm Five.f71 ∈ S := mem1 Five.wf_f66_sq1 Five.wf_f66_sq2 Five.wf_f71 m_f66_sq1 m_f66_sq2 (by bm_strips2 CFSG.KC.BM.Five.cf71 69)
  have m_f72 : sm Five.f72 ∈ S := mem1 Five.wf_f70 Five.wf_f71 Five.wf_f72 m_f70 m_f71 (by bm_strips2 CFSG.KC.BM.Five.cf72 69)
  have m_f72_sq1 : sm Five.f72_sq1 ∈ S := mem1 Five.wf_f72 Five.wf_f72 Five.wf_f72_sq1 m_f72 m_f72 (by bm_strips2 CFSG.KC.BM.Five.cf72_sq1 69)
  have m_f72_sq2 : sm Five.f72_sq2 ∈ S := mem1 Five.wf_f72_sq1 Five.wf_f72_sq1 Five.wf_f72_sq2 m_f72_sq1 m_f72_sq1 (by bm_strips2 CFSG.KC.BM.Five.cf72_sq2 69)
  have m_f74 : sm Five.f74 ∈ S := memI Five.wf_f72_sq2 Five.wf_f74 m_f72_sq2 (by bm_strips2 CFSG.KC.BM.Five.cf74 69)
  have m_f75 : sm Five.f75 ∈ S := mem1 Five.wf_f71 Five.wf_f74 Five.wf_f75 m_f71 m_f74 (by bm_strips2 CFSG.KC.BM.Five.cf75 69)
  have m_f76 : sm Five.f76 ∈ S := mem1 Five.wf_f71 Five.wf_f72_sq2 Five.wf_f76 m_f71 m_f72_sq2 (by bm_strips2 CFSG.KC.BM.Five.cf76 69)
  have m_f77 : sm Five.f77 ∈ S := mem1 Five.wf_f75 Five.wf_f76 Five.wf_f77 m_f75 m_f76 (by bm_strips2 CFSG.KC.BM.Five.cf77 69)
  have m_f78 : sm Five.f78 ∈ S := mem1 Five.wf_f77 Five.wf_f77 Five.wf_f78 m_f77 m_f77 (by bm_strips2 CFSG.KC.BM.Five.cf78 69)
  have m_f79 : sm Five.f79 ∈ S := mem1 Five.wf_f72_sq2 Five.wf_f78 Five.wf_f79 m_f72_sq2 m_f78 (by bm_strips2 CFSG.KC.BM.Five.cf79 69)
  have m_f80 : sm Five.f80 ∈ S := memI Five.wf_f79 Five.wf_f80 m_f79 (by bm_strips2 CFSG.KC.BM.Five.cf80 69)
  have m_f81 : sm Five.f81 ∈ S := mem1 Five.wf_f71 Five.wf_f80 Five.wf_f81 m_f71 m_f80 (by bm_strips2 CFSG.KC.BM.Five.cf81 69)
  have m_f82 : sm Five.f82 ∈ S := mem1 Five.wf_f71 Five.wf_f79 Five.wf_f82 m_f71 m_f79 (by bm_strips2 CFSG.KC.BM.Five.cf82 69)
  have m_f83 : sm Five.f83 ∈ S := mem1 Five.wf_f81 Five.wf_f82 Five.wf_f83 m_f81 m_f82 (by bm_strips2 CFSG.KC.BM.Five.cf83 69)
  have m_f84 : sm Five.f84 ∈ S := mem1 Five.wf_f83 Five.wf_f83 Five.wf_f84 m_f83 m_f83 (by bm_strips2 CFSG.KC.BM.Five.cf84 69)
  have m_f85 : sm Five.f85 ∈ S := mem1 Five.wf_f79 Five.wf_f84 Five.wf_f85 m_f79 m_f84 (by bm_strips2 CFSG.KC.BM.Five.cf85 69)
  have m_f86 : sm Five.f86 ∈ S := mem1 Five.wf_f55 Five.wf_f62 Five.wf_f86 m_f55 m_f62 (by bm_strips2 CFSG.KC.BM.Five.cf86 69)
  exact ⟨m_f85, m_f86⟩

end CFSG.KC.BM.FiveMem

end
