module

public import Certificates.Kernel.BabyMonster.Chain2
public import Certificates.Kernel.BabyMonster.ForallLt
public import CFSG.Certificates.Kernel.BabyMonster.NativePair24.All
public import Certificates.Data.CFSGNative.MonsterB.IntertwinerData
public import Certificates.Data.Kernel.BabyMonster.Pair24
public import CFSG.Certificates.Kernel.BabyMonster.NativePair24.Check0
public import CFSG.Certificates.Kernel.BabyMonster.NativePair24.Check1
public import CFSG.Certificates.Kernel.BabyMonster.NativePair24.Check10
public import CFSG.Certificates.Kernel.BabyMonster.NativePair24.Check11
public import CFSG.Certificates.Kernel.BabyMonster.NativePair24.Check12
public import CFSG.Certificates.Kernel.BabyMonster.NativePair24.Check13
public import CFSG.Certificates.Kernel.BabyMonster.NativePair24.Check14
public import CFSG.Certificates.Kernel.BabyMonster.NativePair24.Check15
public import CFSG.Certificates.Kernel.BabyMonster.NativePair24.Check16
public import CFSG.Certificates.Kernel.BabyMonster.NativePair24.Check17
public import CFSG.Certificates.Kernel.BabyMonster.NativePair24.Check18
public import CFSG.Certificates.Kernel.BabyMonster.NativePair24.Check19
public import CFSG.Certificates.Kernel.BabyMonster.NativePair24.Check2
public import CFSG.Certificates.Kernel.BabyMonster.NativePair24.Check20
public import CFSG.Certificates.Kernel.BabyMonster.NativePair24.Check21
public import CFSG.Certificates.Kernel.BabyMonster.NativePair24.Check22
public import CFSG.Certificates.Kernel.BabyMonster.NativePair24.Check23
public import CFSG.Certificates.Kernel.BabyMonster.NativePair24.Check24
public import CFSG.Certificates.Kernel.BabyMonster.NativePair24.Check3
public import CFSG.Certificates.Kernel.BabyMonster.NativePair24.Check4
public import CFSG.Certificates.Kernel.BabyMonster.NativePair24.Check5
public import CFSG.Certificates.Kernel.BabyMonster.NativePair24.Check6
public import CFSG.Certificates.Kernel.BabyMonster.NativePair24.Check7
public import CFSG.Certificates.Kernel.BabyMonster.NativePair24.Check8
public import CFSG.Certificates.Kernel.BabyMonster.NativePair24.Check9

public section

namespace CertificateChecks.KernelBM.Pair

open CFSG.KC.BM

@[expose] noncomputable def Qs : List (List Nat) :=
  [NativePair.Q0, NativePair.Q1, NativePair.Q2, NativePair.Q3, NativePair.Q4, NativePair.Q5,
    NativePair.Q6, NativePair.Q7, NativePair.Q8, NativePair.Q9, NativePair.Q10, NativePair.Q11,
    NativePair.Q12, NativePair.Q13, NativePair.Q14, NativePair.Q15, NativePair.Q16,
    NativePair.Q17, NativePair.Q18, NativePair.Q19, NativePair.Q20, NativePair.Q21,
    NativePair.Q22, NativePair.Q23, NativePair.Q24, NativePair.Q25]

@[expose] noncomputable def wordL : List (List Nat) :=
  CFSG.Monster.B.Bin.conjWord24.map fun j => Qs.getD (j - 1) []

@[expose] noncomputable def probeL : List (List Nat) :=
  CFSG.Monster.B.Bin.probeWord.map fun l => if l then NativePair24.F else NativePair.Q25

theorem wf_Qs : ∀ g < 26, wfMat (Qs.getD g []) = true := by
  forall_lt_consts CFSG.KC.BM.NativePair24.wf_Q 26

theorem wordL_eq : wordL = NativePair.Q17 :: wordL.tail := rfl

theorem probeL_eq : probeL = NativePair24.F :: probeL.tail := rfl

theorem wchain : WChain wordL.tail NativePair.Q17 NativePair24.W := by
  bm_wchain CFSG.KC.BM.NativePair24.cW 7 CFSG.KC.BM.NativePair24.wf_

theorem prchain : WChain probeL.tail NativePair24.F NativePair24.PR := by
  bm_wchain CFSG.KC.BM.NativePair24.cPR 7 CFSG.KC.BM.NativePair24.wf_

end CertificateChecks.KernelBM.Pair

end
