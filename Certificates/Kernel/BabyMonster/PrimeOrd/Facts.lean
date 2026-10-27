module

public import CFSG.Certificates.Kernel.BabyMonster.PrimeOrd.All
public import CFSG.Certificates.Kernel.BabyMonster.Sound
public import CFSG.Certificates.Kernel.BabyMonster.PairSound
public import CFSG.Certificates.Kernel.BabyMonster.Seeds.All
public import CFSG.Certificates.Kernel.BabyMonster.Chain4
public import CFSG.Monster.B.Pinned.Primes.Program
public import CFSG.Certificates.Kernel.BabyMonster.PrimeOrd.Pow13
public import CFSG.Certificates.Kernel.BabyMonster.PrimeOrd.Pow17
public import CFSG.Certificates.Kernel.BabyMonster.PrimeOrd.Pow19
public import CFSG.Certificates.Kernel.BabyMonster.PrimeOrd.Pow31
public import CFSG.Certificates.Kernel.BabyMonster.PrimeOrd.Pow47
public import CFSG.Certificates.Kernel.BabyMonster.PrimeOrd.Pow7
public import CFSG.Certificates.Kernel.BabyMonster.Seeds.Check0
public import CFSG.Certificates.Kernel.BabyMonster.Seeds.Check1
public import CFSG.Certificates.Kernel.BabyMonster.Seeds.Check2
public import CFSG.Certificates.Kernel.BabyMonster.Seeds.Check3
public import CFSG.Certificates.Kernel.BabyMonster.Seeds.Check4
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF2Fast
public import CFSG.Monster.B.Max2.Pinned
public import CFSG.Monster.B.Pinned.GeneratorDeterminants
public import CFSG.Open.Defs
public import Certificates.Certificate3101
public import Certificates.Certificate3103
public import Certificates.Certificate3106
public import Certificates.Certificate3109Base
public import Certificates.Data.CFSGNative.MonsterB.DyadicFile

public section

namespace CertificateChecks.KernelBM.PrimeOrd

open CFSG.KC.BM CFSG.KC.BM.PrimeOrd CFSG.Monster.B.Pinned CFSG.Monster.B.Primes.Native

local notation "sm" => stripMat
local notation "GA" => stripMat CFSG.KC.BM.Seeds.A1
local notation "GB" => stripMat CFSG.KC.BM.Seeds.A2

local notation "Mt" => Matrix (Fin 4370) (Fin 4370) (ZMod 2)

set_option maxRecDepth 100000

theorem mul1 {A B C : List Nat} (hA : wfMat A = true) (hB : wfMat B = true)
    (h : AllStrips [B] A C) : sm A * sm B = sm C := by
  have e := stripMat_mul_of_allStrips (Ws := [B]) (by simp [hB]) hA h
  simpa using e

theorem one1 {A B : List Nat} (hA : wfMat A = true) (hB : wfMat B = true)
    (h : AllStrips [B] A idStrips) : sm A * sm B = 1 := by
  have e := stripMat_mul_eq_one (Ws := [B]) (by simp [hB]) hA h
  simpa using e

theorem wa : wordG GA GB ['a'] = GA := by simp [wordG]

theorem wb : wordG GA GB ['b'] = GB := by simp [wordG]

theorem step {u v : List Char} {C X : List Nat} (D : List Nat) (wC : wfMat C = true)
    (wX : wfMat X = true) (ih : sm C = wordG GA GB u) (hx : sm X = wordG GA GB v)
    (h : AllStrips [X] C D) : sm D = wordG GA GB (u ++ v) := by
  rw [← mul1 wC wX h, ih, hx, wordG_append]

theorem pw {M : Mt} {i j : ℕ} {A B : List Nat} (C : List Nat) (wA : wfMat A = true)
    (wB : wfMat B = true) (hA : sm A = M ^ i) (hB : sm B = M ^ j) (h : AllStrips [B] A C) :
    sm C = M ^ (i + j) := by
  rw [← mul1 wA wB h, hA, hB, pow_add]

theorem pord {M : Mt} {i : ℕ} {A X : List Nat} (wA : wfMat A = true) (wX : wfMat X = true)
    (hA : sm A = M ^ i) (hX : sm X = M) (h : AllStrips [X] A idStrips) : M ^ (i + 1) = 1 := by
  rw [pow_succ, ← hA, ← hX]
  exact one1 wA wX h

theorem dab : sm Dab = wordG GA GB "ab".toList := by
  rw [step Dab Seeds.wf_A1 Seeds.wf_A2 wa.symm wb.symm
    (by bm_strips4 CFSG.KC.BM.PrimeOrd.cDab 69)]
  exact congrArg (wordG GA GB) (by decide +kernel)

theorem dabb : sm Dabb = wordG GA GB "abb".toList := by
  rw [step Dabb wf_Dab Seeds.wf_A2 dab wb.symm (by bm_strips4 CFSG.KC.BM.PrimeOrd.cDabb 69)]
  exact congrArg (wordG GA GB) (by decide +kernel)

theorem dabbab : sm Dabbab = wordG GA GB "abbab".toList := by
  rw [step Dabbab wf_Dabb wf_Dab dabb dab (by bm_strips4 CFSG.KC.BM.PrimeOrd.cDabbab 69)]
  exact congrArg (wordG GA GB) (by decide +kernel)

theorem dabbabbab : sm Dabbabbab = wordG GA GB "abbabbab".toList := by
  rw [step Dabbabbab wf_Dabb wf_Dabbab dabb dabbab
    (by bm_strips4 CFSG.KC.BM.PrimeOrd.cDabbabbab 69)]
  exact congrArg (wordG GA GB) (by decide +kernel)

theorem dabab : sm Dabab = wordG GA GB "abab".toList := by
  rw [step Dabab wf_Dab wf_Dab dab dab (by bm_strips4 CFSG.KC.BM.PrimeOrd.cDabab 69)]
  exact congrArg (wordG GA GB) (by decide +kernel)

theorem dabababb : sm Dabababb = wordG GA GB "abababb".toList := by
  rw [step Dabababb wf_Dabab wf_Dabb dabab dabb
    (by bm_strips4 CFSG.KC.BM.PrimeOrd.cDabababb 69)]
  exact congrArg (wordG GA GB) (by decide +kernel)

theorem dabbabababb : sm Dabbabababb = wordG GA GB "abbabababb".toList := by
  rw [step Dabbabababb wf_Dabb wf_Dabababb dabb dabababb
    (by bm_strips4 CFSG.KC.BM.PrimeOrd.cDabbabababb 69)]
  exact congrArg (wordG GA GB) (by decide +kernel)

theorem w10 : sm W10 = wordG GA GB word7.toList := by
  rw [step W10 wf_Dab wf_Dabbabbab dab dabbabbab (by bm_strips4 CFSG.KC.BM.PrimeOrd.cW10 69)]
  exact congrArg (wordG GA GB) (by decide +kernel)

theorem w21_0 : sm W21_0 = wordG GA GB (word7.toList ++ "abab".toList) :=
  step W21_0 wf_W10 wf_Dabab w10 dabab (by bm_strips4 CFSG.KC.BM.PrimeOrd.cW21_0 69)

theorem w21 : sm W21 = wordG GA GB word17.toList := by
  rw [step W21 wf_W21_0 wf_Dabababb w21_0 dabababb (by bm_strips4 CFSG.KC.BM.PrimeOrd.cW21 69)]
  exact congrArg (wordG GA GB) (by decide +kernel)

theorem w28 : sm W28 = wordG GA GB word19.toList := by
  rw [step W28 wf_W21 wf_Dabababb w21 dabababb (by bm_strips4 CFSG.KC.BM.PrimeOrd.cW28 69)]
  exact congrArg (wordG GA GB) (by decide +kernel)

theorem w35 : sm W35 = wordG GA GB word31.toList := by
  rw [step W35 wf_W28 wf_Dabababb w28 dabababb (by bm_strips4 CFSG.KC.BM.PrimeOrd.cW35 69)]
  exact congrArg (wordG GA GB) (by decide +kernel)

theorem w65 : sm W65 = wordG GA GB word47.toList := by
  have h0 := step W65_0 wf_W35 wf_W21_0 w35 w21_0 (by bm_strips4 CFSG.KC.BM.PrimeOrd.cW65_0 69)
  have h1 := step W65_1 wf_W65_0 wf_Dabbabbab h0 dabbabbab
    (by bm_strips4 CFSG.KC.BM.PrimeOrd.cW65_1 69)
  rw [step W65 wf_W65_1 wf_Dabbabbab h1 dabbabbab (by bm_strips4 CFSG.KC.BM.PrimeOrd.cW65 69)]
  exact congrArg (wordG GA GB) (by decide +kernel)

theorem w75 : sm W75 = wordG GA GB word13.toList := by
  rw [step W75 wf_W65 wf_Dabbabababb w65 dabbabababb (by bm_strips4 CFSG.KC.BM.PrimeOrd.cW75 69)]
  exact congrArg (wordG GA GB) (by decide +kernel)

theorem pow7 : sm W10 ^ 7 = 1 := by
  have e1 := pw (M := sm W10) (i := 1) (j := 1) W10_sq1 wf_W10 wf_W10 (pow_one _).symm
    (pow_one _).symm (by bm_strips4 CFSG.KC.BM.PrimeOrd.cW10_sq1 69)
  have e2 := pw W10_sq2 wf_W10_sq1 wf_W10_sq1 e1 e1
    (by bm_strips4 CFSG.KC.BM.PrimeOrd.cW10_sq2 69)
  have e3 := pw G7p wf_W10_sq1 wf_W10_sq2 e1 e2 (by bm_strips4 CFSG.KC.BM.PrimeOrd.cG7p 69)
  exact pord wf_G7p wf_W10 e3 rfl (by bm_strips4 CFSG.KC.BM.PrimeOrd.ord_7 69)

theorem pow17 : sm G17 ^ 17 = 1 := by
  have e1 := pw (M := sm G17) (i := 1) (j := 1) G17_sq1 wf_G17 wf_G17 (pow_one _).symm
    (pow_one _).symm (by bm_strips4 CFSG.KC.BM.PrimeOrd.cG17_sq1 69)
  have e2 := pw G17_sq2 wf_G17_sq1 wf_G17_sq1 e1 e1
    (by bm_strips4 CFSG.KC.BM.PrimeOrd.cG17_sq2 69)
  have e3 := pw G17_sq3 wf_G17_sq2 wf_G17_sq2 e2 e2
    (by bm_strips4 CFSG.KC.BM.PrimeOrd.cG17_sq3 69)
  have e4 := pw G17_sq4 wf_G17_sq3 wf_G17_sq3 e3 e3
    (by bm_strips4 CFSG.KC.BM.PrimeOrd.cG17_sq4 69)
  exact pord wf_G17_sq4 wf_G17 e4 rfl (by bm_strips4 CFSG.KC.BM.PrimeOrd.ord_17 69)

theorem g17 : sm G17 = sm W21 ^ 2 := by
  rw [← mul1 wf_W21 wf_W21 (by bm_strips4 CFSG.KC.BM.PrimeOrd.cG17 69), sq]

theorem pow19 : sm W28 ^ 19 = 1 := by
  have e1 := pw (M := sm W28) (i := 1) (j := 1) W28_sq1 wf_W28 wf_W28 (pow_one _).symm
    (pow_one _).symm (by bm_strips4 CFSG.KC.BM.PrimeOrd.cW28_sq1 69)
  have e2 := pw W28_sq2 wf_W28_sq1 wf_W28_sq1 e1 e1
    (by bm_strips4 CFSG.KC.BM.PrimeOrd.cW28_sq2 69)
  have e3 := pw W28_sq3 wf_W28_sq2 wf_W28_sq2 e2 e2
    (by bm_strips4 CFSG.KC.BM.PrimeOrd.cW28_sq3 69)
  have e4 := pw W28_sq4 wf_W28_sq3 wf_W28_sq3 e3 e3
    (by bm_strips4 CFSG.KC.BM.PrimeOrd.cW28_sq4 69)
  have e5 := pw G19p wf_W28_sq1 wf_W28_sq4 e1 e4 (by bm_strips4 CFSG.KC.BM.PrimeOrd.cG19p 69)
  exact pord wf_G19p wf_W28 e5 rfl (by bm_strips4 CFSG.KC.BM.PrimeOrd.ord_19 69)

theorem pow31 : sm W35 ^ 31 = 1 := by
  have e1 := pw (M := sm W35) (i := 1) (j := 1) W35_sq1 wf_W35 wf_W35 (pow_one _).symm
    (pow_one _).symm (by bm_strips4 CFSG.KC.BM.PrimeOrd.cW35_sq1 69)
  have e2 := pw W35_sq2 wf_W35_sq1 wf_W35_sq1 e1 e1
    (by bm_strips4 CFSG.KC.BM.PrimeOrd.cW35_sq2 69)
  have e3 := pw G31pp0 wf_W35_sq1 wf_W35_sq2 e1 e2
    (by bm_strips4 CFSG.KC.BM.PrimeOrd.cG31pp0 69)
  have e4 := pw W35_sq3 wf_W35_sq2 wf_W35_sq2 e2 e2
    (by bm_strips4 CFSG.KC.BM.PrimeOrd.cW35_sq3 69)
  have e5 := pw G31pp1 wf_G31pp0 wf_W35_sq3 e3 e4
    (by bm_strips4 CFSG.KC.BM.PrimeOrd.cG31pp1 69)
  have e6 := pw W35_sq4 wf_W35_sq3 wf_W35_sq3 e4 e4
    (by bm_strips4 CFSG.KC.BM.PrimeOrd.cW35_sq4 69)
  have e7 := pw G31p wf_G31pp1 wf_W35_sq4 e5 e6 (by bm_strips4 CFSG.KC.BM.PrimeOrd.cG31p 69)
  exact pord wf_G31p wf_W35 e7 rfl (by bm_strips4 CFSG.KC.BM.PrimeOrd.ord_31 69)

theorem pow47 : sm W65 ^ 47 = 1 := by
  have e1 := pw (M := sm W65) (i := 1) (j := 1) W65_sq1 wf_W65 wf_W65 (pow_one _).symm
    (pow_one _).symm (by bm_strips4 CFSG.KC.BM.PrimeOrd.cW65_sq1 69)
  have e2 := pw W65_sq2 wf_W65_sq1 wf_W65_sq1 e1 e1
    (by bm_strips4 CFSG.KC.BM.PrimeOrd.cW65_sq2 69)
  have e3 := pw G47pp0 wf_W65_sq1 wf_W65_sq2 e1 e2
    (by bm_strips4 CFSG.KC.BM.PrimeOrd.cG47pp0 69)
  have e4 := pw W65_sq3 wf_W65_sq2 wf_W65_sq2 e2 e2
    (by bm_strips4 CFSG.KC.BM.PrimeOrd.cW65_sq3 69)
  have e5 := pw G47pp1 wf_G47pp0 wf_W65_sq3 e3 e4
    (by bm_strips4 CFSG.KC.BM.PrimeOrd.cG47pp1 69)
  have e6 := pw W65_sq4 wf_W65_sq3 wf_W65_sq3 e4 e4
    (by bm_strips4 CFSG.KC.BM.PrimeOrd.cW65_sq4 69)
  have e7 := pw W65_sq5 wf_W65_sq4 wf_W65_sq4 e6 e6
    (by bm_strips4 CFSG.KC.BM.PrimeOrd.cW65_sq5 69)
  have e8 := pw G47p wf_G47pp1 wf_W65_sq5 e5 e7 (by bm_strips4 CFSG.KC.BM.PrimeOrd.cG47p 69)
  exact pord wf_G47p wf_W65 e8 rfl (by bm_strips4 CFSG.KC.BM.PrimeOrd.ord_47 69)

theorem pow13 : sm G13 ^ 13 = 1 := by
  have e1 := pw (M := sm G13) (i := 1) (j := 1) G13_sq1 wf_G13 wf_G13 (pow_one _).symm
    (pow_one _).symm (by bm_strips4 CFSG.KC.BM.PrimeOrd.cG13_sq1 69)
  have e2 := pw G13_sq2 wf_G13_sq1 wf_G13_sq1 e1 e1
    (by bm_strips4 CFSG.KC.BM.PrimeOrd.cG13_sq2 69)
  have e3 := pw G13_sq3 wf_G13_sq2 wf_G13_sq2 e2 e2
    (by bm_strips4 CFSG.KC.BM.PrimeOrd.cG13_sq3 69)
  have e4 := pw G13p wf_G13_sq2 wf_G13_sq3 e2 e3 (by bm_strips4 CFSG.KC.BM.PrimeOrd.cG13p 69)
  exact pord wf_G13p wf_G13 e4 rfl (by bm_strips4 CFSG.KC.BM.PrimeOrd.ord_13 69)

theorem g13 : sm G13 = sm W75 ^ 2 := by
  rw [← mul1 wf_W75 wf_W75 (by bm_strips4 CFSG.KC.BM.PrimeOrd.cG13 69), sq]

theorem six_facts :
    (wordG GA GB word7.toList ^ 1) ^ 7 = 1 ∧ wordG GA GB word7.toList ^ 1 ≠ 1 ∧
    (wordG GA GB word13.toList ^ 2) ^ 13 = 1 ∧ wordG GA GB word13.toList ^ 2 ≠ 1 ∧
    (wordG GA GB word17.toList ^ 2) ^ 17 = 1 ∧ wordG GA GB word17.toList ^ 2 ≠ 1 ∧
    (wordG GA GB word19.toList ^ 1) ^ 19 = 1 ∧ wordG GA GB word19.toList ^ 1 ≠ 1 ∧
    (wordG GA GB word31.toList ^ 1) ^ 31 = 1 ∧ wordG GA GB word31.toList ^ 1 ≠ 1 ∧
    (wordG GA GB word47.toList ^ 1) ^ 47 = 1 ∧ wordG GA GB word47.toList ^ 1 ≠ 1 := by
  simp only [pow_one]
  rw [← w10, ← w75, ← w21, ← w28, ← w35, ← w65, ← g13, ← g17]
  exact ⟨pow7, notId_sound wf_W10 ne_7, pow13, notId_sound wf_G13 ne_13, pow17,
    notId_sound wf_G17 ne_17, pow19, notId_sound wf_W28 ne_19, pow31, notId_sound wf_W35 ne_31,
    pow47, notId_sound wf_W65 ne_47⟩

end CertificateChecks.KernelBM.PrimeOrd

end
