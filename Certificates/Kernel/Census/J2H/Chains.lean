module

public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.Census.J2H.Data
public import CFSG.Certificates.Kernel.Misc.ArrBind
public import CFSG.Certificates.Kernel.Spor.RawSound
meta import Certificates.Kernel.Census.J2H.Data
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

#ks_rawchain CertificateChecks.KernelJ2H.S0C 315 9 16 CertificateChecks.KernelJ2H.s0Strong
  CertificateChecks.KernelJ2H.s0Base 4 CertificateChecks.KernelJ2H.noD

#ks_rawchain CertificateChecks.KernelJ2H.A5C 315 9 16 CertificateChecks.KernelJ2H.a5Strong
  CertificateChecks.KernelJ2H.a5Base 2 CertificateChecks.KernelJ2H.noD

#ks_rawchain CertificateChecks.KernelJ2H.VC 315 9 16 CertificateChecks.KernelJ2H.vStrong
  CertificateChecks.KernelJ2H.vBase 4 CertificateChecks.KernelJ2H.noD

namespace CertificateChecks.KernelJ2H

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum CFSG.Certificates.Native
open CFSG.Monster.B.Co2.Native
open CFSG.Sporadic.Schreier.Co3.Native (wordsArr)

theorem s0_perm :
    allN 4 (fun j => permOK 315 9 (mask 9) (315 * 9) (S0C.S j) (S0C.SI j)) = true := by
  quickRfl

theorem s0_binds : Binds 315 9 S0C.S 4 1 S0C.BP s0Strong s0Base := by
  have hs : Nat.beq s0Strong.size 4 = true := by quickRfl
  have hb : Nat.beq s0Base.size 1 = true := by quickRfl
  refine ⟨by norm_num, by norm_num, by norm_num, Nat.eq_of_beq_eq_true hs, fun j hj => ?_,
    Nat.eq_of_beq_eq_true hb, by decide +kernel⟩
  interval_cases j <;> exact arrBind_sound (by quickRfl)

theorem s0_chain : rawChainOK 315 (s0Strong.extract 0 4) s0Strong s0Base (wordsArr 4 4 noD) 4 =
      true ∧ rawOrbitSizes 315 s0Strong s0Base = [128] := by
  refine ⟨rawChainK_sound (NS := 20) (CH := 16) s0_binds S0C.head S0C.hl (by norm_num) S0C.hs, ?_⟩
  rw [rawOrbitSizesK_sound s0_binds s0_perm S0C.hl]
  decide

theorem a5_perm :
    allN 2 (fun j => permOK 315 9 (mask 9) (315 * 9) (A5C.S j) (A5C.SI j)) = true := by
  quickRfl

theorem a5_binds : Binds 315 9 A5C.S 2 1 A5C.BP a5Strong a5Base := by
  have hs : Nat.beq a5Strong.size 2 = true := by quickRfl
  have hb : Nat.beq a5Base.size 1 = true := by quickRfl
  refine ⟨by norm_num, by norm_num, by norm_num, Nat.eq_of_beq_eq_true hs, fun j hj => ?_,
    Nat.eq_of_beq_eq_true hb, by decide +kernel⟩
  interval_cases j <;> exact arrBind_sound (by quickRfl)

theorem a5_chain : rawChainOK 315 (a5Strong.extract 0 2) a5Strong a5Base (wordsArr 2 2 noD) 4 =
      true ∧ rawOrbitSizes 315 a5Strong a5Base = [60] := by
  refine ⟨rawChainK_sound (NS := 20) (CH := 16) a5_binds A5C.head A5C.hl (by norm_num) A5C.hs, ?_⟩
  rw [rawOrbitSizesK_sound a5_binds a5_perm A5C.hl]
  decide

theorem v_perm :
    allN 4 (fun j => permOK 315 9 (mask 9) (315 * 9) (VC.S j) (VC.SI j)) = true := by
  quickRfl

theorem v_binds : Binds 315 9 VC.S 4 1 VC.BP vStrong vBase := by
  have hs : Nat.beq vStrong.size 4 = true := by quickRfl
  have hb : Nat.beq vBase.size 1 = true := by quickRfl
  refine ⟨by norm_num, by norm_num, by norm_num, Nat.eq_of_beq_eq_true hs, fun j hj => ?_,
    Nat.eq_of_beq_eq_true hb, by decide +kernel⟩
  interval_cases j <;> exact arrBind_sound (by quickRfl)

end CertificateChecks.KernelJ2H
