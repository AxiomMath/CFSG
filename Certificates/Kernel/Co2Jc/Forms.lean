module

public import CFSG.Sporadic.Co2Jc.Native.Forms

public import Certificates.Data.Kernel.RangeSplit
public import Certificates.Data.Kernel.BitT
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxHeartbeats 0

namespace CertificateChecks.KernelCo2Jc

open CFSG.KC.RangeSplit CFSG.Sporadic.Co2Jc.Native CFSG.Sporadic.Co2Jc.Data

theorem forms_check_bilinCheck : CFSG.Sporadic.Co2Jc.Native.bilinCheck = true := by quickRfl

@[expose] noncomputable def foldEqsF (E : Array Nat) (m : Nat) : Nat :=
  ((List.range E.size).filter fun e => CFSG.KC.BitT.bitT m e).foldl (fun acc e => acc ^^^ E[e]!) 0

theorem foldEqs_eq (E : Array Nat) (m : Nat) : foldEqs E m = foldEqsF E m := by
  unfold foldEqs foldEqsF
  simp only [CFSG.KC.BitT.bitT_eq]

theorem forms_check_wedge0 : ((List.range 10).all fun j =>
      if 0 < j then
        (List.range 10).all fun r =>
          foldEqsF wedEqs (wedUnits[10 * (10 * 0 + j) + r]!) == 1 <<< (10 * (10 * 0 + j) + r)
      else true) = true := by
  quickRfl

theorem forms_check_wedge1 : ((List.range 10).all fun j =>
      if 1 < j then
        (List.range 10).all fun r =>
          foldEqsF wedEqs (wedUnits[10 * (10 * 1 + j) + r]!) == 1 <<< (10 * (10 * 1 + j) + r)
      else true) = true := by
  quickRfl

theorem forms_check_wedge2 : ((List.range 10).all fun j =>
      if 2 < j then
        (List.range 10).all fun r =>
          foldEqsF wedEqs (wedUnits[10 * (10 * 2 + j) + r]!) == 1 <<< (10 * (10 * 2 + j) + r)
      else true) = true := by
  quickRfl

theorem forms_check_wedge3 : ((List.range 10).all fun j =>
      if 3 < j then
        (List.range 10).all fun r =>
          foldEqsF wedEqs (wedUnits[10 * (10 * 3 + j) + r]!) == 1 <<< (10 * (10 * 3 + j) + r)
      else true) = true := by
  quickRfl

theorem forms_check_wedge4 : ((List.range 10).all fun j =>
      if 4 < j then
        (List.range 10).all fun r =>
          foldEqsF wedEqs (wedUnits[10 * (10 * 4 + j) + r]!) == 1 <<< (10 * (10 * 4 + j) + r)
      else true) = true := by
  quickRfl

theorem forms_check_wedge5 : ((List.range 10).all fun j =>
      if 5 < j then
        (List.range 10).all fun r =>
          foldEqsF wedEqs (wedUnits[10 * (10 * 5 + j) + r]!) == 1 <<< (10 * (10 * 5 + j) + r)
      else true) = true := by
  quickRfl

theorem forms_check_wedge6 : ((List.range 10).all fun j =>
      if 6 < j then
        (List.range 10).all fun r =>
          foldEqsF wedEqs (wedUnits[10 * (10 * 6 + j) + r]!) == 1 <<< (10 * (10 * 6 + j) + r)
      else true) = true := by
  quickRfl

theorem forms_check_wedge7 : ((List.range 10).all fun j =>
      if 7 < j then
        (List.range 10).all fun r =>
          foldEqsF wedEqs (wedUnits[10 * (10 * 7 + j) + r]!) == 1 <<< (10 * (10 * 7 + j) + r)
      else true) = true := by
  quickRfl

theorem forms_check_wedge8 : ((List.range 10).all fun j =>
      if 8 < j then
        (List.range 10).all fun r =>
          foldEqsF wedEqs (wedUnits[10 * (10 * 8 + j) + r]!) == 1 <<< (10 * (10 * 8 + j) + r)
      else true) = true := by
  quickRfl

theorem forms_check_wedge9 : ((List.range 10).all fun j =>
      if 9 < j then
        (List.range 10).all fun r =>
          foldEqsF wedEqs (wedUnits[10 * (10 * 9 + j) + r]!) == 1 <<< (10 * (10 * 9 + j) + r)
      else true) = true := by
  quickRfl

theorem forms_check_wedgeCheck : CFSG.Sporadic.Co2Jc.Native.wedgeCheck = true := by
  unfold wedgeCheck
  simp only [foldEqs_eq]
  refine andT (by quickRfl) (List.all_eq_true.2 fun i hi => ?_)
  have h := List.mem_range.1 hi
  obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 := by omega
  exacts [forms_check_wedge0, forms_check_wedge1, forms_check_wedge2, forms_check_wedge3, forms_check_wedge4, forms_check_wedge5, forms_check_wedge6, forms_check_wedge7, forms_check_wedge8, forms_check_wedge9]

theorem forms_check : CFSG.Sporadic.Co2Jc.Native.formsOK = true := by
  unfold CFSG.Sporadic.Co2Jc.Native.formsOK
  exact andT forms_check_bilinCheck forms_check_wedgeCheck

end CertificateChecks.KernelCo2Jc
