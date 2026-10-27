
module

public import CFSG.Sporadic.HeldB.InnerClassCheckBase

public import CFSG.Sporadic.HeldB.HeBlocks
public import CFSG.Sporadic.HeldB.InnerCheck
public import Certificates.Data.CFSGNative.HeldB.Tests
public meta import CFSG.Sporadic.HeldB.HeBlocks
public meta import CFSG.Sporadic.HeldB.InnerCheck
public meta import Certificates.Data.CFSGNative.HeldB.Tests
public meta import Certificates.Data.CFSGNative.PairSchreier.Core
public import CFSG.Sporadic.HeldB.InnerClassCheckInputs
public import Certificates.Certificate2115

public section

namespace CFSG.Sporadic.HeldB

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Sporadic.Schreier.PairNative
  CFSG.Sporadic.HeldB.Native

theorem heT1Arr_fixCount : (List.range 8330).countP (fun i => heT1Arr[i]! == i) = 42 :=
  Certificates.certificate2115.1

theorem heT1cArr_fix0 : heT1cArr[0]! = 0 :=
  Certificates.certificate2115.2.1

theorem heInnerBlocks_check :
    (countWPar 87 (commB (heGen 0) heBase)
        (heBlock0.filter fun t0 => (heGen 0)[t0[0]!]! == t0[0]!) [heBlock1, heBlock2] == 161280 &&
      countWPar 11 (commB heT1cArr heBase)
        (heBlock0.filter fun t0 => heT1cArr[t0[0]!]! == t0[0]!) [heBlock1, heBlock2] == 21504 &&
      countWPar 1 (twistInvB (idA 8330) heBase) (heBlock0.filter fun t0 => t0[0]! == 0)
        [heBlock1, heBlock2] == 1984) = true :=
  Certificates.certificate2115.2.2

theorem heCent0_count :
    countWPar 87 (commB (heGen 0) heBase)
      (heBlock0.filter fun t0 => (heGen 0)[t0[0]!]! == t0[0]!) [heBlock1, heBlock2] = 161280 := by
  have h := heInnerBlocks_check
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact h.1.1

theorem heCent1_count :
    countWPar 11 (commB heT1cArr heBase) (heBlock0.filter fun t0 => heT1cArr[t0[0]!]! == t0[0]!)
      [heBlock1, heBlock2] = 21504 := by
  have h := heInnerBlocks_check
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact h.1.2

theorem heSq0_count :
    countWPar 1 (twistInvB (idA 8330) heBase) (heBlock0.filter fun t0 => t0[0]! == 0)
      [heBlock1, heBlock2] = 1984 := by
  have h := heInnerBlocks_check
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact h.2

end CFSG.Sporadic.HeldB
