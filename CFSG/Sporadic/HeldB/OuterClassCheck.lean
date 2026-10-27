
module

public import CFSG.Sporadic.HeldB.OuterClassCheckBase

public import CFSG.Sporadic.HeldB.HeBlocks
public import CFSG.Sporadic.HeldB.OuterArithCheck
public import Certificates.Data.CFSGNative.HeldB.Tests
public meta import CFSG.Sporadic.HeldB.HeBlocks
public meta import CFSG.Sporadic.HeldB.OuterArithCheck
public meta import Certificates.Data.CFSGNative.HeldB.Tests
public meta import Certificates.Data.CFSGNative.PairSchreier.Core
public import Certificates.Certificate2118

public section

namespace CFSG.Sporadic.HeldB

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Sporadic.Schreier.PairNative
  CFSG.Sporadic.HeldB.Native

theorem heUArr_fix0 : heUArr[0]! = 0 :=
  Certificates.certificate2118.1

theorem heGen0_fix0 : (heGen 0)[0]! = 0 :=
  Certificates.certificate2118.2.1

theorem heUArr_fixCount : (List.range 8330).countP (fun i => heUArr[i]! == i) = 98 :=
  Certificates.certificate2118.2.2.1

theorem heGen0_fixCount : (List.range 8330).countP (fun i => (heGen 0)[i]! == i) = 346 :=
  Certificates.certificate2118.2.2.2.1

theorem heGen0_pow2 : eqA 8330 (hePowA (heGen 0) 2) (idA 8330) = true :=
  Certificates.certificate2118.2.2.2.2.1

theorem heGen1_pow7 : eqA 8330 (hePowA (heGen 1) 7) (idA 8330) = true :=
  Certificates.certificate2118.2.2.2.2.2.1

theorem heOuterBlocks_check :
    ((heBlock1.all fun t => t[0]! == 0) && (heBlock2.all fun t => t[0]! == 0) &&
      countWPar 25 (commB heUArr heBase) (heBlock0.filter fun t0 => heUArr[t0[0]!]! == t0[0]!)
        [heBlock1, heBlock2] == 15120 &&
      countWPar 1 (twistInvB heUArr heBase) (heBlock0.filter fun t0 => t0[0]! == 0)
        [heBlock1, heBlock2] == 3136) = true :=
  Certificates.certificate2118.2.2.2.2.2.2

theorem heBlocks_fix0 :
    ((heBlock1.all fun t => t[0]! == 0) && heBlock2.all fun t => t[0]! == 0) = true := by
  have h := heOuterBlocks_check
  simp only [Bool.and_eq_true] at h ⊢
  exact h.1.1

theorem heOuterCent_count :
    countWPar 25 (commB heUArr heBase) (heBlock0.filter fun t0 => heUArr[t0[0]!]! == t0[0]!)
      [heBlock1, heBlock2] = 15120 := by
  have h := heOuterBlocks_check
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact h.1.2

theorem heOuterInv0_count :
    countWPar 1 (twistInvB heUArr heBase) (heBlock0.filter fun t0 => t0[0]! == 0)
      [heBlock1, heBlock2] = 3136 := by
  have h := heOuterBlocks_check
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact h.2

end CFSG.Sporadic.HeldB
