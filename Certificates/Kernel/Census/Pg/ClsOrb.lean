module

public import Certificates.Kernel.Census.Pg.Chain
public import Certificates.Kernel.Census.Pg.ClsData
public import Certificates.Data.Kernel.W16Cls
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RWRepData
public meta import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RWRepData
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

set_option maxRecDepth 400000
set_option maxHeartbeats 0

#kmisc_packarrs CertificateChecks.KernelPgCls.RK CFSG.EvenSporadicStandard.Fin76b.W16.repArrs 8

public section

namespace CertificateChecks.KernelPgCls

open CFSG.EvenSporadicStandard.Fin76b.W16 CFSG.KC.Enum CFSG.KS CFSG.KC.Misc.ArrEnum CFSG.KC.W16Cls
  CertificateChecks.KernelPg

@[expose] noncomputable def A (k : Nat) : Nat := if k = 0 then C.S 3 else C.S 23

@[expose] noncomputable def AI (k : Nat) : Nat := if k = 0 then C.SI 3 else C.SI 23

theorem bR : ∀ j < 9, arrBind repArrs[j]! 128 8 (RK j) = true := by
  intro j hj
  interval_cases j <;> quickRfl

theorem words_ok : allN 36 (fun j => Nat.beq (wordP A (W j)) (C.S j)) = true := by quickRfl

theorem rep_ok : allN 9 (fun j => Nat.beq (wordP A (RW j)) (RK j) &&
    Nat.beq (pc (RK j) (RK j)) pid && !(Nat.beq (RK j) pid)) = true := by quickRfl

theorem orb0 : orbK A AI (NC 0) (RK 0) (Tc 0) (Ec 0) (Pc 0) (Oc 0) = true := by quickRfl
theorem orb1 : orbK A AI (NC 1) (RK 1) (Tc 1) (Ec 1) (Pc 1) (Oc 1) = true := by quickRfl
theorem orb2 : orbK A AI (NC 2) (RK 2) (Tc 2) (Ec 2) (Pc 2) (Oc 2) = true := by quickRfl
theorem orb3 : orbK A AI (NC 3) (RK 3) (Tc 3) (Ec 3) (Pc 3) (Oc 3) = true := by quickRfl
theorem orb4 : orbK A AI (NC 4) (RK 4) (Tc 4) (Ec 4) (Pc 4) (Oc 4) = true := by quickRfl
theorem orb5 : orbK A AI (NC 5) (RK 5) (Tc 5) (Ec 5) (Pc 5) (Oc 5) = true := by quickRfl
theorem orb6 : orbK A AI (NC 6) (RK 6) (Tc 6) (Ec 6) (Pc 6) (Oc 6) = true := by quickRfl
theorem orb7 : orbK A AI (NC 7) (RK 7) (Tc 7) (Ec 7) (Pc 7) (Oc 7) = true := by quickRfl
theorem orb8 : orbK A AI (NC 8) (RK 8) (Tc 8) (Ec 8) (Pc 8) (Oc 8) = true := by quickRfl

theorem orb_ok : ∀ j < 9, orbK A AI (NC j) (RK j) (Tc j) (Ec j) (Pc j) (Oc j) = true := by
  intro j hj
  interval_cases j
  exacts [orb0, orb1, orb2, orb3, orb4, orb5, orb6, orb7, orb8]

theorem disj_ok : allN 9 (fun j => allN 9 fun j' => Nat.beq j j' ||
    allN (NC j) fun i => !(Nat.beq (Tc j i) (RK j'))) = true := by quickRfl

theorem arith_ok : (∀ j < 9, 0 < NC j ∧ NC j * centTab[j]! = 3317760) ∧
    ((List.range 9).map NC).sum = 10575 := by decide +kernel

end CertificateChecks.KernelPgCls
