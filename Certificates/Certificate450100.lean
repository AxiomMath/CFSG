module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.U42SmallIndexInputs
import CFSG.Certificates.Kernel.EvenSporU42.Sound
import Certificates.Kernel.EvenSporU42.Checks
import Certificates.Kernel.Sporadic.PSp45.Facts

public section

namespace CertificateChecks.Batch450100

open CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.U42SmallIndex
open CFSG.KC.EvenSporU42 CertificateChecks.KernelEvenSporU42 CertificateChecks.KernelSpor
open CFSG.KS.SporSch.MOC CFSG.GH74.KGroups CFSG.GH74.KGroups.NativeChecks CFSG.Sporadic.Schreier
open CFSG.ComponentClassification.CatFactsSmall.PSp43

set_option maxHeartbeats 0 in
private theorem zR : R zK z0 := by
  unfold R CFSG.KS.Raw.Orb.PRep
  decide +kernel

set_option maxHeartbeats 0 in
private theorem paR : R paK pa := by
  unfold R CFSG.KS.Raw.Orb.PRep
  decide +kernel

set_option maxHeartbeats 0 in
private theorem pbR : R pbK pb := by
  unfold R CFSG.KS.Raw.Orb.PRep
  decide +kernel

private theorem elemR (j : Nat) :
    R (elemH P45Q.LR P45Q.TR j) (elemP 45 6 P45Q.LR P45Q.TR 4 j) :=
  prep_elemK PSp45.chainP j

private theorem elems_eq :
    elemsTab QP45 = (List.range 25920).map (elemP 45 6 P45Q.LR P45Q.TR 4) := by
  rw [elemsTab_eq, elemsT_eq, PSp45.qp_eq, enumeration_eq PSp45.chainP, KernelEvenSporU42.ordK_eq]

private theorem bl_tr : L2 blK bl := by
  unfold bl blK jK
  rw [elems_eq, List.filter_map]
  have e : ((List.range 25920).filter fun j => commH (elemH P45Q.LR P45Q.TR j) zK) =
      (List.range 25920).filter ((fun g => decide (g * z0 = z0 * g)) ∘
        elemP 45 6 P45Q.LR P45Q.TR 4) := by
    refine List.filter_congr fun j _ => ?_
    rw [commH_eq (elemR j) zR]
    rfl
  rw [e]
  generalize (List.range 25920).filter ((fun g => decide (g * z0 = z0 * g)) ∘
    elemP 45 6 P45Q.LR P45Q.TR 4) = l
  induction l with
  | nil => exact List.Forall₂.nil
  | cons j l ih => exact List.Forall₂.cons (elemR j) ih

theorem all_checks :
    (bl.length = 648) ∧ (pl.length = 27) ∧ (plMulCheck = true) ∧ (plExpCheck = true) ∧
      (blNormCheck = true) ∧ (zDataCheck z0 = true) :=
  checks_of bl_tr paR pbR zR allK_true

end CertificateChecks.Batch450100

namespace Certificates

open CertificateChecks

open CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.U42SmallIndex in
theorem certificate450100 : (bl.length = 648)
    ∧ (pl.length = 27)
    ∧ (plMulCheck = true)
    ∧ (plExpCheck = true)
    ∧ (blNormCheck = true)
    ∧ (zDataCheck z0 = true) :=
  CertificateChecks.Batch450100.all_checks

end Certificates
