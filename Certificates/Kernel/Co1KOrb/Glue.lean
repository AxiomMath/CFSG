module

public import CFSG.Certificates.Kernel.F2Set24Sound
public import CFSG.Sporadic.Schreier.Co1ThreeLocal
public import Certificates.Kernel.Co1KOrb.Data
public import Certificates.Kernel.SporSch.Co1.ThreeLocal
import all Init.Data.Nat.Fold
import all Init.Data.Range.Basic
import all Init.Data.Array.Basic

public section

namespace CertificateChecks.KernelCo1KOrb

open CFSG.Sporadic.Co1Schreier CFSG.KS.F2Set24 CFSG.KC.F2Set24 CFSG.KD.Co1KOrb
open CFSG.Sporadic.SmallF2 (toVecD)
open CFSG.Sporadic.SmallF2.Native (transposeRows)
open CertificateChecks.KernelSporSch.Co1ThreeLocal

theorem cY_eq : cY.toArray = transposeRows 24 YI := by decide +kernel

theorem cT_eq : cT.toArray = transposeRows 24 TI := by decide +kernel

theorem inv_y : Native.inv Native.yR = YI := by
  rw [yR_eq]
  exact CFSG.KS.SporSch.inv_eq_of_mul ky

theorem inv_t : Native.inv Native.tR = TI := by
  rw [tR_eq]
  exact CFSG.KS.SporSch.inv_eq_of_mul kt

theorem actsBy_yInv :
    ActsBy ThreeLocal.y⁻¹ cY.toArray := by
  have h := threeLocal_check
  simp only [Native.threeLocalCheck, Bool.and_eq_true, beq_iff_eq] at h
  have ha := MRep.actsBy (rep_y.inv h.2)
  rwa [inv_y, ← cY_eq] at ha

theorem actsBy_tInv :
    ActsBy ThreeLocal.t⁻¹ cT.toArray := by
  have h := threeLocal_check
  simp only [Native.threeLocalCheck, Bool.and_eq_true, beq_iff_eq] at h
  have ha := MRep.actsBy (rep_t.inv h.1.2)
  rwa [inv_t, ← cT_eq] at ha

theorem closure_inv_eq : Subgroup.closure {ThreeLocal.y⁻¹, ThreeLocal.t⁻¹} = ThreeLocal.K := by
  rw [ThreeLocal.K, ← Subgroup.closure_inv (s := {ThreeLocal.y, ThreeLocal.t}), Set.inv_insert,
    Set.inv_singleton]

end CertificateChecks.KernelCo1KOrb

end
