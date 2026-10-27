
module

public import CFSG.Monster.GMS.S365CosetSpecBase
public import CFSG.Monster.GMS.S365CentBasic
public import CFSG.Monster.GMS.S365CentPathSpecBase
public import CFSG.Monster.GMS.S365CenterOrbInputs
public import Certificates.Kernel.Co1M.C10044
public import Certificates.Kernel.Co1M.Data10041
public import CFSG.Certificates.Kernel.Co1M.CosetBfsSound
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1M

open CFSG.KC.Co1F2 CFSG.KC.BfsT CFSG.KC.Co1M CFSG.KD.Co1M CFSG.Sporadic.SmallF2.Native
  CFSG.Sporadic.Co1.Module CFSG.Sporadic.Co1.Module.Pairs CFSG.Sporadic.Co1.S365Native
  CFSG.Monster.GMS.S365

theorem trU41 (X : Nat) : transposeRows 24 (unpackR 24 X) = unpackR 24 (trK 24 X) :=
  tr_sound (Nat.beq_refl _)

theorem cosetRowsT_eq : cosetRowsT = ([CT0, CT1, CT2].map (unpackR 24)).toArray := by
  unfold cosetRowsT cosetWords
  simp only [List.map_cons, List.map_nil, wordRowsU, trU41]
  refine congrArg List.toArray (congrArg₂ List.cons ?_ (congrArg₂ List.cons ?_
    (congrArg₂ List.cons ?_ rfl))) <;>
  exact congrArg (unpackR 24) (Nat.eq_of_beq_eq_true (by quickRfl))

theorem cbfs10041 : cosetBFS ([CT0, CT1, CT2].map (unpackR 24)).toArray 0 0 28 400 =
      (OL.toArray, OP.toArray, OB.toArray) ∧ OL.Nodup ∧
    treeCheckK ([CT0, CT1, CT2].map (unpackR 24)).toArray 0 0 OL.toArray OP.toArray OB.toArray =
      true ∧
    (OL.toArray.all fun v => decide (v < 2 ^ 24)) = true :=
  cosetBFS_sound (by quickRfl)

theorem c10041_orbit : orbitCheck3 = true := by
  unfold orbitCheck3 orbitCheck3Of
  rw [cosetRowsT_eq, cbfs10041.1]
  change (treeCheckK ([CT0, CT1, CT2].map (unpackR 24)).toArray 0 0 OL.toArray OP.toArray
      OB.toArray && OL.toArray[0]! == 28 && decide (397 ≤ OL.toArray.size) &&
      (OL.toArray.all fun v => decide (v < 2 ^ 24)) && decide OL.toArray.toList.Nodup) = true
  have hnd : OL.toArray.toList.Nodup := by
    rw [List.toList_toArray]
    exact cbfs10041.2.1
  rw [cbfs10041.2.2.1, cbfs10041.2.2.2, decide_eq_true hnd]
  quickRfl

theorem c10041_neg :
    (!cbfsK [CT0, CT1, CT2] 0 0 28 400 OL OP (OB.set 7 2) &&
      !cbfsK [CT0, CT1, CT2] 0 0 28 399 OL OP OB &&
      !cbfsK [CT0, CT1, CT2] 0 0 27 400 OL OP OB) = true := by
  quickRfl

open Certificates in
open CFSG.Monster.GMS.S365 in
theorem c10041 :
    orbitCheck3 = true := c10041_orbit

end CertificateChecks.KernelCo1M

end
