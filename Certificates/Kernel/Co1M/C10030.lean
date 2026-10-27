module

public import CFSG.Monster.GMS.EdgeSqFact
public import CFSG.Monster.GMS.S365Root
public import CFSG.Sporadic.Co1.Module.TwoB
public import Certificates.Data.CFSGNative.Co1.EdgeSq
public import CFSG.Monster.GMS.EdgeSqCo1Inputs
public import Certificates.Kernel.Co1M.C10041
public import Certificates.Kernel.Co1M.C10044
public import Certificates.Kernel.Co1M.Edge10030
public import CFSG.Certificates.Kernel.Co1M.GmsEdgeSound
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Sporadic.Co1.Module.TwoBCertBase

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1M

open CFSG.KC.GmsPath CFSG.KC.Co1F2 CFSG.KC.Co1M CFSG.KD.Co1M CFSG.Sporadic.SmallF2.Native
  CFSG.Sporadic.Co1.InvNative CFSG.Sporadic.Co1.EdgeSqNative CFSG.Sporadic.Co1.S365UNative

theorem rowsSC_eq : CFSG.Sporadic.Co1.Module.rowsSC = unpackR 24 ESC := by
  have hw : ∀ l ∈ CFSG.Sporadic.Co1.Module.wordC, l < 2 := by decide
  unfold CFSG.Sporadic.Co1.Module.rowsSC genWordRows CFSG.Sporadic.Co1.Module.nGens
  rw [wordRowsU, wordRowsU, idU44, gwU44 _ _ _ hw, powU44]
  exact congrArg (unpackR 24) (Nat.eq_of_beq_eq_true (by quickRfl))

theorem trA30 : transposeRows 24 CFSG.Sporadic.Co1.Module.rowsSA = unpackR 24 ETA := by
  rw [rowsSA_eq, trU41]
  exact congrArg (unpackR 24) (Nat.eq_of_beq_eq_true (by quickRfl))

theorem trC30 : transposeRows 24 CFSG.Sporadic.Co1.Module.rowsSC = unpackR 24 ETC := by
  rw [rowsSC_eq, trU41]
  exact congrArg (unpackR 24) (Nat.eq_of_beq_eq_true (by quickRfl))

theorem f0_30 : transposeRows 24 CFSG.Sporadic.Co1.Module.f0Rows = unpackR 24 EF0 := by
  decide +kernel

theorem kerA30 : kerList (unpackR 24 ETA) = EXA := by decide +kernel

theorem kerC30 : kerList (unpackR 24 ETC) = EXC := by decide +kernel

theorem imA30 : imBasis (unpackR 24 ETA) = EBA := by decide +kernel

theorem imC30 : imBasis (unpackR 24 ETC) = EBC := by decide +kernel

theorem yA30 : EYA = EXA.map (CFSG.KC.M1F2.vmF 24 EF0) := by decide +kernel

theorem yC30 : EYC = EXC.map (CFSG.KC.M1F2.vmF 24 EF0) := by decide +kernel

theorem xA30 : (EXA.all fun x => decide (x < 2 ^ 24) && isFixedN (unpackR 24 ETA) x) = true := by
  decide +kernel

theorem xC30 : (EXC.all fun x => decide (x < 2 ^ 24) && isFixedN (unpackR 24 ETC) x) = true := by
  decide +kernel

theorem crdA30 : crdOK EDA EPA = true := by quickRfl

theorem crdC30 : crdOK EDC EPC = true := by quickRfl

theorem pts30 : ∀ i < 98280, (CFSG.Sporadic.Co1.Module.orbitOf 2 98280).pts[i]! =
    CFSG.KC.VecK.lk CertificateChecks.KernelVec.Co1.Pt 32 i :=
  fun i hi => cm_orb_twin.2.1 i hi

theorem swA30 : ∀ i < 98280,
    edgeV ETA EDA EF0 EMA EYA EBA EPA (CFSG.KC.VecK.lk CertificateChecks.KernelVec.Co1.Pt 32 i) =
      true := by
  intro i hi
  have h := edge30All i hi
  unfold edge30 at h
  rw [strictB_eq, andB_eq, Bool.and_eq_true] at h
  exact h.1

theorem swC30 : ∀ i < 98280,
    edgeV ETC EDC EF0 EMC EYC EBC EPC (CFSG.KC.VecK.lk CertificateChecks.KernelVec.Co1.Pt 32 i) =
      true := by
  intro i hi
  have h := edge30All i hi
  unfold edge30 at h
  rw [strictB_eq, andB_eq, Bool.and_eq_true] at h
  exact h.2

theorem c10030_sA : CFSG.Monster.GMS.EdgeSq.edgeCheck CFSG.Sporadic.Co1.Module.rowsSA = true := by
  unfold CFSG.Monster.GMS.EdgeSq.edgeCheck
  exact edgeCheckN_of trA30 f0_30 kerA30 imA30 yA30 xA30 crdA30 pts30 swA30

theorem c10030_sC : CFSG.Monster.GMS.EdgeSq.edgeCheck CFSG.Sporadic.Co1.Module.rowsSC = true := by
  unfold CFSG.Monster.GMS.EdgeSq.edgeCheck
  exact edgeCheckN_of trC30 f0_30 kerC30 imC30 yC30 xC30 crdC30 pts30 swC30

open Certificates in
open CFSG.Monster.GMS.EdgeSq CFSG.Sporadic.Co1.Module in
theorem c10030 :
    (edgeCheck rowsSA = true)
    ∧ (edgeCheck rowsSC = true) := ⟨c10030_sA, c10030_sC⟩

end CertificateChecks.KernelCo1M

end
