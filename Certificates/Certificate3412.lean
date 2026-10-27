module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage2BridgeData
import CFSG.Certificates.Kernel.O8BridgeSound
import CFSG.Certificates.Kernel.O8EnumSound
import Certificates.Kernel.OmegaEight.EnumCP
import Certificates.Kernel.OmegaEight.EnumCM
import Certificates.Kernel.OmegaEight.EnumT
import Certificates.Kernel.OmegaEight.EnumSP
import Certificates.Kernel.OmegaEight.EnumSM
meta import Certificates.Kernel.OmegaEight.EnumGen
meta import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage2BridgeData
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage2Cand
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage2MinusData
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage2Offend
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage2PlusData
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaParLin

open CFSG.KC.O8 CFSG.EvenSmallLie.OmegaEight.Stage2 CFSG.EvenSmallLie.OmegaEight.Stage1
  CertificateChecks.KernelO8

namespace CertificateChecks.Batch3412

open CFSG.KC.O8 CFSG.EvenSmallLie.OmegaEight.Stage2 CFSG.EvenSmallLie.OmegaEight.Stage1
  CertificateChecks.KernelO8

meta def qCP : Array ℕ := (List.range 6).toArray.map fun i => kronK (genRows .plus i)
meta def qCM : Array ℕ := (List.range 6).toArray.map fun i => kronK (genRows .minus i)
meta def qTP : Array ℕ := (List.range 6).toArray.map fun k => kronK (urRows .plus k)
meta def qTM : Array ℕ := (List.range 6).toArray.map fun k => kronK (urRows .minus k)
meta def qSP : Array ℕ := cGensPlus.map (·.1)
meta def qSM : Array ℕ := cGensMinus.map (·.1)

#ks_enum_query CertificateChecks.KernelO8.EnCP CertificateChecks.Batch3412.QCP
  CertificateChecks.Batch3412.qCP
#ks_enum_query CertificateChecks.KernelO8.EnCM CertificateChecks.Batch3412.QCM
  CertificateChecks.Batch3412.qCM
#ks_enum_query CertificateChecks.KernelO8.EnTP CertificateChecks.Batch3412.QTP
  CertificateChecks.Batch3412.qTP
#ks_enum_query CertificateChecks.KernelO8.EnTM CertificateChecks.Batch3412.QTM
  CertificateChecks.Batch3412.qTM
#ks_enum_query CertificateChecks.KernelO8.EnSP CertificateChecks.Batch3412.QSP
  CertificateChecks.Batch3412.qSP
#ks_enum_query CertificateChecks.KernelO8.EnSM CertificateChecks.Batch3412.QSM
  CertificateChecks.Batch3412.qSM

theorem cP_ok : enumOK cGensPlus (decE EnCP.D EnCP.m) = true := by
  have h := enum_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) EnCP.head
    EnCP.blocks
  rwa [genPairsK_eq (gs := cGensPlus) (by decide +kernel) (by decide +kernel)] at h

theorem cM_ok : enumOK cGensMinus (decE EnCM.D EnCM.m) = true := by
  have h := enum_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) EnCM.head
    EnCM.blocks
  rwa [genPairsK_eq (gs := cGensMinus) (by decide +kernel) (by decide +kernel)] at h

theorem tP_ok : enumOK tGensPlus (decE EnTP.D EnTP.m) = true := by
  have h := enum_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) EnTP.head
    EnTP.blocks
  rwa [genPairsK_eq (gs := tGensPlus) (by decide +kernel) (by decide +kernel)] at h

theorem tM_ok : enumOK tGensMinus (decE EnTM.D EnTM.m) = true := by
  have h := enum_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) EnTM.head
    EnTM.blocks
  rwa [genPairsK_eq (gs := tGensMinus) (by decide +kernel) (by decide +kernel)] at h

theorem sP_ok : enumOK (stage1Gens .plus) (decE EnSP.D EnSP.m) = true := by
  have h := enum_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) EnSP.head
    EnSP.blocks
  refine (genPairsK_eq (gs := stage1Gens .plus) (size_stage1Gens _) fun j hj => ?_) ▸ h
  rw [stage1Gens_getD _ hj, kronK_eq, kronK_eq]
  revert j
  decide +kernel

theorem sM_ok : enumOK (stage1Gens .minus) (decE EnSM.D EnSM.m) = true := by
  have h := enum_sound (by decide +kernel) (by decide +kernel) (by decide +kernel) EnSM.head
    EnSM.blocks
  refine (genPairsK_eq (gs := stage1Gens .minus) (size_stage1Gens _) fun j hj => ?_) ▸ h
  rw [stage1Gens_getD _ hj, kronK_eq, kronK_eq]
  revert j
  decide +kernel

theorem bridge_plus : bridgeCheck .plus cGensPlus tGensPlus (decE EnCP.D EnCP.m)
    (decE EnTP.D EnTP.m) (decE EnSP.D EnSP.m) = true := by
  have hc : ∀ i < 6, kronK (genRows .plus i) = enKey EnCP.D (QCP i) ∧ QCP i < EnCP.m := by
    simp only [kronK_eq]
    decide +kernel
  have ht : ∀ k < 6, (tGensPlus.getD (k + 1) (0, 0)).1 = kronK (urRows .plus k) ∧
      kronK (urRows .plus k) = enKey EnTP.D (QTP k) ∧ QTP k < EnTP.m := by
    simp only [kronK_eq]
    decide +kernel
  have hs : ∀ j < cGensPlus.size, (cGensPlus.getD j (0, 0)).1 = enKey EnSP.D (QSP j) ∧
      QSP j < EnSP.m := by
    decide +kernel
  refine bridgeCheck_of (fun i hi => ?_) sP_ok (gensIn_of fun j hj => ?_) (by decide +kernel)
    (by decide +kernel) fun k hk => ⟨(ht k hk).1, ?_⟩
  · rw [(hc i hi).1]
    exact memK_decE cP_ok (by decide +kernel) (hc i hi).2
  · rw [(hs j hj).1]
    exact memK_decE sP_ok (by decide +kernel) (hs j hj).2
  · rw [(ht k hk).2.1]
    exact memK_decE tP_ok (by decide +kernel) (ht k hk).2.2

theorem bridge_minus : bridgeCheck .minus cGensMinus tGensMinus (decE EnCM.D EnCM.m)
    (decE EnTM.D EnTM.m) (decE EnSM.D EnSM.m) = true := by
  have hc : ∀ i < 6, kronK (genRows .minus i) = enKey EnCM.D (QCM i) ∧ QCM i < EnCM.m := by
    simp only [kronK_eq]
    decide +kernel
  have ht : ∀ k < 6, (tGensMinus.getD (k + 1) (0, 0)).1 = kronK (urRows .minus k) ∧
      kronK (urRows .minus k) = enKey EnTM.D (QTM k) ∧ QTM k < EnTM.m := by
    simp only [kronK_eq]
    decide +kernel
  have hs : ∀ j < cGensMinus.size, (cGensMinus.getD j (0, 0)).1 = enKey EnSM.D (QSM j) ∧
      QSM j < EnSM.m := by
    decide +kernel
  refine bridgeCheck_of (fun i hi => ?_) sM_ok (gensIn_of fun j hj => ?_) (by decide +kernel)
    (by decide +kernel) fun k hk => ⟨(ht k hk).1, ?_⟩
  · rw [(hc i hi).1]
    exact memK_decE cM_ok (by decide +kernel) (hc i hi).2
  · rw [(hs j hj).1]
    exact memK_decE sM_ok (by decide +kernel) (hs j hj).2
  · rw [(ht k hk).2.1]
    exact memK_decE tM_ok (by decide +kernel) (ht k hk).2.2

end CertificateChecks.Batch3412

public section

namespace Certificates

open CertificateChecks.Batch3412 in
open CFSG.EvenSmallLie.OmegaEight.Stage2 in
theorem certificate3412 : (∃ cE tcE sE : Enum, enumOK cGensPlus cE = true ∧ enumOK tGensPlus tcE = true ∧
      bridgeCheck .plus cGensPlus tGensPlus cE tcE sE = true)
    ∧ (∃ cE tcE sE : Enum, enumOK cGensMinus cE = true ∧ enumOK tGensMinus tcE = true ∧
      bridgeCheck .minus cGensMinus tGensMinus cE tcE sE = true) :=
  ⟨⟨_, _, _, cP_ok, tP_ok, bridge_plus⟩, ⟨_, _, _, cM_ok, tM_ok, bridge_minus⟩⟩

end Certificates
