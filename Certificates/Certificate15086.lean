module

public import Certificates.Data.HePresImage
import Certificates.Kernel.CosetJ.He
import Certificates.Kernel.CosetJ.HeImg
import Certificates.Kernel.CosetJ.HeModel

public section

namespace Certificates

open CertificateChecks

open CFSG.CosetTable CFSG.ComponentClassification.AS81.HePres.Native in
theorem certificate15086 :
    (Finite (PG 8 hePiRels) ∧ Nat.card (PG 8 hePiRels) ≤ 4030387200)
    ∧ HePiImageFacts
    ∧ (modelCheck 32 (hePiCArrs false) hePiRelsC = true)
    ∧ (modelCheck 32 (hePiCArrs true) hePiRelsC = true)
    ∧ (modelCheck 64 hePiEArrs hePiRelsE = true)
    ∧ (modelCheck 64 hePiFArrs hePiRelsF = true) :=
  ⟨KernelCosetJ.He.card_le, KernelCosetJ.HeImg.facts, KernelCosetJ.HeModel.modelC0,
    KernelCosetJ.HeModel.modelC1, KernelCosetJ.HeModel.modelE, KernelCosetJ.HeModel.modelF⟩

end Certificates
