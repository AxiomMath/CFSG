module

public import Certificates.Data.HePresCheck
public import CFSG.Certificates.Kernel.CosetJ.ModelSound
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo
import all Certificates.Data.HePresData
import all Certificates.Data.HePresCheck

#kc_repo #kc_json_gz CertificateChecks.KernelCosetJ.HeModel
  "Certificates/Kernel/CosetJ/data/hemodel.json.gz" 7868 2565357447463072950
  (IC0 : List (List Nat)) (IC1 : List (List Nat)) (IE : List (List Nat)) (IF : List (List Nat))
  (RC : List (List (Nat × Bool))) (RE : List (List (Nat × Bool))) (RF : List (List (Nat × Bool)))

public section

namespace CertificateChecks.KernelCosetJ.HeModel

open CFSG.ComponentClassification.AS81.HePres.Native CFSG.KC.CosetJ.Model CFSG.KC.MiscCoset

theorem relsC_eq : hePiRelsC.map encW = RC := by decide +kernel
theorem relsE_eq : hePiRelsE.map encW = RE := by decide +kernel
theorem relsF_eq : hePiRelsF.map encW = RF := by decide +kernel

theorem kC0 : modelK 32 8 ((hePiCArrs false).toList.map Array.toList) IC0 RC = true := by quickRfl
theorem kC1 : modelK 32 8 ((hePiCArrs true).toList.map Array.toList) IC1 RC = true := by quickRfl
theorem kE : modelK 64 8 (hePiEArrs.toList.map Array.toList) IE RE = true := by quickRfl
theorem kF : modelK 64 8 (hePiFArrs.toList.map Array.toList) IF RF = true := by quickRfl

theorem modelC0 : modelCheck 32 (hePiCArrs false) hePiRelsC = true :=
  modelK_sound (by rw [relsC_eq]; exact kC0)

theorem modelC1 : modelCheck 32 (hePiCArrs true) hePiRelsC = true :=
  modelK_sound (by rw [relsC_eq]; exact kC1)

theorem modelE : modelCheck 64 hePiEArrs hePiRelsE = true :=
  modelK_sound (by rw [relsE_eq]; exact kE)

theorem modelF : modelCheck 64 hePiFArrs hePiRelsF = true :=
  modelK_sound (by rw [relsF_eq]; exact kF)

end CertificateChecks.KernelCosetJ.HeModel

end
