module

public import Certificates.Kernel.CoreGen.Runs
public import Certificates.Kernel.MatCert.Glue
public import CFSG.Certificates.Kernel.CoreGenNSound
import all CFSG.Blueprint.NativeSporadic

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCG

open CFSG.KC.OpsMN CFSG.KC.OpsK CFSG.KC.OpsHom CFSG.KC.Ord CFSG.KS.SporSch.LyM
open CFSG.SectionRank.Native CFSG.AGLEmbedding.R3 CFSG.Blueprint CertificateChecks.KernelMC

theorem thCore : coreGenCheck (ops2 248) NativeSporadic.ThSeed1 NativeSporadic.ThSeed2
    CoreTh5.nregs CoreTh5.prog CoreTh5.spec = true :=
  coreGenCheck_of_N (hom2 248 (by norm_num)) thA thB trivial trivial th_D.1 th_D.2.1 th_K th_D.2.2

theorem j4Core : coreGenCheck (ops2 112) NativeSporadic.J4Seed1 NativeSporadic.J4Seed2
    CoreJ43.nregs CoreJ43.prog CoreJ43.spec = true :=
  coreGenCheck_of_N (hom2 112 (by norm_num)) j4A j4B trivial trivial j4_D.1 j4_D.2.1 j4_K j4_D.2.2

theorem heA : (opsP 7 50).decode NativeSporadic.HeSeed1 = (homP heConsts (by norm_num)).U
    (payHe HeS1.chars) := by
  rw [HeS1.eq]
  exact payRunP_eqL _ (by norm_num) (by norm_num) (by norm_num)

theorem heB : (opsP 7 50).decode NativeSporadic.HeSeed2 = (homP heConsts (by norm_num)).U
    (payHe HeS2.chars) := by
  rw [HeS2.eq]
  exact payRunP_eqL _ (by norm_num) (by norm_num) (by norm_num)

theorem he3Core : coreGenCheck (opsP 7 50) NativeSporadic.HeSeed1 NativeSporadic.HeSeed2
    CoreHe3.nregs CoreHe3.prog CoreHe3.spec = true := by
  have h := he3_K
  rw [forceB_eq, forceB_eq] at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hA, hB⟩, h⟩ := h
  exact coreGenCheck_of_N (homP heConsts (by norm_num)) heA heB hA hB he3_D.1 he3_D.2.1 h
    he3_D.2.2

theorem he7Core : coreGenCheck (opsP 7 50) NativeSporadic.HeSeed1 NativeSporadic.HeSeed2
    CoreHe7.nregs CoreHe7.prog CoreHe7.spec = true := by
  have h := he7_K
  rw [forceB_eq, forceB_eq] at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hA, hB⟩, h⟩ := h
  exact coreGenCheck_of_N (homP heConsts (by norm_num)) heA heB hA hB he7_D.1 he7_D.2.1 h
    he7_D.2.2

end CertificateChecks.KernelCG

end
