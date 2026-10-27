module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocalMSecData
public import CFSG.Blueprint.NativeSporadic
public import Certificates.Data.CFSGNative.SectionRank.F2
public import Certificates.Data.CFSGNative.SectionRank.F3
import Certificates.Kernel.FongSporM.MSecT
import Certificates.Kernel.TcGen.F2Glue
import CFSG.Certificates.Kernel.OpsMcertTSound
import CFSG.Certificates.Kernel.OpsLayMcertSound
import CFSG.Certificates.Kernel.OpsLayTSound
import all CFSG.Blueprint.NativeSporadic

public section

open CFSG.KC.OpsMN CFSG.KC.OpsK CFSG.KC.OpsLayK CFSG.SectionRank.Native CFSG.Blueprint
  CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal CertificateChecks.KernelTc
  CertificateChecks.KernelMSec

namespace Certificates

open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal CFSG.SectionRank.Native CFSG.Blueprint in
theorem certificate40262 : MSec.check (ops3 21) NativeSporadic.McLSeed1 NativeSporadic.McLSeed2 mcl_7_claims = true ∧
    MSec.check (ops2 22) NativeSporadic.Co3Seed1 NativeSporadic.Co3Seed2 co3_11_claims = true ∧
    MSec.check (ops3 64) NativeSporadic.SuzSeed1 NativeSporadic.SuzSeed2 suz_7_claims = true := by
  have hD := ch40262T_wf
  simp only [Bool.and_eq_true] at hD
  obtain ⟨⟨hm, h3⟩, hs⟩ := hD
  have hc := ch40262T_co3
  rw [CFSG.KC.OpsMT.mcertT_eq] at hc
  have hl := ch40262T_mcl
  rw [mcertLT_eq] at hl
  have hz := ch40262T_suz
  rw [mcertLT_eq] at hz
  refine ⟨?_, ?_, ?_⟩
  · rw [MSec.check, hm, Bool.true_and]
    exact mcertL_sound (d := 21) McL.lay_ok rfl rfl McL.decA McL.decB McL.LA_eq McL.LB_eq hl
  · rw [MSec.check, h3, Bool.true_and]
    exact mcertCheck_of_N (hom2 22 (by norm_num)) c3A c3B trivial trivial hc
  · rw [MSec.check, hs, Bool.true_and]
    exact mcertL_sound (d := 64) Suz.lay_ok rfl rfl Suz.decA Suz.decB Suz.LA_eq Suz.LB_eq hz

end Certificates
