module

public import Certificates.Kernel.Census.McL
public import CFSG.Certificates.Kernel.Census.SoundProof

public section

namespace CertificateChecks.KernelCensus.McLK

open CFSG.KC.Census CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.ComponentClassification.RankTwoSporadic CFSG.ComponentClassification.RankTwoSporadic.McL
open CFSG.ComponentClassification.RankTwoSporadic.Cert CFSG.Sporadic.Schreier
open CFSG.KC.Misc.HexFlat

set_option maxRecDepth 1000000

theorem mclCheckW_eq_true_proved : mclCheckW mclSG mclRoots mclNodes mclCS mclWCS = true := by
  have hin : ∀ P, canon1 275 9 P = true → pvalid 275 9 P = true →
      inP P = mclInP (unpackP 275 9 P) := fun P hP hv => inP_eq hP hv
  have hN : ∀ i < mclNodes.size, nodeF i = true := by
    rw [nodes_size]
    exact allRange_extend (a := 156) (len := 52) (allRange_extend (a := 104) (len := 52)
      (allRange_extend (a := 52) (len := 52) (allRange_extend (a := 0) (len := 52)
        (allRange_zero _) kN0) kN1) kN2) kN3
  have hcensus := pcensus_sound_proved (by norm_num) (by norm_num) kCanon hin hin kS kR hN
  unfold mclCheckW
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨hcensus, ?_⟩, ?_⟩
  · rw [allLt_iff]
    intro k hk
    rw [Array.size_map] at hk
    have h := List.all_eq_true.1 kG k (List.mem_range.2 hk)
    simp only [Bool.and_eq_true, Bool.or_eq_true] at h
    have hv := pvalid_of_penumOK kS hk
    rw [getElem!_map_lt _ _ hk, u_eq, ← unpackP_pc (by norm_num) (by norm_num) kU,
      ← inP_eq h.1 hv, ← inP_eq (canon1_pc (by norm_num) (by norm_num))
        (pvalid_pc (by norm_num) (by norm_num) kU kUV h.1 hv)]
    simpa only [Bool.or_eq_true] using h.2
  · simp only [ArrCertP.toMain, Array.size_map]
    decide +kernel

end CertificateChecks.KernelCensus.McLK

end
