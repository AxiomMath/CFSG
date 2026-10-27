module

public import Certificates.Kernel.Census.U42.Bind
public import Certificates.Kernel.Census.U42.T
public import Certificates.Kernel.Census.U42.N0
public import Certificates.Kernel.Census.U42.N1
public import CFSG.Certificates.Kernel.Census.SoundProof
public import CFSG.Certificates.Kernel.Common.ForallChunks
import all CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeData
import all CFSG.Sporadic.Schreier.TitsBasic
public import CFSG.Certificates.Kernel.Census.ToMainExc
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicExcW
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicGenCensus
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicPairCensus
public import CFSG.Monster.Code.Weights

public section

namespace CertificateChecks.KernelCensus.U42K

open CFSG.KC.Census CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.ComponentClassification.RankTwoHypIICover.U42
open CFSG.ComponentClassification.RankTwoSporadic.Cert

set_option maxRecDepth 1000000

#kc_forall_chunks nodes_c (fun k => (List.range' (20 * k) 20).all nodeF = true) 9
  CertificateChecks.KernelCensus.U42K.kN 20

theorem nodes_ok : ∀ i < u42Nodes.size, nodeF i = true := by
  intro i hi
  rw [Nat.eq_of_beq_eq_true kNs] at hi
  rcases Nat.lt_or_ge i 180 with h | h
  · have hk : i / 20 < 9 := by omega
    exact List.all_eq_true.1 (nodes_c (i / 20) hk) i (List.mem_range'_1.2 ⟨by omega, by omega⟩)
  · exact List.all_eq_true.1 kNt i (List.mem_range'_1.2 ⟨h, by omega⟩)

theorem getElem!_map_lt {α β : Type} [Inhabited α] [Inhabited β] (a : Array α) (f : α → β)
    {k : Nat} (hk : k < a.size) : (a.map f)[k]! = f a[k]! := by
  rw [getElem!_pos (a.map f) k (by simpa using hk), Array.getElem_map, getElem!_pos a k hk]

theorem u42_ok : ∃ (sG roots : Array ℕ) (nodes : Array NodeP) (cS : ArrCertP)
    (wcs : Array (Array ArrCertP)), u42CheckW sG roots nodes cS wcs = true := by
  have hin : ∀ P, canon1 45 6 P = true → pvalid 45 6 P = true →
      inP P = u42InX (unpackP 45 6 P) := fun P hP hv => inP_eq hP hv
  have hcensus := pcensus_sound_proved (by norm_num) (by norm_num) kCanon hin hin kS kR nodes_ok
  have hchain := rawChainK_sound (NS := 3) (CH := 16) (chunks := 4) binds U42C.head U42C.hl
    (by norm_num) U42C.hs
  have hw : CFSG.EvenSmallLie.OmegaEight.wordsOf 2 u42Words =
      CFSG.Sporadic.Schreier.Co3.Native.wordsArr 2 6 u42Words := by
    decide +kernel
  refine ⟨u42SG, u42Roots, u42Nodes, u42CS, u42WCS, ?_⟩
  unfold u42CheckW
  rw [hw]
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨hchain, hcensus⟩, ?_⟩, ?_⟩
  · rw [allLt_iff]
    intro k hk
    rw [Array.size_map] at hk
    have h := List.all_eq_true.1 kG k (List.mem_range.2 hk)
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨hc1, hv1⟩, hc2⟩, hv2⟩, hor⟩ := h
    rw [getElem!_map_lt _ _ hk, ← unpackP_pc (by norm_num) (by norm_num) kF, ← inP_eq hc1 hv1,
      ← inP_eq hc2 hv2]
    exact hor
  · simp only [ArrCertP.toMain, Array.size_map]
    exact Nat.eq_of_beq_eq_true kSz

end CertificateChecks.KernelCensus.U42K

end
