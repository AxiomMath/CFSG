module

public import Certificates.Kernel.Census.M23.Bind
public import Certificates.Kernel.Census.M23.T
public import Certificates.Kernel.Census.M23.N0
public import CFSG.Certificates.Kernel.Census.Sound2Proof
public import CFSG.Certificates.Kernel.Common.ForallChunks
import all CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeData
import all CFSG.Sporadic.Schreier.TitsBasic
public import CFSG.Certificates.Kernel.Census.ToMainExc
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicExcW
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicPairCensus

public section

namespace CertificateChecks.KernelCensus.M23K

open CFSG.KC.Census CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.ComponentClassification.RankTwoSporadic CFSG.ComponentClassification.RankTwoSporadic.M23
open CFSG.ComponentClassification.RankTwoSporadic.Cert

set_option maxRecDepth 1000000

#kc_forall_chunks nodes_c (fun k => (List.range' (31 * k) 31).all nodeF = true) 4
  CertificateChecks.KernelCensus.M23K.kN 31

theorem nodes_ok : ∀ i < m23Nodes.size, nodeF i = true := by
  intro i hi
  rw [Nat.eq_of_beq_eq_true kNs] at hi
  have hk : i / 31 < 4 := by omega
  exact List.all_eq_true.1 (nodes_c (i / 31) hk) i (List.mem_range'_1.2 ⟨by omega, by omega⟩)

theorem getElem!_map_lt {α β : Type} [Inhabited α] [Inhabited β] (a : Array α) (f : α → β)
    {k : Nat} (hk : k < a.size) : (a.map f)[k]! = f a[k]! := by
  rw [getElem!_pos (a.map f) k (by simpa using hk), Array.getElem_map, getElem!_pos a k hk]

theorem m23_ok : ∃ (sG roots : Array ℕ) (nodes : Array NodeP) (cS : ArrCertP)
    (wcs : Array (Array ArrCertP)) (pfs : Array PerfWP),
    m23CheckW2 sG roots nodes cS wcs pfs = true := by
  have hin : ∀ P, canon1 23 5 P = true → pvalid 23 5 P = true →
      inP P = m23InXW (unpackP 23 5 P) := fun P hP hv => inP_eq hP hv
  have hout : ∀ P, canon1 23 5 P = true → pvalid 23 5 P = true →
      (fun _ => true) P = M24.allA (unpackP 23 5 P) := fun _ _ _ => rfl
  have hcensus := pcensus_sound2_proved (by norm_num) (by norm_num) kCanon hin hout kS kR nodes_ok
  have hchain := rawChainK_sound (NS := 2) (CH := 16) (chunks := 4) binds M23C.head M23C.hl
    (by norm_num) M23C.hs
  have hw : CFSG.EvenSmallLie.OmegaEight.wordsOf 2 m23DW =
      CFSG.Sporadic.Schreier.Co3.Native.wordsArr 2 13 m23DW := by
    decide +kernel
  refine ⟨m23SG, m23Roots, m23Nodes, m23CS, m23WCS, m23PFS, ?_⟩
  unfold m23CheckW2
  rw [hw]
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨hchain, hcensus⟩, ?_⟩, ?_⟩
  · rw [allLt_iff]
    intro k hk
    rw [Array.size_map] at hk
    have h := List.all_eq_true.1 kG k (List.mem_range.2 hk)
    simp only [Bool.and_eq_true] at h
    rw [getElem!_map_lt _ _ hk, ← inP_eq h.1 (pvalid_of_penumOK kS hk)]
    exact h.2
  · simp only [ArrCertP.toMain, Array.size_map]
    exact Nat.eq_of_beq_eq_true kSz

end CertificateChecks.KernelCensus.M23K

end
