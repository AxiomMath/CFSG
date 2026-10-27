module

public import Certificates.Kernel.Census.M12.Bind
public import Certificates.Kernel.Census.M12.T
public import Certificates.Kernel.Census.M12.N0
public import CFSG.Certificates.Kernel.Census.ExcProof
public import CFSG.Certificates.Kernel.Common.ForallChunks
import all CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicM12W
import all CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicM12Tests
import all CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicM12Data
import all CFSG.Sporadic.Schreier.TitsBasic
import all CFSG.RankThree.PartOne.KS.PKit
import all Certificates.Data.CFSGNative.MonsterB.Co2Chain
import all Init.Data.Nat.Fold
import all Init.Data.Range.Basic

public section

namespace CertificateChecks.KernelCensus.M12K

open CFSG.KC.Census CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.ComponentClassification.RankTwoSporadic CFSG.ComponentClassification.RankTwoSporadic.M12
open CFSG.ComponentClassification.RankTwoSporadic.Cert CFSG.RankThree.PartOne

set_option maxRecDepth 1000000

#kc_forall_chunks nodes_c (fun k => (List.range' (61 * k) 61).all nodeF = true) 2
  CertificateChecks.KernelCensus.M12K.kN 61

theorem getElem!_map_lt {α β : Type} [Inhabited α] [Inhabited β] (a : Array α) (f : α → β)
    {k : Nat} (hk : k < a.size) : (a.map f)[k]! = f a[k]! := by
  rw [getElem!_pos (a.map f) k (by simpa using hk), Array.getElem_map, getElem!_pos a k hk]

theorem m12_ok : ∃ (sG roots : Array ℕ) (nodes : Array NodeP) (cS : ArrCertP)
    (wcs : Array (Array ArrCertP)) (excs : List ExcRefP),
    m12CheckW m12S m12W m12E0 sG roots nodes cS wcs excs = true := by
  have hin : ∀ P, canon1 24 5 P = true → pvalid 24 5 P = true →
      inP P = m12InP m12S (unpackP 24 5 P) := fun P hP hv => inP_eq hP hv
  have hinW : ∀ P, canon1 24 5 P = true → pvalid 24 5 P = true →
      inRP P = m12InR m12S (unpackP 24 5 P) := fun P hP hv => inRP_eq hP hv
  have hN : ∀ i < m12Nodes.size, nodeF i = true := by
    intro i hi
    rw [Nat.eq_of_beq_eq_true kNs] at hi
    have hk : i / 61 < 2 := by omega
    exact List.all_eq_true.1 (nodes_c (i / 61) hk) i (List.mem_range'_1.2 ⟨by omega, by omega⟩)
  have hcensus := pcensusExc_sound_proved (by norm_num) (by norm_num) kCanon kE0 kEx hin hin
    hinW kS kR hN
  rw [he0] at hcensus
  have hchain := rawChainK_sound (NS := 2) (CH := 16) (chunks := 1) binds M12C.head M12C.hl
    (by norm_num) M12C.hs
  have hw : CFSG.Sporadic.Schreier.Co3.Native.wordsArr 2 12 m12DW = m12W := by
    decide +kernel
  rw [hw] at hchain
  have hab : eqA 24 m12S[0]! m12A1Arr = true ∧ eqA 24 m12S[1]! m12B1Arr = true := by
    decide +kernel
  refine ⟨m12SG, m12Roots, m12Nodes, m12CS, m12WCS, m12Excs, ?_⟩
  unfold m12CheckW caseChainOK2P
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
  refine ⟨⟨⟨⟨by decide +kernel, ⟨hchain, hab.1⟩, hab.2⟩, hcensus⟩, ?_⟩, ?_⟩
  · rw [allLt_iff]
    intro k hk
    rw [Array.size_map] at hk
    have h := List.all_eq_true.1 kG k (List.mem_range.2 hk)
    simp only [Bool.and_eq_true] at h
    rw [getElem!_map_lt _ _ hk]
    have := inRP_eq h.1 (pvalid_of_penumOK kS hk)
    unfold inRP m12InR at this
    rw [← this]
    exact h.2
  · simp only [ArrCertP.toMain, Array.size_map]
    exact Nat.eq_of_beq_eq_true kSz

end CertificateChecks.KernelCensus.M12K

end
