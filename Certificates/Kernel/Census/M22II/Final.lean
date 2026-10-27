module

public import Certificates.Kernel.Census.M22II.Bind
public import Certificates.Kernel.Census.M22II.T
public import Certificates.Kernel.Census.M22II.L0
public import Certificates.Kernel.Census.M22II.L1
public import CFSG.Certificates.Kernel.Census.PackedLProof
public import CFSG.Certificates.Kernel.Census.SoundProof
public import CFSG.Certificates.Kernel.Census.XsProof
public import CFSG.Certificates.Kernel.Common.ForallChunks
public import CFSG.Certificates.Kernel.Census.ToMainExc
public import CFSG.Certificates.Kernel.Spor.SiftEq
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicExcW
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicGenCensus
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicPairCensus

public section

namespace CertificateChecks.KernelCensus.M22II

open CFSG.KC.Census CFSG.KC.Enum CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.ComponentClassification.RankTwoSporadic.M22 CFSG.ComponentClassification.RankTwoSporadic.Cert

set_option maxRecDepth 1000000

#kc_forall_chunks nodes_c (fun k => blkL (30 * k) 30 = true) 19
  CertificateChecks.KernelCensus.M22II.kL 30

#kc_forall_chunks words_c (fun k => (List.range' (120 * k) 120).all wordF = true) 8
  CertificateChecks.KernelCensus.M22II.kW 120

theorem nodes_ok : ∀ i < m22IINodes.size, nodeF i = true := by
  intro i hi
  have he : nodeL (pinvFl 24 5 m22IICS) i = nodeF i := by
    unfold nodeL nodeF
    exact pnodeL_eq (fun j hj => pcN_getElem! m22IINodes hj) hi
  have hb : ∀ {a len : Nat}, blkL a len = true →
      (List.range' a len).all (nodeL (pinvFl 24 5 m22IICS)) = true := fun h => by
    unfold blkL at h
    rwa [withFl_eq] at h
  rw [← he]
  rw [Nat.eq_of_beq_eq_true kNs] at hi
  rcases Nat.lt_or_ge i 570 with h | h
  · have hk : i / 30 < 19 := by omega
    exact List.all_eq_true.1 (hb (nodes_c (i / 30) hk)) i
      (List.mem_range'_1.2 ⟨by omega, by omega⟩)
  · exact List.all_eq_true.1 (hb kLt) i (List.mem_range'_1.2 ⟨h, by omega⟩)

theorem words_ok : pxsOK 24 5 m22IIXG m22IIXS m22IIXW = true := by
  have h : ∀ k < m22IIXS.size, wordF k = true := by
    intro k hk
    rw [Nat.eq_of_beq_eq_true kXs] at hk
    rcases Nat.lt_or_ge k 960 with h | h
    · have hk' : k / 120 < 8 := by omega
      exact List.all_eq_true.1 (words_c (k / 120) hk') k
        (List.mem_range'_1.2 ⟨by omega, by omega⟩)
    · exact List.all_eq_true.1 kWt k (List.mem_range'_1.2 ⟨h, by omega⟩)
  unfold pxsOK
  exact List.all_eq_true.2 fun k hk => h k (List.mem_range.1 hk)

theorem m22II_ok : ∃ (sG roots : Array ℕ) (nodes : Array NodeP) (cS : ArrCertP)
    (wcs : Array (Array ArrCertP)) (xg xs : Array ℕ) (xw : List (List ℕ)),
    m22CheckW false true sG roots nodes cS wcs xg xs xw = true := by
  have hin : ∀ P, canon1 24 5 P = true → pvalid 24 5 P = true →
      pinXL m22IIXS P = inXL 24 (m22IIXS.map (unpackP 24 5)) (unpackP 24 5 P) :=
    fun P hP _ => pinXL_eq hP kXc
  have hout : ∀ P, canon1 24 5 P = true → pvalid 24 5 P = true →
      outXP P = m22OutX (unpackP 24 5 P) := fun P _ _ => outXP_eq P
  have hcensus := pcensus_sound_proved (by norm_num) (by norm_num) kCanon hin hout kS kR nodes_ok
  have hxs := xsOK_of_pxsOK_proved (by norm_num) (by norm_num) (by norm_num) kGc kXc words_ok
  refine ⟨m22IISG, m22IIRoots, m22IINodes, m22IICS, m22IIWCS, m22IIXG, m22IIXS, m22IIXW, ?_⟩
  unfold m22CheckW
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨kXG, hxs⟩, hcensus⟩, kGen⟩, ?_⟩
  simp only [ArrCertP.toMain, Array.size_map]
  exact Nat.eq_of_beq_eq_true kSz

end CertificateChecks.KernelCensus.M22II

end
