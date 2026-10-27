module

public import Certificates.Kernel.Census.M2217.Bind
public import Certificates.Kernel.Census.M2217.T
public import Certificates.Kernel.Census.M2217.W
public import Certificates.Kernel.Census.M2217.L0
public import Certificates.Kernel.Census.M2217.L1
public import CFSG.Certificates.Kernel.Census.PackedLProof
public import CFSG.Certificates.Kernel.Census.Sound2Proof
public import CFSG.Certificates.Kernel.Census.XsProof
public import CFSG.Certificates.Kernel.Common.ForallChunks
public import CFSG.Certificates.Kernel.Census.ToMainExc
public import CFSG.Certificates.Kernel.Spor.SiftEq
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicExcW
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicGenCensus
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicPairCensus

public section

namespace CertificateChecks.KernelCensus.M2217

open CFSG.KC.Census CFSG.KC.Enum CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.ComponentClassification.RankTwoSporadic.M22 CFSG.ComponentClassification.RankTwoSporadic.Cert

set_option maxRecDepth 1000000

#kc_forall_chunks nodes_c (fun k => blkL (30 * k) 30 = true) 14
  CertificateChecks.KernelCensus.M2217.kL 30

#kc_forall_chunks words_c (fun k => (List.range' (120 * k) 120).all wordF = true) 10
  CertificateChecks.KernelCensus.M2217.kW 120

theorem nodes_ok : ∀ i < m2217Nodes.size, nodeF i = true := by
  intro i hi
  have he : nodeL (pinvFl 24 5 m2217CS) i = nodeF i := by
    unfold nodeL nodeF
    exact pnodeL2_eq (fun j hj => pcN_getElem! m2217Nodes hj) hi
  have hb : ∀ {a len : Nat}, blkL a len = true →
      (List.range' a len).all (nodeL (pinvFl 24 5 m2217CS)) = true := fun h => by
    unfold blkL at h
    rwa [withFl_eq] at h
  rw [← he]
  rw [Nat.eq_of_beq_eq_true kNs] at hi
  rcases Nat.lt_or_ge i 420 with h | h
  · have hk : i / 30 < 14 := by omega
    exact List.all_eq_true.1 (hb (nodes_c (i / 30) hk)) i
      (List.mem_range'_1.2 ⟨by omega, by omega⟩)
  · exact List.all_eq_true.1 (hb kLt) i (List.mem_range'_1.2 ⟨h, by omega⟩)

theorem words_ok : pxsOK 24 5 m2217XG m2217XS m2217XW = true := by
  have h : ∀ k < m2217XS.size, wordF k = true := by
    intro k hk
    rw [Nat.eq_of_beq_eq_true kXs] at hk
    rcases Nat.lt_or_ge k 1200 with h | h
    · have hk' : k / 120 < 10 := by omega
      exact List.all_eq_true.1 (words_c (k / 120) hk') k
        (List.mem_range'_1.2 ⟨by omega, by omega⟩)
    · exact List.all_eq_true.1 kWt k (List.mem_range'_1.2 ⟨h, by omega⟩)
  unfold pxsOK
  exact List.all_eq_true.2 fun k hk => h k (List.mem_range.1 hk)

theorem m2217_ok : ∃ (sG roots : Array ℕ) (nodes : Array NodeP) (cS : ArrCertP)
    (wcs : Array (Array ArrCertP)) (pfs : Array PerfWP) (xg xs : Array ℕ) (xw : List (List ℕ)),
    m22CheckW2 true false sG roots nodes cS wcs pfs xg xs xw = true := by
  have hin : ∀ P, canon1 24 5 P = true → pvalid 24 5 P = true →
      pinXL m2217XS P = inXL 24 (m2217XS.map (unpackP 24 5)) (unpackP 24 5 P) :=
    fun P hP _ => pinXL_eq hP kXc
  have hout : ∀ P, canon1 24 5 P = true → pvalid 24 5 P = true →
      outXP P = m22OutX (unpackP 24 5 P) := fun P _ _ => outXP_eq P
  have hcensus := pcensus_sound2_proved (by norm_num) (by norm_num) kCanon hin hout kS kR nodes_ok
  have hxs := xsOK_of_pxsOK_proved (by norm_num) (by norm_num) (by norm_num) kGc kXc words_ok
  refine ⟨m2217SG, m2217Roots, m2217Nodes, m2217CS, m2217WCS, m2217PFS, m2217XG, m2217XS,
    m2217XW, ?_⟩
  unfold m22CheckW2
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨kXG, hxs⟩, hcensus⟩, kGen⟩, ?_⟩
  simp only [ArrCertP.toMain, Array.size_map]
  exact Nat.eq_of_beq_eq_true kSz

end CertificateChecks.KernelCensus.M2217

end
