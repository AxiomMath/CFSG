module

public import Certificates.Kernel.Census.J2.Bind
public import Certificates.Kernel.Census.J2.TII
public import Certificates.Kernel.Census.J2.LII0
public import Certificates.Kernel.Census.J2.LII1
public import Certificates.Kernel.Census.J2.TExc
public import Certificates.Kernel.Census.J2.LExc0
public import Certificates.Kernel.Census.J2.LExc1
public import CFSG.Certificates.Kernel.Census.PackedLProof
public import CFSG.Certificates.Kernel.Census.SoundProof
public import CFSG.Certificates.Kernel.Census.ExcProof
public import CFSG.Certificates.Kernel.Common.ForallChunks

public section

namespace CertificateChecks.KernelCensus.J2K

open CFSG.KC.Census CFSG.KC.Enum CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.ComponentClassification.RankTwoSporadic CFSG.ComponentClassification.RankTwoSporadic.J2
open CFSG.ComponentClassification.RankTwoSporadic.Cert CFSG.ComponentClassification.J2Cover

set_option maxRecDepth 1000000

#kc_forall_chunks nodesII_c (fun k => blkIIL (58 * k) 58 = true) 4
  CertificateChecks.KernelCensus.J2K.kIIL 58

#kc_forall_chunks nodesExc_c (fun k => blkExcL (58 * k) 58 = true) 4
  CertificateChecks.KernelCensus.J2K.kExcL 58

theorem blkIIL_all {a len : Nat} (h : blkIIL a len = true) :
    (List.range' a len).all (nodeIIL (pinvFl 315 9 j2IICS)) = true := by
  unfold blkIIL at h
  rwa [withFl_eq] at h

theorem blkExcL_all {a len : Nat} (h : blkExcL a len = true) :
    (List.range' a len).all (nodeExcL (pinvFl 315 9 j2ExcCS)) = true := by
  unfold blkExcL at h
  rwa [withFl_eq] at h

theorem ps_eq : j2PS = [0, 4, 3] := rfl

theorem j2II_ok : ∃ (sG roots : Array ℕ) (nodes : Array NodeP) (cS : ArrCertP)
    (wcs : Array (Array ArrCertP)), j2CheckWII sG roots nodes cS wcs = true := by
  have hin : ∀ P, canon1 315 9 P = true → pvalid 315 9 P = true →
      inP P = j2InP (unpackP 315 9 P) := fun P hP hv => inP_eq hP hv
  have hN : ∀ i < j2IINodes.size, pnodeOK 315 9 j2PS inP inP false true false j2IICS j2IINodes
      (pcN 315 9 j2IINodes) j2IIWCS i = true := by
    intro i hi
    rw [← pnodeL_eq (n := 315) (w := 9) (fun j hj => pcN_getElem! j2IINodes hj) hi, ps_eq]
    rw [Nat.eq_of_beq_eq_true kNSII] at hi
    have hk : i / 58 < 4 := by omega
    exact List.all_eq_true.1 (blkIIL_all (nodesII_c (i / 58) hk)) i
      (List.mem_range'_1.2 ⟨by omega, by omega⟩)
  have hR : ((List.range j2IICS.pts.size).all fun p =>
      prootOK 315 9 j2IINodes (pcN 315 9 j2IINodes) j2IICS.pts[p]! j2IIRoots[p]!) = true := by
    rw [cNLII_eq]
    exact kRII
  have hcensus := pcensus_sound_proved (by norm_num) (by norm_num) kCanonII hin hin
    kSII hR hN
  refine ⟨j2IISG, j2IIRoots, j2IINodes, j2IICS, j2IIWCS, ?_⟩
  unfold j2CheckWII
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨hcensus, gens_of kSII kGII⟩, ?_⟩
  simp only [ArrCertP.toMain, Array.size_map]
  exact Nat.eq_of_beq_eq_true kSzII

theorem j2Exc_ok : ∃ (sG roots : Array ℕ) (nodes : Array NodeP) (cS : ArrCertP)
    (wcs : Array (Array ArrCertP)) (excs : List ExcRefP),
    j2CheckWExc j2E0 sG roots nodes cS wcs excs = true := by
  have hin : ∀ P, canon1 315 9 P = true → pvalid 315 9 P = true →
      inP P = j2InP (unpackP 315 9 P) := fun P hP hv => inP_eq hP hv
  have hinW : ∀ P, canon1 315 9 P = true → pvalid 315 9 P = true →
      inRP P = j2InR (unpackP 315 9 P) := fun P hP hv => inRP_eq hP hv
  have hN : ∀ i < j2ExcNodes.size, pnodeExcOK 315 9 j2PS inP inP inRP false false false j2ExcCS
      j2ExcNodes (pcN 315 9 j2ExcNodes) j2ExcWCS j2ExcE0P j2ExcExcs i = true := by
    intro i hi
    rw [← pnodeExcL_eq (n := 315) (w := 9) (fun j hj => pcN_getElem! j2ExcNodes hj) hi,
      cNLExc_eq, ps_eq]
    rw [Nat.eq_of_beq_eq_true kNSExc] at hi
    have hk : i / 58 < 4 := by omega
    exact List.all_eq_true.1 (blkExcL_all (nodesExc_c (i / 58) hk)) i
      (List.mem_range'_1.2 ⟨by omega, by omega⟩)
  have hR : ((List.range j2ExcCS.pts.size).all fun p =>
      prootOK 315 9 j2ExcNodes (pcN 315 9 j2ExcNodes) j2ExcCS.pts[p]! j2ExcRoots[p]!) = true := by
    rw [cNLExc_eq]
    exact kRExc
  have hcensus := pcensusExc_sound_proved (by norm_num) (by norm_num) kCanonExc kE0Exc kExExc hin
    hin hinW kSExc hR hN
  rw [he0Exc] at hcensus
  refine ⟨j2ExcSG, j2ExcRoots, j2ExcNodes, j2ExcCS, j2ExcWCS, j2ExcExcs, ?_⟩
  unfold j2CheckWExc
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨hcensus, gens_of kSExc kGExc⟩, ?_⟩
  simp only [ArrCertP.toMain, Array.size_map]
  exact Nat.eq_of_beq_eq_true kSzExc

end CertificateChecks.KernelCensus.J2K

end
