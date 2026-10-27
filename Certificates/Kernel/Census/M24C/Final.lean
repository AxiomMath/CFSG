module

public import Certificates.Kernel.Census.M24C.Bind
public import Certificates.Kernel.Census.M24C.T
public import Certificates.Kernel.Census.M24C.N0
public import Certificates.Kernel.Census.M24C.N1
public import Certificates.Kernel.Census.M24C.N2
public import Certificates.Kernel.Census.M24C.N3
public import Certificates.Kernel.Census.M24C.E0
public import CFSG.Certificates.Kernel.Census.ConjProof
public import CFSG.Certificates.Kernel.Census.XsProof
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicM24C

public section

namespace CertificateChecks.KernelCensus.M24C

open CFSG.KC.Census CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.RankThree.Native
open CFSG.ComponentClassification.RankTwoSporadic.Cert CFSG.ComponentClassification.RankTwoSporadic.M22
open CFSG.ComponentClassification.RankTwoSporadic.M24

theorem nodes_all : ∀ i < d.nodes.size, nodeF i = true := by
  intro i hi
  rw [Nat.eq_of_beq_eq_true kNs] at hi
  by_cases h1 : i < 83
  · exact List.all_eq_true.1 kN0 i (List.mem_range'_1.2 ⟨by omega, by omega⟩)
  by_cases h2 : i < 166
  · exact List.all_eq_true.1 kN83 i (List.mem_range'_1.2 ⟨by omega, by omega⟩)
  by_cases h3 : i < 249
  · exact List.all_eq_true.1 kN166 i (List.mem_range'_1.2 ⟨by omega, by omega⟩)
  · exact List.all_eq_true.1 kN249 i (List.mem_range'_1.2 ⟨by omega, by omega⟩)

theorem m24_conj : ∃ (xg xs : Array (Array ℕ)) (xw : List (List ℕ)) (D : ConjData)
    (e : Array (Array ℕ)) (wit : Wit) (cl : ClosW), m24CheckC xg xs xw D e wit cl = true := by
  have hxs : ∀ P ∈ d.xs, canon1 24 5 P = true := by
    have h := kCanon
    unfold canonC at h
    simp only [Bool.and_eq_true] at h
    exact List.all_eq_true.1 h.1.1.1.1.1.1
  have hin : ∀ P, canon1 24 5 P = true → pvalid 24 5 P = true →
      inXP P = inXL 24 (Xs.map (unpackP 24 5)) (unpackP 24 5 P) :=
    fun P hP _ => pinXL_eq hP kXc
  have hc := pconjCensus_sound_proved (ps := m22PS) (outX := allA) (outXP := fun _ => true)
    (allowPW := true) (allowInX := false) (allowU := false) (by norm_num) (by norm_num)
    (by norm_num) kCanon kE0c hin (fun _ _ _ => rfl) hin kPc kInv kTab kRl kR nodes_all
  refine ⟨xg.map (unpackP 24 5), Xs.map (unpackP 24 5), xw, d.toMain 24 5, e0.map (unpackP 24 5),
    e0wit.toMain 24 5, clE, ?_⟩
  unfold m24CheckC
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨⟨⟨kXG, xsOK_of_pxsOK_proved (by norm_num) (by norm_num) (by norm_num) kGc kXc kXs⟩,
    hc⟩, ?_⟩, ?_⟩, kE0e⟩, kE0w⟩
  · simp only [ConjDataP.toMain, List.all_map]
    refine List.all_eq_true.2 fun P hP => ?_
    rw [Function.comp_apply, ← pinXL_eq (hxs P hP) kXc]
    exact List.all_eq_true.1 kW P hP
  · simp only [ConjDataP.toMain, List.length_map]
    exact Nat.eq_of_beq_eq_true kLen

end CertificateChecks.KernelCensus.M24C

end
