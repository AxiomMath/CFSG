module

public import Certificates.Kernel.D4.Facts
public import Certificates.Kernel.D4.ChecksL
public import CFSG.Certificates.Kernel.K426KSound
public import CFSG.Certificates.Kernel.HeDihKSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelD4

open CFSG.RankThree.PartTwo.Sec4.Item434D42 CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.B3S3K
open CFSG.KC.Misc.ArrEnum CFSG.KC.D4K CFSG.KC.BfsPin CFSG.KC.K426K CFSG.KC.HeDih
open CFSG.Monster.B.Co2.Native CFSG.RankThree.Native CFSG.Monster.B.Fischer
open CFSG.RankThree.PartTwo.KFacts.K426 CFSG.HardMathSupport.Dickson.Bal207.Fam3D42
open CFSG.HardMathSupport.Dickson.I271.L28Presentation
open CFSG.Monster.B.Co2 (allLt_iff)

theorem ngA3 : EA.ng = 3 := Nat.eq_of_beq_eq_true bG.2.1

theorem ngL2 : EL.ng = 2 := Nat.eq_of_beq_eq_true gL.2.2.1

theorem ppA : ∀ k < 3, PP 2457 12 (EA.G k) := fun k hk =>
  pp_of_permB szOK' (pGA k (by rw [ngA3]; exact hk))

theorem gensA : ∀ k < 3, d4CAGens[k]! = unpack 2457 12 (EA.G k) := fun k hk =>
  bindG.2 k (by rw [ngA3]; exact hk)

theorem wordL : ∀ k < 2, (lGens ())[k]! = unpack 2457 12 (EL.G k) ∧ PP 2457 12 (EL.G k) := by
  intro k hk
  obtain ⟨a1, a2⟩ := evalWA_unpack szOK' gensA ppA lWordA
  obtain ⟨b1, b2⟩ := evalWA_unpack szOK' gensA ppA lWordB
  have e0 : EL.G 0 = evalWK 2457 12 EA.G lWordA := Nat.eq_of_beq_eq_true gL.1
  have e1 : EL.G 1 = evalWK 2457 12 EA.G lWordB := Nat.eq_of_beq_eq_true gL.2.1
  interval_cases k
  · have e : (lGens ())[0]! = evalWA 2457 d4CAGens lWordA := rfl
    rw [e, a1, e0]
    exact ⟨rfl, a2⟩
  · have e : (lGens ())[1]! = evalWA 2457 d4CAGens lWordB := rfl
    rw [e, b1, e1]
    exact ⟨rfl, b2⟩

theorem bindL3 : BindA 2457 12 (lGens ()) EL.ng EL.G := by
  refine ⟨by rw [ngL2]; rfl, fun k hk => ?_⟩
  rw [ngL2] at hk
  exact (wordL k hk).1

theorem pL3 : ∀ k < EL.ng, permB 2457 12 (EL.G k) = true := fun k hk => by
  rw [ngL2] at hk
  exact permB_of_pp (wordL k hk).2

theorem okL : bfsK 2457 12 EL.ng EL.G EL.N EL.T EL.E EL.S = true :=
  bfsK_of_slices (L := 56) (K := 9) (C := EL.C) (by decide) (by norm_num) szOK' EL.g EL.csAll EL.t0
    EL.dist (Nat.eq_of_beq_eq_true EL.c0) (Nat.eq_of_beq_eq_true EL.cK) EL.rsAll

theorem enumL3 : enumOK 2457 (lGens ()) d4Keys (lCert ()) = true ∧ (lCert ()).pts.size = EL.N ∧
    ∀ i < EL.N, (lCert ()).pts[i]! = unpack 2457 12 (EL.T i) := by
  have h := enum_of (fuel := 520) bindL3 pL3 okL (mem_base_lt bindsA CA.hl) EL.keys
    (by rw [Nat.eq_of_beq_eq_true gL.2.2.2]; norm_num)
  rw [keys_eq] at h
  exact h

theorem derived_ok : derivedLeOK 2457 d4CAGens (lGens ()) d4Keys (lCert ()) 504 = true :=
  derivedLeOK_of szOK' enumL3.1 enumL3.2.1 enumL3.2.2 (permB_pts okL pL3) bindG pGA bindL3 pL3
    (Nat.eq_of_beq_eq_true gL.2.2.2) derL

theorem mem_ok : allLt (lGens ()).size
    (fun l => d4CACert.pts.toList.any (eqA 2457 (lGens ())[l]!)) = true := by
  rw [allLt_iff]
  intro l hl
  rw [bindL3.1] at hl
  rw [bindL3.2 l hl]
  exact any_of_memIdxK szOK' enumA.2.1 enumA.2.2 (permB_pts okA pGA) (Orb.allN_iff.1 memL l hl)

theorem words_ok : wordsOneOK 2457 (lGens ()) l28Words = true := by
  have hg : ∀ k < 2, (lGens ())[k]! = unpack 2457 12 (EL.G k) := fun k hk => (wordL k hk).1
  have hp : ∀ k < 2, PP 2457 12 (EL.G k) := fun k hk => (wordL k hk).2
  unfold wordsOneOK
  rw [Bool.and_eq_true, allLt_iff, List.all_eq_true]
  refine ⟨fun k hk => enumOK_gens_valid enumL3.1 hk, fun wd hwd => ?_⟩
  obtain ⟨h1, h2⟩ := evalWA_unpack szOK' hg hp wd
  rw [h1, idA_eq szOK', eqA_PP h2 (PP.id szOK')]
  exact List.all_eq_true.1 relL wd hwd

theorem caseA3_ok : caseA3Check () = true := by
  unfold caseA3Check
  simp only [derived_ok, mem_ok, words_ok, Bool.and_self]

end CertificateChecks.KernelD4

end
