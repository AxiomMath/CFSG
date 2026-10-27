module

public import Certificates.Data.TitsAschbacherE32Pairs
public import Certificates.Kernel.EvenBN.Lists
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Certificate7050Base

public section

set_option maxRecDepth 400000

namespace CertificateChecks.Batch27582

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin CFSG.Monster.B.Co2.Native
open CFSG.Sporadic.Schreier.Tits CertificateChecks.KernelSpor CertificateChecks.KernelSpor.Tits2268
open CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.TitsHelp
open CertificateChecks.KernelSporSch.TitsCentral CertificateChecks.KernelEvenBN
open Certificates.TitsAschbacherParrott Certificates.TitsAschbacherE32

@[expose] noncomputable def pc (p q : Nat) : Nat := pcomp 1755 11 (mask 11) p q

@[expose] noncomputable def pairK (m₁ m₂ : Nat) : Bool :=
  Nat.beq (EL.getD m₁ 0) (pidn 1755 11) || Nat.beq (EL.getD m₁ 0) (V 12) ||
    Nat.beq (EL.getD m₂ 0) (pidn 1755 11) || Nat.beq (EL.getD m₂ 0) (V 12) ||
    Nat.beq (EL.getD m₂ 0) (EL.getD m₁ 0) || Nat.beq (EL.getD m₂ 0) (pc (EL.getD m₁ 0) (V 12)) ||
    pairTbl.any fun e => e.1 == m₁ % 16 && e.2.1 == m₂ % 16 && jLetters e.2.2 &&
      strictB (wP TitsJ.S e.2.2) fun J =>
        Nat.beq (pc J (EL.getD m₁ 0)) (pc (EL.getD m₁ 0) J) &&
          Nat.beq (pc J (EL.getD m₂ 0)) (pc (pc (EL.getD m₂ 0) (V 12)) J)

theorem k0 : ((List.range 8).all fun m₁ => (List.range 32).all fun m₂ => pairK m₁ m₂) = true := by
  quickRfl
theorem k1 : ((List.range' 8 8).all fun m₁ => (List.range 32).all fun m₂ => pairK m₁ m₂) = true := by
  quickRfl
theorem k2 : ((List.range' 16 8).all fun m₁ => (List.range 32).all fun m₂ => pairK m₁ m₂) = true := by
  quickRfl
theorem k3 : ((List.range' 24 8).all fun m₁ => (List.range 32).all fun m₂ => pairK m₁ m₂) = true := by
  quickRfl

theorem jW {w : List Nat} (hw : jLetters w = true) :
    jArr w = unpack 1755 11 (wP TitsJ.S w) ∧ C (wP TitsJ.S w) := by
  refine chain_gen bindsJ canJ fun j hj => ?_
  have := List.all_eq_true.1 hw j hj
  simp only [decide_eq_true_eq] at this
  omega

theorem pair_eq {m₁ m₂ : Nat} (h1 : m₁ < 32) (h2 : m₂ < 32) :
    Certificates.TitsAschbacherE32.pairOK (EL.map (unpack 1755 11)) m₁ m₂ = pairK m₁ m₂ := by
  have l1 : m₁ < EL.length := by rw [EL_len]; exact h1
  have l2 : m₂ < EL.length := by rw [EL_len]; exact h2
  have ca := eArrs_eq.2 _ (getD_mem l1)
  have cb := eArrs_eq.2 _ (getD_mem l2)
  obtain ⟨hz, cz⟩ := v_eq (i := 12) (by decide)
  unfold Certificates.TitsAschbacherE32.pairOK pairK
  simp only []
  rw [getD_mapU l1, getD_mapU l2, vA_eq (i := 12) (by decide),
    CertificateChecks.KernelSporSch.TitsCentral.id_eq, eqU ca canId, eqU ca cz, eqU cb canId, eqU cb cz,
    eqU cb ca, cmpU ca cz, eqU cb (cmpC ca cz)]
  congr 1
  refine any_congr_mem fun e he => ?_
  cases hl : jLetters e.2.2
  · simp only [Bool.and_false, Bool.false_and]
  · obtain ⟨hj, cj⟩ := jW hl
    unfold commA conjToA
    rw [hj, cmpU cj ca, cmpU ca cj, eqU (cmpC cj ca) (cmpC ca cj), cmpU cj cb, cmpU cb cz,
      cmpU (cmpC cb cz) cj, eqU (cmpC cj cb) (cmpC (cmpC cb cz) cj), strictB_app]
    simp only [Bool.and_assoc]
    rfl

theorem tits_e32_pair_check_0 : pairCheck () = true := by
  unfold pairCheck
  simp only []
  rw [eArrs_eq.1]
  rw [all_congr_mem fun m₁ hm₁ => all_congr_mem fun m₂ hm₂ =>
    pair_eq (List.mem_range.1 hm₁) (List.mem_range.1 hm₂)]
  refine List.all_eq_true.2 fun m₁ hm₁ => ?_
  have h := List.mem_range.1 hm₁
  by_cases a : m₁ < 8
  · exact List.all_eq_true.1 k0 m₁ (List.mem_range.2 a)
  by_cases b : m₁ < 16
  · exact List.all_eq_true.1 k1 m₁ (List.mem_range'_1.2 ⟨by omega, by omega⟩)
  by_cases c : m₁ < 24
  · exact List.all_eq_true.1 k2 m₁ (List.mem_range'_1.2 ⟨by omega, by omega⟩)
  · exact List.all_eq_true.1 k3 m₁ (List.mem_range'_1.2 ⟨by omega, by omega⟩)

end CertificateChecks.Batch27582

namespace Certificates

open CertificateChecks

theorem certificate27582 : Certificates.TitsAschbacherE32.pairCheck () = true := by
  exact CertificateChecks.Batch27582.tits_e32_pair_check_0

end Certificates
