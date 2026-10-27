module

public import Certificates.Data.KappaLemmaA
public import Certificates.Kernel.EvenBN.K561002
public import Certificates.Kernel.EvenBN.Lists
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Certificate7050Base

public section

set_option maxRecDepth 400000

namespace CertificateChecks.Batch561002

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin CFSG.Monster.B.Co2.Native
open CFSG.Sporadic.Schreier.Tits CertificateChecks.KernelSpor CertificateChecks.KernelSpor.Tits2268
open CertificateChecks.KernelSporSch.TitsHelp CertificateChecks.KernelSporSch.TitsCentral
open CertificateChecks.KernelEvenBN CertificateChecks.KernelEvenBN.K561002
open Certificates.TitsAschbacherParrott Certificates.KappaLemmaA

@[expose] noncomputable def pc (p q : Nat) : Nat := pcomp 1755 11 (mask 11) p q

@[expose] noncomputable def prodK (c : Fin 5 → ZMod 2) : Nat :=
  pc (pc (pc (pc (ppw (V 12) (c 0).val) (ppw (V 11) (c 1).val)) (ppw (V 10) (c 2).val))
    (ppw (V 9) (c 3).val)) (ppw (V 8) (c 4).val)

theorem modelK : ((List.finRange 3).all fun c => (List.finRange 5).all fun j =>
    Nat.beq (pc (TitsH.S c.val) (V (12 - j.val)))
      (pc (prodK fun i => kapA5 c i j) (TitsH.S c.val))) = true := by quickRfl

theorem pw {i : Nat} (hi : i < 13) (k : Nat) :
    powA (vA i) k = unpack 1755 11 (ppw (V i) k) ∧ C (ppw (V i) k) :=
  ⟨by rw [vA_eq hi, powU (cV hi)], powC (cV hi)⟩

theorem prodEA_eq (c : Fin 5 → ZMod 2) : prodEA c = unpack 1755 11 (prodK c) ∧ C (prodK c) := by
  obtain ⟨e0, c0⟩ := pw (i := 12) (by decide) (c 0).val
  obtain ⟨e1, c1⟩ := pw (i := 11) (by decide) (c 1).val
  obtain ⟨e2, c2⟩ := pw (i := 10) (by decide) (c 2).val
  obtain ⟨e3, c3⟩ := pw (i := 9) (by decide) (c 3).val
  obtain ⟨e4, c4⟩ := pw (i := 8) (by decide) (c 4).val
  unfold prodEA prodK pc
  rw [e0, e1, e2, e3, e4, cmpU c0 c1, cmpU (cmpC c0 c1) c2, cmpU (cmpC (cmpC c0 c1) c2) c3,
    cmpU (cmpC (cmpC (cmpC c0 c1) c2) c3) c4]
  exact ⟨rfl, cmpC (cmpC (cmpC (cmpC c0 c1) c2) c3) c4⟩

theorem model_eq : modelOK () = true := by
  unfold modelOK
  rw [← modelK]
  refine all_congr_mem fun c _ => all_congr_mem fun j _ => ?_
  have hc : c.val < 9 := by omega
  have hj : 12 - j.val < 13 := by omega
  have ch : C (TitsH.S c.val) := allN_spec canH c.val hc
  obtain ⟨hp, cp⟩ := prodEA_eq fun i => kapA5 c i j
  rw [bindsH.2.2.2.2.1 c.val hc, vA_eq hj, hp, cmpU ch (cV hj), cmpU cp ch,
    eqU (cmpC ch (cV hj)) (cmpC cp ch)]
  rfl

theorem kappa_lemma_a_check_0 : check () = true := by
  unfold check
  rw [model_eq, comboK, table0K, table1K]
  rfl

end CertificateChecks.Batch561002

namespace Certificates

open CertificateChecks

theorem certificate561002 : Certificates.KappaLemmaA.check () = true := by
  exact CertificateChecks.Batch561002.kappa_lemma_a_check_0

end Certificates
