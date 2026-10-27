module

public import CFSG.Monster.B.TwoA.Base.SevenPairAInputs
public import CFSG.Certificates.Kernel.SortTreeArr
public import Certificates.Kernel.MonsterB.Conj3052Data
import CFSG.Certificates.Kernel.Common.Harness

public section

open CFSG.Monster.B.TwoA.Census CFSG.Monster.B.TwoA CFSG.KC.SortTree CFSG.KLie.CT
  CFSG.KC.U6Orb

namespace CertificateChecks.Batch3052

open CFSG.Monster.B.TwoA.Census CFSG.Monster.B.TwoA CFSG.KC.SortTree CFSG.KLie.CT
  CFSG.KC.U6Orb

set_option maxRecDepth 100000

noncomputable abbrev actC (k c : ℕ) : ℕ :=
  aconjK (packL 5 gensP[k]!.toList) (packL 5 (ainv gensP[k]!).toList) c

theorem kGen : (List.range 3).all (fun k => PermArr gensP[k]!) = true := by quickRfl

theorem kRoot : (PermArr sig2Arr && PermArr sig3Arr && gensP.size == 3) = true := by quickRfl

theorem t2 : treeOK actC 3 (fun _ => true) (akey sig2Arr) (recT Conj3052.A2 6 128)
    1155 111 4 11 64 19 = true := by quickRfl

theorem e2 : closeOK actC 3 (recT Conj3052.A2 6 128)
    (fun i k => fget (recT Conj3052.A2E 6 36 i) k 11) 1155 111 64 19 = true := by quickRfl

theorem t3 : treeOK actC 3 (fun _ => true) (akey sig3Arr) (recT Conj3052.A3 6 128)
    330 111 4 9 64 6 = true := by quickRfl

theorem e3 : closeOK actC 3 (recT Conj3052.A3 6 128)
    (fun i k => fget (recT Conj3052.A3E 6 28 i) k 9) 330 111 64 6 = true := by quickRfl

theorem orbits : certOK aconj gensP sig2Arr orbA2Cert = true ∧
    certOK aconj gensP sig3Arr orbA3Cert = true ∧ orbA2Cert.pts.size = 1155 ∧
    orbA3Cert.pts.size = 330 := by
  have h := kRoot
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨hr2, hr3⟩, hs⟩ := h
  have hg : ∀ k < gensP.size, PermArr gensP[k]! = true := by
    have h := kGen
    simp only [List.all_eq_true, List.mem_range] at h
    intro k hk
    exact h k (by omega)
  have hact : ∀ k < gensP.size, ∀ x, PermArr x = true → PermArr (aconj gensP[k]! x) = true :=
    fun k hk x hx => PermArr_aconj (hg k hk) hx
  have hcode : ∀ k < gensP.size, ∀ x, PermArr x = true → actC k (akey x) = akey (aconj gensP[k]! x) :=
    fun k hk x hx => aconjK_eq (hg k hk) hx
  have T2 := t2
  have E2 := e2
  have T3 := t3
  have E3 := e3
  rw [← hs] at T2 E2 T3 E3
  obtain ⟨a1, a2⟩ := bfsCert_tree (fuel := 2000) hact hcode hr2 (by norm_num) (by norm_num) T2 E2
  obtain ⟨b1, b2⟩ := bfsCert_tree (fuel := 1000) hact hcode hr3 (by norm_num) (by norm_num) T3 E3
  exact ⟨a1, b1, a2, b2⟩

end CertificateChecks.Batch3052

namespace Certificates

open CertificateChecks

open CFSG.Monster.B.TwoA.Census CFSG.Monster.B.TwoA in
theorem certificate3052 : (certOK aconj gensP sig2Arr orbA2Cert = true)
    ∧ (certOK aconj gensP sig3Arr orbA3Cert = true)
    ∧ (orbA2Cert.pts.size = 1155)
    ∧ (orbA3Cert.pts.size = 330) := CertificateChecks.Batch3052.orbits

end Certificates
