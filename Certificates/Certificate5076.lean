module

public import CFSG.GH74.GLS.C3.Prop121.Card7F1
import CFSG.Certificates.Kernel.PermCent.F7Conj
import CFSG.Certificates.Kernel.PermCent.F7CentSound
import Certificates.Kernel.Card7F.CentChecks
import Mathlib.Algebra.Order.Ring.Star

public section

open Subgroup Equiv Perm CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model
  CFSG.GH74.GLS.C3.Prop121.Card7 CFSG.GH74.GLS.C3.Prop121.Card7.FF CFSG.Certificates.Kernel.F7Conj
  CFSG.Certificates.Kernel.PkCV

namespace CertificateChecks.Batch5076

open Subgroup Equiv Perm CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model
  CFSG.GH74.GLS.C3.Prop121.Card7 CFSG.GH74.GLS.C3.Prop121.Card7.FF CFSG.Certificates.Kernel.F7Conj
  CFSG.Certificates.Kernel.PkCV

theorem d_cube : ∀ d : Perm (Fin 4), d * x4 = x4 * d → d ^ 3 = 1 → d = 1 := by
  decide

theorem snd_of_cube {f : F7} (h3 : f ^ 3 = 1) : (f : Amb 7).2 = 1 := by
  refine d_cube _ (comm_x4 f) ?_
  rw [← snd_pow, h3]
  rfl

theorem fst_cube {f : F7} (h3 : f ^ 3 = 1) : (f : Amb 7).1 ^ 3 = 1 := by
  rw [← fst_pow, h3]
  rfl

theorem ord3 : ∀ f ∈ F7L, f ^ 3 = 1 → f ≠ 1 → Ty3 f ∨ Ty33 f := by
  intro f _ h3 h1
  have hd := snd_of_cube h3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, -, hn⟩ := cycleType_of_pow_prime (fst_cube h3) (fst_ne_one h1 hd)
  have hle := numMoved_le (f : Amb 7).1
  unfold Ty3 Ty33
  have hk : k = 0 ∨ k = 1 := by omega
  rcases hk with rfl | rfl
  · exact Or.inl ⟨hd, h3, by omega⟩
  · exact Or.inr ⟨hd, h3, by omega⟩

theorem conj_of_numMoved {f g : F7} (hf : (f : Amb 7).2 = 1) (hg : (g : Amb 7).2 = 1)
    (hf3 : (f : Amb 7).1 ^ 3 = 1) (hg3 : (g : Amb 7).1 ^ 3 = 1) {j : ℕ} (hj : 0 < j)
    (hfn : numMoved (f : Amb 7).1 = 3 * j) (hgn : numMoved (g : Amb 7).1 = 3 * j) :
    ∃ k ∈ F7L, k * f * k⁻¹ = g := by
  obtain ⟨k, hk⟩ := exists_conj_of_cycleType hf hg
    ((cycleType_of_pow_three hf3 hfn hj).trans (cycleType_of_pow_three hg3 hgn hj).symm)
  exact ⟨k, mem_F7L k, hk⟩

theorem conj3 : ∀ f ∈ F7L, Ty3 f → ∃ k ∈ F7L, k * f * k⁻¹ = f0 := by
  rintro f _ ⟨hd, h3, hn⟩
  exact conj_of_numMoved hd rfl (fst_cube h3) (by decide) (j := 1) (by norm_num) hn (by decide)

theorem conj33 : ∀ f ∈ F7L, Ty33 f → ∃ k ∈ F7L, k * f * k⁻¹ = g0 := by
  rintro f _ ⟨hd, h3, hn⟩
  exact conj_of_numMoved hd rfl (fst_cube h3) (by decide) (j := 2) (by norm_num) hn (by decide)

theorem card_f0 : ccardB f0 f0 = 288 := by
  rw [ccardB_self f0 _ rfl]
  exact (of_decide_eq_true Certificates.Kernel.Card7F.cent_f0_g0).1

theorem card_g0 : ccardB g0 g0 = 72 := by
  rw [ccardB_self g0 _ rfl]
  exact (of_decide_eq_true Certificates.Kernel.Card7F.cent_f0_g0).2

theorem parity_eq {a b : ℕ} (h : ((-1 : ℤˣ) ^ a) = (-1) ^ b) : (Even a ↔ Even b) := by
  rcases Nat.even_or_odd a with ha | ha <;> rcases Nat.even_or_odd b with hb | hb
  · exact ⟨fun _ => hb, fun _ => ha⟩
  · rw [ha.neg_one_pow, hb.neg_one_pow] at h
    exact absurd h (by decide)
  · rw [ha.neg_one_pow, hb.neg_one_pow] at h
    exact absurd h (by decide)
  · exact ⟨fun h' => absurd h' (Nat.not_even_iff_odd.2 ha), fun h' => absurd h' (Nat.not_even_iff_odd.2 hb)⟩

theorem inv_nm : ∀ f ∈ F7L, IsInv f → nm7 (f : Amb 7) = 4 ∨ nm7 (f : Amb 7) = 8 := by
  rintro f _ ⟨h2, h1⟩
  have hr : (f : Amb 7).1 ^ 2 = 1 := by
    rw [← fst_pow, h2]
    rfl
  have hd : (f : Amb 7).2 ^ 2 = 1 := by
    rw [← snd_pow, h2]
    rfl
  obtain ⟨a, ha, hsa⟩ := numMoved_sign_of_sq hr
  obtain ⟨b, hb, hsb⟩ := numMoved_sign_of_sq hd
  have hpar := parity_eq (hsa.symm.trans ((sign_eq f).trans hsb))
  have hlr := numMoved_le (f : Amb 7).1
  have hld := numMoved_le (f : Amb 7).2
  have hne : a ≠ 0 ∨ b ≠ 0 := by
    by_contra hc
    push Not at hc
    apply h1
    apply Subtype.ext
    exact Prod.ext (eq_one_of_numMoved (by omega)) (eq_one_of_numMoved (by omega))
  unfold nm7
  rcases Nat.even_or_odd a with he | ho
  · obtain ⟨i, hi⟩ := he
    obtain ⟨j, hj⟩ := hpar.1 ⟨i, hi⟩
    omega
  · obtain ⟨i, hi⟩ := ho
    have hb' : ¬ Even b := fun h => Nat.not_even_iff_odd.2 ⟨i, hi⟩ (hpar.2 h)
    obtain ⟨j, hj⟩ := Nat.not_even_iff_odd.1 hb'
    omega

end CertificateChecks.Batch5076

namespace Certificates

open CertificateChecks

open CFSG in
open CFSG.GH74 in
open CFSG.GH74.GLS in
open CFSG.GH74.GLS.C3 in
open CFSG.GH74.GLS.C3.Prop121 in
open CFSG.GH74.GLS.C3.Prop121.Card7 in
open CFSG.GH74.GLS.C3.Prop121.Card7.FF in
open Subgroup Equiv Perm CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model in
theorem certificate5076 : (∀ f ∈ F7L, f ^ 3 = 1 → f ≠ 1 → Ty3 f ∨ Ty33 f)
    ∧ (∀ f ∈ F7L, Ty3 f → ∃ k ∈ F7L, k * f * k⁻¹ = f0)
    ∧ (ccardB f0 f0 = 288)
    ∧ (∀ f ∈ F7L, Ty33 f → ∃ k ∈ F7L, k * f * k⁻¹ = g0)
    ∧ (ccardB g0 g0 = 72)
    ∧ (∀ f ∈ F7L, IsInv f → nm7 (f : Amb 7) = 4 ∨ nm7 (f : Amb 7) = 8) :=
  ⟨CertificateChecks.Batch5076.ord3, CertificateChecks.Batch5076.conj3, CertificateChecks.Batch5076.card_f0, CertificateChecks.Batch5076.conj33, CertificateChecks.Batch5076.card_g0,
    CertificateChecks.Batch5076.inv_nm⟩

end Certificates
