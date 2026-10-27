module

public import CFSG.GH74.GLS.C3.Prop121.Card7F4Inputs
import CFSG.Certificates.Kernel.PermCent.F7Conj

public section

open Subgroup Equiv Perm CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model
  CFSG.GH74.GLS.C3.Prop121.Card7 CFSG.GH74.GLS.C3.Prop121.Card7.FF CFSG.Certificates.Kernel.F7Conj

namespace CertificateChecks.Batch5078

open Subgroup Equiv Perm CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model
  CFSG.GH74.GLS.C3.Prop121.Card7 CFSG.GH74.GLS.C3.Prop121.Card7.FF CFSG.Certificates.Kernel.F7Conj

theorem nm4 : ∀ f ∈ N4L, ¬ (ccardB f f ∣ 1152) := by
  intro f hf
  obtain ⟨⟨⟨hsq, -⟩, h4⟩, hd⟩ : XF f ∧ (f : Amb 7).2 ≠ 1 := of_decide_eq_true (List.mem_filter.1 hf).2
  have hr2 : (f : Amb 7).1 ^ 2 = 1 := by
    rw [← fst_pow, hsq]
    rfl
  have hn : numMoved (f : Amb 7).1 ≤ 2 := by
    have := two_le_numMoved hd
    unfold nm7 at h4
    omega
  obtain ⟨w, hw, hs, h5, hw1⟩ := exists_comm_five hr2 hn
  let W : F7 := ⟨(w, 1), by simp, by simp [hs]⟩
  have hWc : W ∈ centralizer ({f} : Set F7) := by
    rw [mem_centralizer_singleton_iff]
    apply Subtype.ext
    rw [val_mul, val_mul]
    exact Prod.ext hw (by simp [W])
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have ho : orderOf (⟨W, hWc⟩ : centralizer ({f} : Set F7)) = 5 := by
    refine orderOf_eq_prime ?_ ?_
    · apply Subtype.ext
      rw [Subgroup.coe_pow]
      apply Subtype.ext
      rw [val_pow]
      exact Prod.ext (by rw [Prod.pow_fst]; exact h5) (by simp [W])
    · intro h
      apply hw1
      exact congrArg (fun x : centralizer ({f} : Set F7) => ((x : F7) : Amb 7).1) h
  have h5d : 5 ∣ Nat.card (centralizer ({f} : Set F7)) := ho ▸ orderOf_dvd_natCard _
  have hc : Nat.card (centralizer ({f} : Set F7)) = ccardB f f := by
    rw [← ccard_eq_ccardB]
    unfold ccard
    refine Nat.card_congr (Equiv.subtypeEquivRight fun c => ?_)
    rw [mem_centralizer_singleton_iff, and_self]
  intro hdvd
  rw [← hc] at hdvd
  exact absurd (h5d.trans hdvd) (by norm_num)

theorem cycleType_u0 : (u0 : Amb 7).1.cycleType = Multiset.replicate 2 2 :=
  cycleType_of_even_inv (r := swap 0 1 * swap 2 3) (by decide) (by decide) (by simp [sign_mul])

theorem conj40 : ∀ f ∈ I40L, ∃ k ∈ F7L, k * f * k⁻¹ = u0 := by
  intro f hf
  obtain ⟨⟨hsq, hne⟩, h1⟩ : IsInv f ∧ (f : Amb 7).2 = 1 := of_decide_eq_true (List.mem_filter.1 hf).2
  have hr2 : (f : Amb 7).1 ^ 2 = 1 := by
    rw [← fst_pow, hsq]
    rfl
  have hs : sign (f : Amb 7).1 = 1 := by rw [sign_eq, h1, map_one]
  have hct := cycleType_of_even_inv hr2 (fst_ne_one hne h1) hs
  obtain ⟨k, hk⟩ := exists_conj_of_cycleType h1 rfl (hct.trans cycleType_u0.symm)
  exact ⟨k, mem_F7L k, hk⟩

end CertificateChecks.Batch5078

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
theorem certificate5078 : (∀ f ∈ N4L, ¬ (ccardB f f ∣ 1152))
    ∧ (∀ f ∈ I40L, ∃ k ∈ F7L, k * f * k⁻¹ = u0) := ⟨CertificateChecks.Batch5078.nm4, CertificateChecks.Batch5078.conj40⟩

end Certificates
