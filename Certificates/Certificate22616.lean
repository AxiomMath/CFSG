module

public import Certificates.Kernel.Sporadic.SuzInv.C22616
public import CFSG.Certificates.Kernel.SporSch.SporXElemSound
public import CFSG.Sporadic.SuzOddCore.FourCentralizers

public section

namespace CertificateChecks.Batch22616

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporXE CFSG.KS.SporSch CFSG.KD.SuzInv.C22616
open CFSG.Sporadic.SuzOddCore CFSG.Sporadic.Schreier CFSG.Certificates CertificateChecks.KernelSpor
open Subgroup

theorem mem_ptsL : ∀ {n x : Nat}, x < n → x ∈ ptsL n
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, x, h => by
    change x ∈ n :: ptsL n
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with h | rfl
    · exact List.mem_cons_of_mem _ (mem_ptsL h)
    · exact List.mem_cons_self

theorem lt_of_mem_ptsL : ∀ {n x : Nat}, x ∈ ptsL n → x < n
  | 0, _, h => absurd h List.not_mem_nil
  | n + 1, x, h => by
    change x ∈ n :: ptsL n at h
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.lt_succ_self _
    · exact Nat.lt_succ_of_lt (lt_of_mem_ptsL h)

theorem faithT : BaseFaithful (⊤ : Subgroup (Equiv.Perm (Fin 1782))) (ptsL 1782) :=
  fun _ _ hfix => Equiv.ext fun x => hfix x (mem_ptsL x.2)

theorem upk_get {P x : Nat} (hx : x < 1782) : (unpack 1782 11 P)[x]! = pg 11 (mask 11) P x := by
  rw [unpack, getElem!_pos _ x (by simpa using hx), Array.getElem_ofFn]

@[expose] noncomputable def gE (i l : ℕ) : Equiv.Perm (Fin 1782) :=
  if h : l < (invInnerChain i).originalCount then (invInnerChain i).original.get ⟨l, h⟩ else 1

theorem gE_mem (i l : ℕ) : gE i l ∈ invE i := by
  rw [invE, RawSchreierDatum.originalSubgroup, gE]
  split_ifs with h
  · exact subset_closure (schreier_vector_get_mem_toList _ _)
  · exact one_mem _

theorem row {i : Nat} (hi : i < 4) {F : Nat → Nat} {s nl : Nat} (hs : invInnerStart i = s)
    (hnl : invInnerGenCounts.getD i 0 = nl) (hrun : ∀ k < s + nl, invRun i k = unpack 1782 11 (F k))
    {words : List (List Nat × Nat)} (hck : ckE (ptsL 1782) (lE F s) nl words = true) :
    ∃ E : Subgroup (Equiv.Perm (Fin 1782)), E ≤ suzM ⊓ centralizer {suzInv i} ∧
      (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) ∧ (∀ a ∈ E, a ^ 2 = 1) ∧
      2 ^ words.length ≤ Nat.card E := by
  have hc := invInnerChain_arrays hi
  have hL : ∀ l < nl, RepF 1782 (lE F s l) (gE i l) := by
    intro l hl x hx
    have hl' : l < (invInnerGenArrs i).size := by
      rw [invInnerGenArrs, Array.size_ofFn, hnl]
      exact hl
    have hlc : l < (invInnerChain i).originalCount := hc.orig_size ▸ hl'
    have hr := hc.orig ⟨l, hlc⟩
    change CFSG.Monster.B.Co2.Rep 1782 (invInnerGenArrs i)[l]! _ at hr
    rw [invInnerGenArrs_get hl', hs, hrun (s + l) (by omega)] at hr
    change pg 11 (mask 11) (F (s + l)) x = _
    rw [gE, dif_pos hlc, ← upk_get hx]
    exact hr ⟨x, hx⟩
  obtain ⟨E, hE, hcm, hsq, hcard⟩ := elem_of_ckE faithT (fun _ h => lt_of_mem_ptsL h) le_top hL
    (fun l _ => gE_mem i l) hck
  refine ⟨E, ?_, hcm, hsq, hcard⟩
  refine (hE.trans (invE_le_centM hi)).trans ?_
  rw [centM, inf_comm]

theorem elem_all : ∀ i < 4, ∃ E : Subgroup (Equiv.Perm (Fin 1782)),
    E ≤ suzM ⊓ centralizer {suzInv i} ∧ (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) ∧
    (∀ a ∈ E, a ^ 2 = 1) ∧ (suzInv i ∈ suzM → 2 ^ 4 ≤ Nat.card E) ∧ 2 ^ 3 ≤ Nat.card E := by
  intro i hi
  obtain ⟨-, -, -, h2, h3, -⟩ := invT_check
  interval_cases i
  · obtain ⟨E, hE, hc, hs, hcard⟩ := row (i := 0) (s := 32) (nl := 22) (by norm_num) rfl rfl
      (fun _ hk => CertificateChecks.KernelSpor.SuzInv.run_eq0 (by omega)) ck0
    have hl : w0.length = 4 := rfl
    rw [hl] at hcard
    exact ⟨E, hE, hc, hs, fun _ => hcard, le_trans (by norm_num) hcard⟩
  · obtain ⟨E, hE, hc, hs, hcard⟩ := row (i := 1) (s := 18) (nl := 10) (by norm_num) rfl rfl
      (fun _ hk => CertificateChecks.KernelSpor.SuzInv.run_eq1 (by omega)) ck1
    have hl : w1.length = 4 := rfl
    rw [hl] at hcard
    exact ⟨E, hE, hc, hs, fun _ => hcard, le_trans (by norm_num) hcard⟩
  · obtain ⟨E, hE, hc, hs, hcard⟩ := row (i := 2) (s := 12) (nl := 2) (by norm_num) rfl rfl
      (fun _ hk => CertificateChecks.KernelSpor.SuzInv.run_eq2 (by omega)) ck2
    have hl : w2.length = 3 := rfl
    rw [hl] at hcard
    refine ⟨E, hE, hc, hs, fun hM => ?_, hcard⟩
    rw [suzInv_mem_iff_inM (by norm_num), h2] at hM
    exact absurd hM Bool.false_ne_true
  · obtain ⟨E, hE, hc, hs, hcard⟩ := row (i := 3) (s := 20) (nl := 5) (by norm_num) rfl rfl
      (fun _ hk => CertificateChecks.KernelSpor.SuzInv.run_eq3 (by omega)) ck3
    have hl : w3.length = 3 := rfl
    rw [hl] at hcard
    refine ⟨E, hE, hc, hs, fun hM => ?_, hcard⟩
    rw [suzInv_mem_iff_inM (by norm_num), h3] at hM
    exact absurd hM Bool.false_ne_true

end CertificateChecks.Batch22616

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.SuzOddCore Subgroup in
theorem certificate22616 : ∀ i < 4, ∃ E : Subgroup (Equiv.Perm (Fin 1782)), E ≤ suzM ⊓ centralizer {suzInv i} ∧
    (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) ∧ (∀ a ∈ E, a ^ 2 = 1) ∧
    (suzInv i ∈ suzM → 2 ^ 4 ≤ Nat.card E) ∧ 2 ^ 3 ≤ Nat.card E := CertificateChecks.Batch22616.elem_all

end Certificates
