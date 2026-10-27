module

public import CFSG.Permutation.FinPackCount

public section

namespace CFSG.Permutation.FinPack

open Equiv

variable {n : ℕ}

theorem enc_mem_of_beq {L : List (Perm (Fin n))} {C : List ℕ} (hL : (L.map enc == C) = true)
    {x : Perm (Fin n)} (hx : x ∈ L) : enc x ∈ C := by
  rw [beq_iff_eq] at hL
  rw [← hL]
  exact List.mem_map.2 ⟨x, hx, rfl⟩

theorem mem_of_memKL (hn : n ≤ 16) {L : List (Perm (Fin n))} {C : List ℕ}
    (hL : (L.map enc == C) = true) {x : Perm (Fin n)} (h : memK (enc x) C = true) : x ∈ L := by
  rw [beq_iff_eq] at hL
  subst hL
  exact (mem_iff_enc hn L x).2 (memK_iff.1 h)

@[expose] noncomputable def mulInK (n : ℕ) (C D : List ℕ) : Bool :=
  allK (fun a => allK (fun b => memK (mulK n a b) C) D) C

theorem mul_mem_of_K (hn : n ≤ 16) (L S : List (Perm (Fin n))) (C D : List ℕ)
    (hL : (L.map enc == C) = true) (hS : (S.map enc == D) = true) (h : mulInK n C D = true) :
    ∀ x ∈ L, ∀ s ∈ S, x * s ∈ L := by
  intro x hx s hs
  have h1 := allK_iff.1 (allK_iff.1 h _ (enc_mem_of_beq hL hx)) _ (enc_mem_of_beq hS hs)
  rw [← enc_mul hn] at h1
  exact mem_of_memKL hn hL h1

@[expose] noncomputable def sqKL (n e : ℕ) (D : List ℕ) : Bool :=
  allK (fun a => Nat.beq (mulK n a a) e) D

theorem sq_of_KL (hn : n ≤ 16) (S : List (Perm (Fin n))) (D : List ℕ) (e : ℕ)
    (hS : (S.map enc == D) = true) (he : enc (1 : Perm (Fin n)) = e) (h : sqKL n e D = true) :
    ∀ s ∈ S, s * s = 1 := by
  intro s hs
  have h1 := allK_iff.1 h _ (enc_mem_of_beq hS hs)
  rw [← enc_mul hn, ← he, Nat.beq_eq] at h1
  exact enc_inj hn h1

@[expose] noncomputable def conjInK (n : ℕ) (D C : List ℕ) : Bool :=
  allK (fun g => allK (fun r => memK (mulK n (mulK n g r) g) C) C) D

theorem conj_mem_of_K (hn : n ≤ 16) (S R : List (Perm (Fin n))) (D C : List ℕ)
    (hS : (S.map enc == D) = true) (hR : (R.map enc == C) = true) (h : conjInK n D C = true) :
    ∀ g ∈ S, ∀ r ∈ R, g * r * g ∈ R := by
  intro g hg r hr
  have h1 := allK_iff.1 (allK_iff.1 h _ (enc_mem_of_beq hS hg)) _ (enc_mem_of_beq hR hr)
  rw [← enc_mul hn, ← enc_mul hn] at h1
  exact mem_of_memKL hn hR h1

@[expose] noncomputable def subKL (A B : List ℕ) : Bool := allK (fun a => memK a B) A

theorem sub_of_KL (hn : n ≤ 16) (L M : List (Perm (Fin n))) (A B : List ℕ)
    (hL : (L.map enc == A) = true) (hM : (M.map enc == B) = true) (h : subKL A B = true) :
    ∀ x ∈ L, x ∈ M :=
  fun _ hx => mem_of_memKL hn hM (allK_iff.1 h _ (enc_mem_of_beq hL hx))

@[expose] noncomputable def interK (A B D : List ℕ) : Bool :=
  allK (fun a => !memK a B || memK a D) A

theorem inter_of_K (hn : n ≤ 16) (L M N : List (Perm (Fin n))) (A B D : List ℕ)
    (hL : (L.map enc == A) = true) (hM : (M.map enc == B) = true) (hN : (N.map enc == D) = true)
    (h : interK A B D = true) : ∀ x ∈ L, x ∈ M → x ∈ N := by
  intro x hx hxM
  have h1 := allK_iff.1 h _ (enc_mem_of_beq hL hx)
  rw [memK_iff.2 (enc_mem_of_beq hM hxM), Bool.not_true, Bool.false_or] at h1
  exact mem_of_memKL hn hN h1

@[expose] noncomputable def permValidK (n d : ℕ) : Bool :=
  Nat.beq (encF (rd d) n) d && allLtK (fun i => Nat.blt (rd d i) n) n &&
    allLtK (fun i => allLtK (fun j => !Nat.beq (rd d i) (rd d j) || Nat.beq i j) n) n

theorem exists_enc_of_permValidK {d : ℕ} (h : permValidK n d = true) : ∃ σ : Perm (Fin n), enc σ = d := by
  simp only [permValidK, Bool.and_eq_true] at h
  obtain ⟨⟨he, hp⟩, hi⟩ := h
  have hp' : ∀ i < n, rd d i < n := by
    intro i h1
    have h2 := allLtK_iff.1 hp i h1
    rwa [Nat.blt_eq] at h2
  have hi' : ∀ i < n, ∀ j < n, rd d i = rd d j → i = j := by
    intro i h1 j h2 e
    have h3 := allLtK_iff.1 (allLtK_iff.1 hi i h1) j h2
    rw [e, Nat.beq_refl, Bool.not_true, Bool.false_or, Nat.beq_eq] at h3
    exact h3
  refine ⟨ofVals (rd d) hp' hi', ?_⟩
  have h4 : encF (valF (ofVals (rd d) hp' hi')) n = encF (rd d) n :=
    encF_congr fun i h1 => valF_ofVals _ hp' hi' h1
  change encF (valF (ofVals (rd d) hp' hi')) n = d
  rw [h4]
  exact Nat.eq_of_beq_eq_true he

end CFSG.Permutation.FinPack
