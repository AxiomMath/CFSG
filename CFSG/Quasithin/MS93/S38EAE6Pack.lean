module

public import CFSG.Permutation.FinPackWalk

public section

namespace CFSG.Quasithin.MS93.S38EAPack

open Equiv CFSG.Permutation.FinPack

theorem h16 : 6 ≤ 16 := by norm_num

theorem enc_one : enc (1 : Perm (Fin 6)) = 5517840 := by decide +kernel

@[expose] noncomputable def exLtK (f : ℕ → Bool) (m : ℕ) : Bool := !allLtK (fun j => !f j) m

theorem exLtK_iff {f : ℕ → Bool} {m : ℕ} : exLtK f m = true ↔ ∃ j < m, f j = true := by
  unfold exLtK
  constructor
  · intro h
    by_contra hc
    have ha : allLtK (fun j => !f j) m = true := allLtK_iff.2 fun j hj => by
      cases hf : f j
      · rfl
      · exact absurd ⟨j, hj, hf⟩ hc
    rw [ha] at h
    exact absurd h Bool.false_ne_true
  · rintro ⟨j, hj, hf⟩
    cases ha : allLtK (fun j => !f j) m
    · rfl
    · have h1 := allLtK_iff.1 ha j hj
      rw [hf] at h1
      exact absurd h1 Bool.false_ne_true

@[expose] def invCodes : List ℕ :=
  [4530960, 3298320, 2311440, 4534560, 5456160, 3428640, 4526640, 5379120, 2364720, 3232320,
    5317440, 2176320, 1262160, 1319760, 1193040, 4534785, 5456385, 3428865, 5513985, 5387265,
    2372865, 4534290, 5455890, 3428370, 5509170, 5320770, 1323090, 4522515, 5374995, 2360595,
    5505315, 5308995, 1311315, 3166740, 5251860, 2110740, 5255460, 5247540, 1061460, 213525,
    271125, 144405, 274725, 266805, 78405]

@[expose] noncomputable def qInv (c : ℕ) : Bool :=
  !(Nat.beq (mulK 6 c c) 5517840 && evenK 6 c && !Nat.beq c 5517840) || memK c invCodes

theorem qInv_walk : walkK 6 qInv 6 0 0 0 = true := by decide +kernel

theorem mem_invCodes {σ : Perm (Fin 6)} (h : σ * σ = 1 ∧ Perm.sign σ = 1 ∧ σ ≠ 1) :
    enc σ ∈ invCodes := by
  have hw := walkK_sound qInv_walk σ
  have h1 : Nat.beq (mulK 6 (enc σ) (enc σ)) 5517840 = true := by
    rw [← enc_mul h16, ← enc_one]
    exact (beq_enc_iff h16).2 h.1
  have h2 : evenK 6 (enc σ) = true := (sign_eq_one_iff_evenK h16 σ).1 h.2.1
  have h3 : Nat.beq (enc σ) 5517840 = false := by
    rw [← enc_one]
    exact beq_enc_false h16 h.2.2
  rw [qInv.eq_1, h1, h2, h3] at hw
  simp only [Bool.not_false, Bool.and_self, Bool.not_true, Bool.false_or] at hw
  exact memK_iff.1 hw

theorem rd_beq_iff (σ : Perm (Fin 6)) (i j : Fin 6) :
    Nat.beq (rd (enc σ) i) j = true ↔ σ i = j := by
  rw [rd_enc h16, Nat.beq_eq]
  exact Fin.val_inj

theorem rd_beq_false (σ : Perm (Fin 6)) (i j : Fin 6) :
    Nat.beq (rd (enc σ) i) j = false ↔ σ i ≠ j := by
  rw [ne_eq, ← rd_beq_iff, Bool.not_eq_true]

theorem beq_val_false (i j : Fin 6) : Nat.beq i j = false ↔ i ≠ j := by
  rw [ne_eq, ← Fin.val_inj, ← Nat.beq_eq, Bool.not_eq_true]

@[expose] noncomputable def qFix (c : ℕ) : Bool := exLtK (fun j => Nat.beq (rd c j) j) 6

theorem fix_check : allK qFix invCodes = true := by decide +kernel

theorem exists_fix {σ : Perm (Fin 6)} (h : σ * σ = 1 ∧ Perm.sign σ = 1 ∧ σ ≠ 1) :
    ∃ j, σ j = j := by
  obtain ⟨j, hj, hf⟩ := exLtK_iff.1 (allK_iff.1 fix_check _ (mem_invCodes h))
  exact ⟨⟨j, hj⟩, (rd_beq_iff σ ⟨j, hj⟩ ⟨j, hj⟩).1 hf⟩

@[expose] noncomputable def qTwo (c : ℕ) : Bool :=
  exLtK (fun i => exLtK (fun k => !Nat.beq (rd c i) i && !Nat.beq (rd c k) k && !Nat.beq k i &&
    !Nat.beq k (rd c i)) 6) 6

theorem two_check : allK qTwo invCodes = true := by decide +kernel

theorem exists_two_moved {σ : Perm (Fin 6)} (h : σ * σ = 1 ∧ Perm.sign σ = 1 ∧ σ ≠ 1) :
    ∃ i k, σ i ≠ i ∧ σ k ≠ k ∧ k ≠ i ∧ k ≠ σ i := by
  obtain ⟨i, hi, hf⟩ := exLtK_iff.1 (allK_iff.1 two_check _ (mem_invCodes h))
  obtain ⟨k, hk, hf⟩ := exLtK_iff.1 hf
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hf
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hf
  refine ⟨⟨i, hi⟩, ⟨k, hk⟩, (rd_beq_false σ ⟨i, hi⟩ ⟨i, hi⟩).1 h1,
    (rd_beq_false σ ⟨k, hk⟩ ⟨k, hk⟩).1 h2, (beq_val_false ⟨k, hk⟩ ⟨i, hi⟩).1 h3, ?_⟩
  have h4' : Nat.beq ((⟨k, hk⟩ : Fin 6) : ℕ) (σ ⟨i, hi⟩ : ℕ) = false := by
    rw [← rd_enc h16 σ ⟨i, hi⟩]
    exact h4
  exact (beq_val_false _ _).1 h4'

@[expose] noncomputable def qNe (a b : ℕ) : Bool :=
  Nat.beq a b || exLtK (fun i => !Nat.beq (rd b i) i && !Nat.beq (rd a i) (rd b i)) 6

theorem ne_check : allK (fun a => allK (fun b => qNe a b) invCodes) invCodes = true := by
  decide +kernel

theorem exists_ne {σ₁ σ₂ : Perm (Fin 6)} (h₁ : σ₁ * σ₁ = 1 ∧ Perm.sign σ₁ = 1 ∧ σ₁ ≠ 1)
    (h₂ : σ₂ * σ₂ = 1 ∧ Perm.sign σ₂ = 1 ∧ σ₂ ≠ 1) (hne : σ₁ ≠ σ₂) :
    ∃ i, σ₂ i ≠ i ∧ σ₁ i ≠ σ₂ i := by
  have hc := allK_iff.1 (allK_iff.1 ne_check _ (mem_invCodes h₁)) _ (mem_invCodes h₂)
  rw [qNe.eq_1, beq_enc_false h16 hne, Bool.false_or] at hc
  obtain ⟨i, hi, hf⟩ := exLtK_iff.1 hc
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hf
  obtain ⟨h1, h2⟩ := hf
  refine ⟨⟨i, hi⟩, (rd_beq_false σ₂ ⟨i, hi⟩ ⟨i, hi⟩).1 h1, fun e => ?_⟩
  have h3 : rd (enc σ₁) i = rd (enc σ₂) i := by
    rw [rd_enc h16 σ₁ ⟨i, hi⟩, rd_enc h16 σ₂ ⟨i, hi⟩, e]
  rw [h3, Nat.beq_refl] at h2
  exact absurd h2 (by decide)

end CFSG.Quasithin.MS93.S38EAPack
