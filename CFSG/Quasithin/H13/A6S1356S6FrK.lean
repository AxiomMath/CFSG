module

public import CFSG.Permutation.FinPackPow

public section

namespace CFSG.Quasithin.H13.A6S1356K

open Equiv Equiv.Perm CFSG.Permutation.FinPack

theorem h16 : 6 ≤ 16 := by norm_num

@[expose] noncomputable def q4 (c : ℕ) : Bool :=
  !Nat.beq (powK 6 5517840 c 16) 5517840 || Nat.beq (powK 6 5517840 c 4) 5517840

theorem q4_walk : walkK 6 q4 6 0 0 0 = true := by decide +kernel

theorem pow_iff (he : enc (1 : Perm (Fin 6)) = 5517840) (σ : Perm (Fin 6)) (k : ℕ) :
    σ ^ k = 1 ↔ Nat.beq (powK 6 5517840 (enc σ) k) 5517840 = true := by
  rw [← enc_pow h16 he, ← he, beq_enc_iff h16]

theorem pow4_K (he : enc (1 : Perm (Fin 6)) = 5517840) :
    ∀ σ : Perm (Fin 6), σ ^ 16 = 1 → σ ^ 4 = 1 := by
  intro σ h
  have hw := walkK_sound q4_walk σ
  rw [q4.eq_1, (pow_iff he σ 16).1 h] at hw
  simp only [Bool.not_true, Bool.false_or] at hw
  exact (pow_iff he σ 4).2 hw

@[expose] noncomputable def fpfK (c : ℕ) : Bool :=
  allLtK (fun i => !Nat.beq (rd c i) i) 6

theorem fpfK_iff (σ : Perm (Fin 6)) : (∀ i, σ i ≠ i) ↔ fpfK (enc σ) = true := by
  rw [fpfK, allLtK_iff]
  constructor
  · intro H j hj
    have e : Nat.beq (rd (enc σ) j) j = true ↔ σ ⟨j, hj⟩ = ⟨j, hj⟩ := beq_rd_iff h16 σ ⟨j, hj⟩
    rw [Bool.not_eq_true', Bool.eq_false_iff]
    exact fun h' => H ⟨j, hj⟩ (e.1 h')
  · intro H i hi
    have h' := H i i.isLt
    rw [Bool.not_eq_true', (beq_rd_iff h16 σ i).2 hi] at h'
    cases h'

@[expose] noncomputable def qT (s t : ℕ) : Bool :=
  !Nat.beq (powK 6 5517840 t 4) 5517840 || !evenK 6 t ||
    !Nat.beq (mulK 6 s t) (mulK 6 t s) || Nat.beq t 5517840

@[expose] noncomputable def qF (s : ℕ) : Bool :=
  !(Nat.beq (powK 6 5517840 s 3) 5517840 && fpfK s) || walkK 6 (qT s) 6 0 0 0

theorem qF_walk : walkK 6 qF 6 0 0 0 = true := by decide +kernel

theorem comm_fpf3_K (he : enc (1 : Perm (Fin 6)) = 5517840) : ∀ σ : Perm (Fin 6),
    σ ^ 3 = 1 → (∀ i, σ i ≠ i) → ∀ τ : Perm (Fin 6), τ ^ 4 = 1 → sign τ = 1 →
      σ * τ = τ * σ → τ = 1 := by
  intro σ h3 hf τ h4 hs hc
  have hw := walkK_sound qF_walk σ
  rw [qF.eq_1, (pow_iff he σ 3).1 h3, (fpfK_iff σ).1 hf] at hw
  simp only [Bool.and_true, Bool.not_true, Bool.false_or] at hw
  have ht := walkK_sound hw τ
  rw [qT.eq_1, (pow_iff he τ 4).1 h4, (sign_eq_one_iff_evenK h16 τ).1 hs,
    (comm_enc_iff h16).2 hc] at ht
  simp only [Bool.not_true, Bool.false_or] at ht
  rw [← he] at ht
  exact (beq_enc_iff h16).1 ht

end CFSG.Quasithin.H13.A6S1356K
