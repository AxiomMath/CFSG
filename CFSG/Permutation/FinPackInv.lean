module

public import CFSG.Permutation.FinPackCount

public section

namespace CFSG.Permutation.FinPack

open Equiv Finset

variable {n : ℕ}

theorem encF_eq_sum (a : ℕ → ℕ) (k : ℕ) : encF a k = ∑ i ∈ range k, a i * 16 ^ i := by
  induction k with
  | zero => rfl
  | succ k ih => rw [encF_succ, ih, Finset.sum_range_succ]

@[expose] noncomputable def invCK (n c : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0 (fun i acc => Nat.add acc (Nat.shiftLeft i (Nat.mul 4 (rd c i)))) n

theorem invCK_eq_sum (n c : ℕ) : invCK n c = ∑ i ∈ range n, i * 16 ^ rd c i := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [Finset.sum_range_succ, ← ih]
    change invCK k c + k <<< (4 * rd c k) = _
    rw [Nat.shiftLeft_eq, pow_mul]
    norm_num

theorem enc_inv_invCK (hn : n ≤ 16) (σ : Perm (Fin n)) : enc σ⁻¹ = invCK n (enc σ) := by
  rw [invCK_eq_sum, enc, encF_eq_sum,
    ← Fin.sum_univ_eq_sum_range (fun i => i * 16 ^ rd (enc σ) i) n,
    ← Fin.sum_univ_eq_sum_range
      (fun i => (if h : i < n then ((σ⁻¹ ⟨i, h⟩ : Fin n) : ℕ) else 0) * 16 ^ i) n,
    ← Equiv.sum_comp σ]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [dif_pos (σ i).isLt, rd_enc hn σ i]
  simp

@[expose] def decK (n c : ℕ) (i : Fin n) : Fin n := ⟨rd c i % n, Nat.mod_lt _ i.pos⟩

theorem decK_enc (hn : n ≤ 16) (σ : Perm (Fin n)) : decK n (enc σ) = ⇑σ := by
  funext i
  apply Fin.ext
  change rd (enc σ) i % n = _
  rw [rd_enc hn σ i, Nat.mod_eq_of_lt (Fin.isLt _)]

theorem card_filter_of_iff (p : Perm (Fin n) → Prop) [DecidablePred p] (Q : ℕ → Bool)
    (h : ∀ σ, p σ ↔ Q (enc σ) = true) : (univ.filter p).card = cntK n Q n 0 0 0 := by
  rw [← card_filter_eq_cntK]
  exact congrArg Finset.card (Finset.filter_congr fun σ _ => h σ)

theorem mem_iff_count (hn : n ≤ 16) (p : Perm (Fin n) → Prop) [DecidablePred p]
    (P : (Fin n → Fin n) → Bool) (hP : ∀ σ : Perm (Fin n), p σ ↔ P ⇑σ = true) (L : List ℕ)
    (hL : allK (fun c => P (decK n c)) L = true)
    (hcard : (univ.filter p).card ≤ cntK n (fun c => memK c L) n 0 0 0) :
    ∀ σ : Perm (Fin n), p σ ↔ memK (enc σ) L = true := by
  have hsub : ∀ σ : Perm (Fin n), memK (enc σ) L = true → p σ := fun σ h => by
    have h1 := allK_iff.1 hL _ (memK_iff.1 h)
    rw [decK_enc hn] at h1
    exact (hP σ).2 h1
  rw [← card_filter_eq_cntK] at hcard
  have hs : (univ.filter fun σ : Perm (Fin n) => memK (enc σ) L = true) ⊆ univ.filter p := by
    intro σ hσ
    rw [Finset.mem_filter] at hσ ⊢
    exact ⟨hσ.1, hsub σ hσ.2⟩
  have heq := Finset.eq_of_subset_of_card_le hs hcard
  intro σ
  refine ⟨fun h => ?_, hsub σ⟩
  have h1 : σ ∈ univ.filter p := Finset.mem_filter.2 ⟨Finset.mem_univ σ, h⟩
  rw [← heq, Finset.mem_filter] at h1
  exact h1.2

end CFSG.Permutation.FinPack
