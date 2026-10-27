module

public import Mathlib.GroupTheory.Perm.Cycle.Type
public import CFSG.Monster.B.Co2.PermArr

public noncomputable section

namespace CFSG.Sporadic.HeldB

open Finset CFSG.Monster.B.Co2

variable {n : ℕ}

@[expose] def fixCard (x : Equiv.Perm (Fin n)) : ℕ := (univ.filter fun q => x q = q).card

theorem countP_range_eq_card (p : ℕ → Bool) :
    (List.range n).countP p = ((Finset.range n).filter fun i => p i = true).card := by
  rw [Finset.card_filter]
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [List.range_succ, List.countP_append, ih, Finset.sum_range_succ]
    simp [List.countP_cons]

theorem fixCard_eq_countP {t : Array ℕ} {x : Equiv.Perm (Fin n)} (h : Rep n t x) :
    fixCard x = (List.range n).countP (fun i => t[i]! == i) := by
  rw [countP_range_eq_card, fixCard, ← Finset.card_map Fin.valEmbedding]
  congr 1
  ext i
  simp only [mem_map, mem_filter, mem_univ, true_and, Fin.valEmbedding_apply, mem_range,
    beq_iff_eq]
  constructor
  · rintro ⟨q, hq, rfl⟩
    refine ⟨q.2, ?_⟩
    rw [h q, hq]
  · rintro ⟨hi, hti⟩
    refine ⟨⟨i, hi⟩, Fin.ext ?_, rfl⟩
    rw [← h ⟨i, hi⟩]
    exact hti

theorem inv_apply_self_perm {α : Type*} (f : Equiv.Perm α) (x : α) : f⁻¹ (f x) = x :=
  f.symm_apply_apply x

theorem apply_inv_self_perm {α : Type*} (f : Equiv.Perm α) (x : α) : f (f⁻¹ x) = x :=
  f.apply_symm_apply x

theorem fixCard_conj (c x : Equiv.Perm (Fin n)) : fixCard (c * x * c⁻¹) = fixCard x := by
  unfold fixCard
  refine Finset.card_nbij' (fun q => c⁻¹ q) (fun q => c q) (fun q hq => ?_) (fun q hq => ?_)
    (fun q _ => ?_) (fun q _ => ?_)
  · rw [Finset.mem_coe, Finset.mem_filter] at hq ⊢
    refine ⟨mem_univ _, ?_⟩
    have h := congrArg (⇑c⁻¹) hq.2
    rwa [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, inv_apply_self_perm] at h
  · rw [Finset.mem_coe, Finset.mem_filter] at hq ⊢
    refine ⟨mem_univ _, ?_⟩
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, inv_apply_self_perm, hq.2]
  · exact apply_inv_self_perm c q
  · exact inv_apply_self_perm c q

theorem card_fixedPoints_eq (x : Equiv.Perm (Fin n)) :
    Fintype.card (Function.fixedPoints x) = fixCard x := by
  rw [fixCard, ← Fintype.card_subtype]
  rfl

theorem exists_fix_of_sign (hn : n % 4 = 2) {x : Equiv.Perm (Fin n)} (h2 : x ^ 2 = 1)
    (hs : Equiv.Perm.sign x = 1) : ∃ q, x q = q := by
  by_contra hne
  push Not at hne
  have h0 : fixCard x = 0 := by
    rw [fixCard, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    exact fun q _ => hne q
  have hsign := Equiv.Perm.sign_of_pow_two_eq_one h2
  rw [card_fixedPoints_eq, h0, Fintype.card_fin, Nat.sub_zero, hs] at hsign
  have hodd : Odd (n / 2) := by
    rw [Nat.odd_iff]
    omega
  rw [hodd.neg_one_pow] at hsign
  exact absurd hsign (by decide)

theorem sum_fixCard_eq {G : Subgroup (Equiv.Perm (Fin n))} (b : Fin n)
    (htrans : ∀ q : Fin n, ∃ h ∈ G, h b = q) (X : Finset (Equiv.Perm (Fin n)))
    (hX : ∀ x ∈ X, ∀ h ∈ G, h * x * h⁻¹ ∈ X) :
    ∑ x ∈ X, fixCard x = n * (X.filter fun x => x b = b).card := by
  classical
  have key : ∀ q : Fin n,
      (X.filter fun x => x q = q).card = (X.filter fun x => x b = b).card := by
    intro q
    obtain ⟨h, hG, hq⟩ := htrans q
    refine Finset.card_nbij' (fun x => h⁻¹ * x * h) (fun x => h * x * h⁻¹) (fun x hx => ?_)
      (fun x hx => ?_) (fun x _ => ?_) (fun x _ => ?_)
    · rw [Finset.mem_coe, Finset.mem_filter] at hx ⊢
      refine ⟨?_, ?_⟩
      · have := hX x hx.1 h⁻¹ (G.inv_mem hG)
        rwa [inv_inv] at this
      · rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hq, hx.2, ← hq, inv_apply_self_perm]
    · rw [Finset.mem_coe, Finset.mem_filter] at hx ⊢
      refine ⟨hX x hx.1 h hG, ?_⟩
      rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ← hq, inv_apply_self_perm, hx.2]
    · group
    · group
  calc ∑ x ∈ X, fixCard x = ∑ x ∈ X, ∑ q : Fin n, if x q = q then 1 else 0 := by
        simp only [fixCard, Finset.card_filter]
    _ = ∑ q : Fin n, ∑ x ∈ X, if x q = q then 1 else 0 := Finset.sum_comm
    _ = ∑ q : Fin n, (X.filter fun x => x q = q).card := by simp only [Finset.card_filter]
    _ = ∑ _q : Fin n, (X.filter fun x => x b = b).card := Finset.sum_congr rfl fun q _ => key q
    _ = n * (X.filter fun x => x b = b).card := by simp

end CFSG.Sporadic.HeldB
