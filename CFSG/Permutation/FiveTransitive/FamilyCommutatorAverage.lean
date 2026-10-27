module

public import CFSG.Permutation.FiveTransitive.RefinedCommutatorSupport
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG

namespace FiveTransitive.FamilyCommutatorAverage

open Equiv
open scoped BigOperators

theorem sum_card_filter {T X : Type*} [Fintype T] [Fintype X]
    (s : Finset X) (p : T → X → Prop) [∀ t x, Decidable (p t x)] :
    (∑ t : T, (s.filter (p t)).card) = ∑ x ∈ s, Nat.card {t : T // p t x} := by
  classical
  simp only [Finset.card_filter, Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [Finset.sum_comm]

private theorem sum_card_filter_mul_le {T X : Type*} [Fintype T] [Fintype X]
    (s : Finset X) (p : T → X → Prop) [∀ t x, Decidable (p t x)] (d c : ℕ)
    (hc : ∀ x ∈ s, Nat.card {t : T // p t x} * d ≤ c) :
    (∑ t : T, (s.filter (p t)).card) * d ≤ s.card * c := by
  rw [sum_card_filter, Finset.sum_mul]
  calc
    _ ≤ ∑ x ∈ s, c := Finset.sum_le_sum hc
    _ = _ := by simp

private theorem card_image_mem_eq_sum {T X : Type*} [Fintype T] [Fintype X] [DecidableEq X]
    (f : T → X) (s : Finset X) :
    Nat.card {t : T // f t ∈ s} = ∑ x ∈ s, Nat.card {t : T // f t = x} := by
  classical
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact (Finset.sum_card_fiberwise_eq_card_filter Finset.univ s f).symm

theorem refined_sum_inequality
    {T X : Type*} [Fintype T] [Nonempty T] [Fintype X] [DecidableEq X]
    (g : Perm X) (α : X) (hα : α ∈ g.support) (v : T → Perm X)
    (hfix : ∀ t, v t α = α) (hmove : ∀ t, v t (g α) ≠ g α)
    (hmoved : ∀ γ, γ ≠ α → γ ≠ g α →
      Nat.card {t : T // v t γ ≠ γ} * (Fintype.card X - 2) =
        Nat.card T * (g.support.card - 1))
    (hbeta : ∀ γ, γ ≠ α → γ ≠ g α →
      Nat.card {t : T // v t γ = g α} * (Fintype.card X - 2) = Nat.card T)
    (hpair : ∀ γ δ, γ ≠ α → γ ≠ g α → δ ≠ α → δ ≠ g α → γ ≠ δ →
      Nat.card {t : T // v t γ = δ} * (Fintype.card X - 2) * (Fintype.card X - 3) =
        Nat.card T * (g.support.card - 2))
    (hfixed : ∀ γ δ, γ ≠ α → γ ≠ g α → δ ≠ α → δ ≠ g α → γ ≠ δ →
      Nat.card {t : T // v t γ = γ ∧ v t δ ≠ δ} *
          (Fintype.card X - 2) * (Fintype.card X - 3) =
        Nat.card T * ((Fintype.card X - g.support.card - 1) * (g.support.card - 1)))
    (hpoint : ∀ t, g.support.card ≤ (g.support ∩ (v t).support).card +
      (RefinedCommutatorSupport.outsideEntry g (v t)).card +
      (RefinedCommutatorSupport.fixedMovedImage g (v t)).card) :
    let n := Fintype.card X
    let m := g.support.card
    m * (n - 2) * (n - 3) ≤
      2 * (n - 2) * (n - 3) + (m - 2) * (m - 1) * (n - 3) +
      (n - m) * (m - 2)^2 + (n - m) * (n - 3) +
      (m - 2) * (n - m - 1) * (m - 1) := by
  classical
  let n := Fintype.card X
  let m := g.support.card
  let q := Nat.card T
  let β := g α
  let A := (g.support.erase α).erase β
  let O := g.supportᶜ
  have hαβ : α ≠ β := (Perm.mem_support.mp hα).symm
  have hβ : β ∈ g.support := Perm.apply_mem_support.mpr hα
  have hβerase : β ∈ g.support.erase α := Finset.mem_erase.mpr ⟨hαβ.symm, hβ⟩
  have hA : A.card = m - 2 := by
    simp only [A, Finset.card_erase_of_mem hβerase, Finset.card_erase_of_mem hα, m]
    omega
  have hO : O.card = n - m := Finset.card_compl _
  have hApart : ∀ γ ∈ A, γ ∈ g.support ∧ γ ≠ α ∧ γ ≠ β := by
    intro γ hγ
    simp only [A, Finset.mem_erase] at hγ
    exact ⟨hγ.2.2, hγ.2.1, hγ.1⟩
  have hOpart : ∀ γ ∈ O, γ ∉ g.support ∧ γ ≠ α ∧ γ ≠ β := by
    intro γ hγ
    have hg : γ ∉ g.support := Finset.mem_compl.mp hγ
    exact ⟨hg, fun he => hg (he ▸ hα), fun he => hg (he ▸ hβ)⟩
  have hpartition : g.support = insert α (insert β A) := by
    rw [Finset.insert_erase hβerase, Finset.insert_erase hα]
  have hαA : α ∉ A := by simp [A]
  have hβA : β ∉ A := by simp [A]
  have hIfilter (t : T) : (g.support ∩ (v t).support).card =
      1 + (A.filter (fun γ => v t γ ≠ γ)).card := by
    have heq : g.support ∩ (v t).support =
        insert β (A.filter (fun γ => v t γ ≠ γ)) := by
      ext γ
      rw [hpartition]
      simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_filter, Perm.mem_support]
      constructor
      · rintro ⟨hγ | hγ | hγ, hm⟩
        · subst γ
          exact (hm (hfix t)).elim
        · exact Or.inl hγ
        · exact Or.inr ⟨hγ, hm⟩
      · rintro (rfl | ⟨hγ, hm⟩)
        · exact ⟨Or.inr (Or.inl rfl), hmove t⟩
        · exact ⟨Or.inr (Or.inr hγ), hm⟩
    rw [heq, Finset.card_insert_of_notMem (fun h => hβA (Finset.mem_filter.mp h).1)]
    omega
  have hIsum : (∑ t : T, (g.support ∩ (v t).support).card) * (n - 2) ≤
      q * (n - 2) + (m - 2) * (q * (m - 1)) := by
    have hbound := sum_card_filter_mul_le A (fun t γ => v t γ ≠ γ) (n - 2)
      (q * (m - 1)) (fun γ hγ => (hmoved γ (hApart γ hγ).2.1 (hApart γ hγ).2.2).le)
    simp only [hIfilter, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      smul_eq_mul, mul_one] at ⊢
    rw [hA] at hbound
    rw [add_mul, ← Nat.card_eq_fintype_card]
    exact Nat.add_le_add_left hbound _
  have hBsum : (∑ t : T, (RefinedCommutatorSupport.outsideEntry g (v t)).card) *
      ((n - 2) * (n - 3)) ≤
      (n - m) * (q * (n - 3) + (m - 2) * (q * (m - 2))) := by
    have hB (t : T) : RefinedCommutatorSupport.outsideEntry g (v t) =
        O.filter (fun γ => v t γ ∈ g.support) := by
      ext γ
      simp only [RefinedCommutatorSupport.mem_outsideEntry, Finset.mem_filter,
        O, Finset.mem_compl]
    simp only [hB]
    rw [← hO]
    apply sum_card_filter_mul_le
    intro γ hγ
    have hp := hOpart γ hγ
    rw [card_image_mem_eq_sum]
    rw [hpartition, Finset.sum_insert (by simp [hαβ, hαA]), Finset.sum_insert hβA]
    have hz : Nat.card {t : T // v t γ = α} = 0 := by
      apply Nat.card_eq_zero.mpr
      left
      exact ⟨fun t => hp.2.1 ((v t.val).injective (t.property.trans (hfix t.val).symm))⟩
    rw [hz, zero_add, add_mul]
    have hb := congrArg (fun z : ℕ => z * (n - 3)) (hbeta γ hp.2.1 hp.2.2)
    have hb' : Nat.card {t : T // v t γ = β} * ((n - 2) * (n - 3)) = q * (n - 3) := by
      simpa only [mul_assoc] using hb
    rw [hb', Finset.sum_mul]
    apply Nat.add_le_add_left
    calc
      _ ≤ ∑ δ ∈ A, q * (m - 2) := by
        apply Finset.sum_le_sum
        intro δ hδ
        have hd := hApart δ hδ
        have hγδ : γ ≠ δ := fun he => hp.1 (he ▸ hd.1)
        exact (by simpa only [mul_assoc] using
          (hpair γ δ hp.2.1 hp.2.2 hd.2.1 hd.2.2 hγδ).le)
      _ = _ := by simp [hA]
  have hCsum : (∑ t : T, (RefinedCommutatorSupport.fixedMovedImage g (v t)).card) *
      ((n - 2) * (n - 3)) ≤
      q * ((n - 2) * (n - 3)) + (m - 2) * (q * ((n - m - 1) * (m - 1))) := by
    have hC (t : T) : RefinedCommutatorSupport.fixedMovedImage g (v t) =
        insert α (A.filter (fun γ => v t γ = γ ∧ v t (g γ) ≠ g γ)) := by
      ext γ
      rw [RefinedCommutatorSupport.mem_fixedMovedImage, hpartition]
      simp only [Finset.mem_insert, Finset.mem_filter, Perm.mem_support]
      constructor
      · rintro ⟨hγ | hγ | hγ, hf, hm⟩
        · exact Or.inl hγ
        · subst γ
          exact ((hmove t) hf).elim
        · exact Or.inr ⟨hγ, hf, hm⟩
      · rintro (rfl | ⟨hγ, hf, hm⟩)
        · exact ⟨Or.inl rfl, hfix t, hmove t⟩
        · exact ⟨Or.inr (Or.inr hγ), hf, hm⟩
    have hCcard (t : T) : (RefinedCommutatorSupport.fixedMovedImage g (v t)).card =
        1 + (A.filter (fun γ => v t γ = γ ∧ v t (g γ) ≠ g γ)).card := by
      rw [hC, Finset.card_insert_of_notMem (fun h => hαA (Finset.mem_filter.mp h).1)]
      omega
    have hbound := sum_card_filter_mul_le A (fun t γ => v t γ = γ ∧ v t (g γ) ≠ g γ)
      ((n - 2) * (n - 3)) (q * ((n - m - 1) * (m - 1))) (by
        intro γ hγ
        have hp := hApart γ hγ
        by_cases hga : g γ = α
        · have hz : Nat.card {t : T // v t γ = γ ∧ v t (g γ) ≠ g γ} = 0 := by
            apply Nat.card_eq_zero.mpr
            left
            exact ⟨fun t => t.property.2 (by simpa only [hga] using hfix t.val)⟩
          rw [hz, zero_mul]
          exact Nat.zero_le _
        · have hgb : g γ ≠ β := fun he => hp.2.1 (g.injective he)
          have hγg : γ ≠ g γ := (Perm.mem_support.mp hp.1).symm
          exact (by simpa only [mul_assoc] using
            (hfixed γ (g γ) hp.2.1 hp.2.2 hga hgb hγg).le))
    simp only [hCcard, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      smul_eq_mul, mul_one] at ⊢
    rw [hA] at hbound
    rw [add_mul, ← Nat.card_eq_fintype_card]
    exact Nat.add_le_add_left hbound _
  have hsum := Finset.sum_le_sum (fun t (_ : t ∈ (Finset.univ : Finset T)) => hpoint t)
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, Finset.sum_add_distrib] at hsum
  rw [← Nat.card_eq_fintype_card] at hsum
  have hsumD := Nat.mul_le_mul_right ((n - 2) * (n - 3)) hsum
  have hIsumD := Nat.mul_le_mul_right (n - 3) hIsum
  have htotal : q * (m * (n - 2) * (n - 3)) ≤ q *
      (2 * (n - 2) * (n - 3) + (m - 2) * (m - 1) * (n - 3) +
        (n - m) * (m - 2)^2 + (n - m) * (n - 3) +
        (m - 2) * (n - m - 1) * (m - 1)) := by
    nlinarith only [hsumD, hIsumD, hBsum, hCsum]
  exact Nat.le_of_mul_le_mul_left htotal (Nat.card_pos (α := T))

end FiveTransitive.FamilyCommutatorAverage

end CFSG
