module

public import CFSG.Quasithin.Background.F7TwoInvAltXi

public section

namespace CFSG.Quasithin.F7Two

open Equiv Equiv.Perm

variable {α : Type*} [DecidableEq α] {σ : Perm α} {B : Set α}

theorem eq_univ_of_closed_fixed {r p : α} (hr : σ r = r) (hp : σ p ≠ p) (hB : B.Nonempty)
    (hcl : ∀ a b d, (σ a = b ∧ a ≠ b ∧ σ d = d) → (a ∈ B ∨ b ∈ B ∨ d ∈ B) →
      a ∈ B ∧ b ∈ B ∧ d ∈ B) : B = Set.univ := by
  obtain ⟨x, hx⟩ := hB
  have hrB : r ∈ B := by
    by_cases hxf : σ x = x
    · have h1 := hcl p (σ p) x ⟨rfl, hp.symm, hxf⟩ (Or.inr (Or.inr hx))
      exact (hcl p (σ p) r ⟨rfl, hp.symm, hr⟩ (Or.inl h1.1)).2.2
    · exact (hcl x (σ x) r ⟨rfl, fun h => hxf h.symm, hr⟩ (Or.inl hx)).2.2
  refine Set.eq_univ_of_forall fun y => ?_
  by_cases hyf : σ y = y
  · have h1 := hcl p (σ p) r ⟨rfl, hp.symm, hr⟩ (Or.inr (Or.inr hrB))
    exact (hcl p (σ p) y ⟨rfl, hp.symm, hyf⟩ (Or.inl h1.1)).2.2
  · exact (hcl y (σ y) r ⟨rfl, fun h => hyf h.symm, hr⟩ (Or.inr (Or.inr hrB))).1

theorem eq_univ_of_closed_free [Fintype α] (hσ : ∀ x, σ (σ x) = x) (hfix : ∀ x, σ x ≠ x)
    (h5 : 5 ≤ Fintype.card α) (hB : B.Nonempty)
    (hcl : ∀ a b d, (a ≠ b ∧ b ≠ d ∧ a ≠ d ∧ ∀ x y, (x = a ∨ x = b ∨ x = d) →
      (y = a ∨ y = b ∨ y = d) → σ x ≠ y) → (a ∈ B ∨ b ∈ B ∨ d ∈ B) → a ∈ B ∧ b ∈ B ∧ d ∈ B) :
    B = Set.univ := by
  have step : ∀ x ∈ B, ∀ y, y ≠ σ x → y ∈ B := by
    intro x hx y hy
    by_cases hyx : y = x
    · exact hyx ▸ hx
    obtain ⟨d, -, hd⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (s := ({x, σ x, y, σ y} : Finset α)) (t := Finset.univ)
      (by rw [Finset.card_univ]; exact lt_of_le_of_lt Finset.card_le_four (by omega))
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hd
    have := hσ x
    have := hσ y
    have := hσ d
    have := hfix x
    have := hfix y
    have := hfix d
    refine (hcl x y d ⟨Ne.symm hyx, by grind, by grind, ?_⟩ (Or.inl hx)).2.1
    rintro x' y' (rfl | rfl | rfl) (rfl | rfl | rfl) <;> grind
  obtain ⟨x, hx⟩ := hB
  refine Set.eq_univ_of_forall fun y => ?_
  by_cases hy : y = σ x
  · obtain ⟨z, -, hz⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (s := ({x, σ x} : Finset α)) (t := Finset.univ)
      (by rw [Finset.card_univ]; exact lt_of_le_of_lt Finset.card_le_two (by omega))
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hz
    exact hy ▸ step z (step x hx z hz.2) (σ x) fun h => hz.1 (σ.injective h).symm
  · exact step x hx y hy

theorem invGen_alternatingGroup [Fintype α] (h5 : 5 ≤ Fintype.card α) (hσ : σ * σ = 1)
    (hσ1 : σ ≠ 1) : InvGen (alternatingGroup α) σ := by
  have hσ' : ∀ x, σ (σ x) = x := fun x => by simpa using congrArg (fun f : Perm α => f x) hσ
  have : Nontrivial α := Fintype.one_lt_card_iff_nontrivial.1 (by omega)
  refine le_antisymm ((Subgroup.closure_le _).2 fun x hx => hx.1) ?_
  by_cases hfix : ∃ r, σ r = r
  · obtain ⟨r, hr⟩ := hfix
    obtain ⟨p, hp⟩ : ∃ p, σ p ≠ p := by
      by_contra! h
      exact hσ1 (Equiv.ext h)
    refine alternatingGroup_le_of_connected
      (P := fun a b d => σ a = b ∧ a ≠ b ∧ σ d = d) ?_
      fun B hB hcl => eq_univ_of_closed_fixed hr hp hB hcl
    rintro a b d ⟨h1, h2, h3⟩
    have h2' : σ b = a := h1 ▸ hσ' a
    have hbd : b ≠ d := fun h => h2 (h2'.symm.trans (by rw [h, h3]))
    have had : a ≠ d := fun h => h2 ((by rw [h, h3] : σ a = a).symm.trans h1)
    exact ⟨h2, hbd, had, Subgroup.subset_closure (triCycle_mem_invXi_fixed h2 hbd had h1 h2' h3)⟩
  · push Not at hfix
    refine alternatingGroup_le_of_connected
      (P := fun a b d => a ≠ b ∧ b ≠ d ∧ a ≠ d ∧ ∀ x y, (x = a ∨ x = b ∨ x = d) →
        (y = a ∨ y = b ∨ y = d) → σ x ≠ y) ?_
      fun B hB hcl => eq_univ_of_closed_free hσ' hfix h5 hB hcl
    rintro a b d ⟨hab, hbd, had, h⟩
    exact ⟨hab, hbd, had, Subgroup.subset_closure (triCycle_mem_invXi_disjoint hab hbd had h)⟩

theorem invGen_alternatingGroup_fin {n : ℕ} (hn : 5 ≤ n) {σ : Perm (Fin n)} (hσ : σ * σ = 1)
    (hσ1 : σ ≠ 1) : InvGen (alternatingGroup (Fin n)) σ :=
  invGen_alternatingGroup (by simpa using hn) hσ hσ1

end CFSG.Quasithin.F7Two
