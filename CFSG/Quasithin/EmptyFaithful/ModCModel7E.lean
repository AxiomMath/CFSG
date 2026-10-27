module

public import CFSG.Quasithin.EmptyFaithful.ModCModel7Defs

public section

namespace CFSG.Quasithin.ModC

open Equiv Equiv.Perm CFSG.Quasithin.G6

namespace M7

set_option maxRecDepth 100000

theorem trans4 : ∀ p q : Fin 7, p.val < 4 → q.val < 4 →
    q = p ∨ q = (swap 0 1 * swap 2 3 : Perm (Fin 7)) p ∨ q = (swap 0 2 * swap 1 3 : Perm (Fin 7)) p ∨
      q = ((swap 0 1 * swap 2 3) * (swap 0 2 * swap 1 3) : Perm (Fin 7)) p := by
  decide +kernel

theorem gens_stab45 : ∀ s ∈ gens, s ∈ stab45 := by decide +kernel

theorem D0_le_stab45 : D0 ≤ stab45 :=
  (Subgroup.closure_le _).2 fun s hs => gens_stab45 s hs

theorem mem_stab45_of_fix {g : Perm (Fin 7)} (h : permAct 7 g b = b) : g ∈ stab45 := by
  intro i
  have h1 := congrFun (congrArg Multiplicative.toAdd h) (g i)
  have e : g⁻¹ (g i) = i := by simp
  simp only [permAct_apply, e, b, ev, toAdd_ofAdd] at h1
  have hmem : ∀ j : Fin 7, ((j : ℕ) ∈ [4, 5]) ↔ (j = 4 ∨ j = 5) := by decide
  rw [← hmem, ← hmem]
  by_cases hi : (i : ℕ) ∈ [4, 5] <;> by_cases hgi : ((g i : Fin 7) : ℕ) ∈ [4, 5] <;>
    simp [hi, hgi] at h1 ⊢

theorem orbit5 (g : Perm (Fin 7)) (hg : g ∈ stab45) (hg6 : (g 6).val < 4) :
    5 ∣ Nat.card ↥(Subgroup.closure ((D0 : Set (Perm (Fin 7))) ∪ {g})) := by
  classical
  let X := Subgroup.closure ((D0 : Set (Perm (Fin 7))) ∪ {g})
  have hXle : X ≤ stab45 := by
    refine (Subgroup.closure_le _).2 ?_
    rintro s (hs | hs)
    · exact D0_le_stab45 hs
    · rw [Set.mem_singleton_iff.mp hs]; exact hg
  have hD0X : D0 ≤ X := fun s hs => Subgroup.subset_closure (Or.inl hs)
  have hgX : g ∈ X := Subgroup.subset_closure (Or.inr rfl)
  have hs1 : (swap 0 1 * swap 2 3 : Perm (Fin 7)) ∈ D0 := Subgroup.subset_closure (by simp [gens])
  have hs2 : (swap 0 2 * swap 1 3 : Perm (Fin 7)) ∈ D0 := Subgroup.subset_closure (by simp [gens])
  have horb : MulAction.orbit X (6 : Fin 7) = {i : Fin 7 | i.val < 4 ∨ i = 6} := by
    ext i
    constructor
    · rintro ⟨σ, rfl⟩
      have h := hXle σ.2
      have h6 : ¬ ((σ : Perm (Fin 7)) 6 = 4 ∨ (σ : Perm (Fin 7)) 6 = 5) := fun hh => by
        have := (h 6).1 hh
        revert this; decide
      show ((σ : Perm (Fin 7)) 6).val < 4 ∨ (σ : Perm (Fin 7)) 6 = 6
      generalize (σ : Perm (Fin 7)) 6 = k at h6 ⊢
      revert h6
      revert k
      decide
    · rintro (hi | rfl)
      · rcases trans4 (g 6) i hg6 hi with h | h | h | h
        · exact ⟨⟨g, hgX⟩, by simp [h]⟩
        · exact ⟨⟨swap 0 1 * swap 2 3 * g, X.mul_mem (hD0X hs1) hgX⟩, by simp [h]⟩
        · exact ⟨⟨swap 0 2 * swap 1 3 * g, X.mul_mem (hD0X hs2) hgX⟩, by simp [h]⟩
        · exact ⟨⟨((swap 0 1 * swap 2 3) * (swap 0 2 * swap 1 3)) * g,
            X.mul_mem (hD0X (D0.mul_mem hs1 hs2)) hgX⟩, by simp [h]⟩
      · exact ⟨1, rfl⟩
  have hcard : Nat.card (MulAction.orbit X (6 : Fin 7)) = 5 := by
    rw [horb]
    rw [Nat.card_eq_fintype_card]
    decide
  have := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup X (6 : Fin 7))
  rw [Nat.card_prod, hcard] at this
  exact ⟨_, this.symm⟩

end M7

end CFSG.Quasithin.ModC
