module

public import CFSG.Quasithin.EmptyFaithful.SzF53MTab

public section

namespace CFSG.Quasithin.F53.Stellmacher.S35.E8

open Equiv CFSG.Quasithin CFSG.Quasithin.F53Mod

@[expose] def DS (t s : Perm (Fin 5)) : Prop :=
  (s ≠ 1 ∧ s ^ 2 = 1 ∧ Perm.sign s ≠ 1) ∧ s * t = t * s ∧ s ≠ t

instance (t s : Perm (Fin 5)) : Decidable (DS t s) := by unfold DS; infer_instance

theorem F1 : ∀ g : Perm (Fin 5), g * swap 0 1 = swap 0 1 * g → g ^ 8 = 1 →
    g = 1 ∨ g = swap 0 1 ∨ ∃ s, DS (swap 0 1) s ∧ (g = s ∨ g = swap 0 1 * s) := by
  decide +kernel

theorem F2 : ∀ s s' : Perm (Fin 5), DS (swap 0 1) s → DS (swap 0 1) s' → s ≠ s' →
    ∀ u u' : Perm (Fin 5), (u = 1 ∨ u = swap 0 1) → (u' = 1 ∨ u' = swap 0 1) →
    ((u * s)⁻¹ * (u' * s')) ^ 8 ≠ 1 := by
  decide +kernel

theorem F4 : ∀ s : Perm (Fin 5), DS (swap 0 1) s →
    s = swap 2 3 ∨ s = swap 2 4 ∨ s = swap 3 4 := by
  decide +kernel

theorem F3 : ∀ s : Perm (Fin 5), (s = swap 2 3 ∨ s = swap 2 4 ∨ s = swap 3 4) →
    ∀ w : orth.W, ∃ w1 w2 : orth.W, orth.act (swap 0 1) w1 = w1 ∧ orth.act s w2 = w2 ∧
      w = w1 * w2 := by
  decide +kernel

theorem F5 : ∀ a b : Fin 5, a ≠ b → ∃ σ : Perm (Fin 5), σ * swap a b * σ⁻¹ = swap 0 1 := by
  decide +kernel

theorem exists_conj_swap {t : Perm (Fin 5)} (ht : t.IsSwap) :
    ∃ σ : Perm (Fin 5), σ * t * σ⁻¹ = swap 0 1 := by
  obtain ⟨a, b, hab, rfl⟩ := ht
  exact F5 a b hab

end CFSG.Quasithin.F53.Stellmacher.S35.E8
