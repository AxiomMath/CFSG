module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Delta5

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecE

open CFSG.QuasithinUnique.A5.Delta5 Equiv

theorem card_support_iff_card_commute : ∀ σ : Perm (Fin 5), σ * σ = 1 →
    ((Finset.univ.filter (fun g : Perm (Fin 5) => g * σ = σ * g)).card = 12 ↔
      σ.support.card = 2) := by
  decide +kernel

theorem isSwap_map_mulEquiv (φ : Perm (Fin 5) ≃* Perm (Fin 5)) {τ : Perm (Fin 5)}
    (hτ : τ.IsSwap) : (φ τ).IsSwap := by
  have hττ : τ * τ = 1 := by
    obtain ⟨x, y, -, rfl⟩ := hτ
    exact swap_mul_self x y
  have hφφ : φ τ * φ τ = 1 := by rw [← map_mul, hττ, map_one]
  rw [← Perm.card_support_eq_two] at hτ ⊢
  rw [← card_support_iff_card_commute _ hφφ]
  rw [← (card_support_iff_card_commute _ hττ)] at hτ
  rw [← hτ]
  refine Finset.card_bij (fun g _ => φ.symm g) ?_ ?_ ?_
  · intro g hg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
    have := congrArg φ.symm hg
    simpa using this
  · intro g₁ _ g₂ _ h
    exact φ.symm.injective h
  · intro g hg
    refine ⟨φ g, ?_, by simp⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
    rw [← map_mul, ← map_mul, hg]

theorem exists_comm_pair : ∀ i j : Fin 5, i ≠ j → ∃ σ : Perm (Fin 5), σ ^ 3 = 1 ∧ σ ≠ 1 ∧
    ∃ z : Fin 5 → ZMod 2, isEven z ∧
      pact σ z + z = (Pi.single i 1 + Pi.single j 1 : Fin 5 → ZMod 2) := by
  decide +kernel

end CFSG.Quasithin.Vol2.Ch10.SecE
