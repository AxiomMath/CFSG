module

public import CFSG.Quasithin.Background.Basic

public section

namespace CFSG.ASVolI.ChH

open CFSG.Quasithin CFSG.Open

theorem thompsonJ_eq_of_unique_max {G : Type*} [Group G] {H J₀ : Subgroup G}
    (hJ₀H : J₀ ≤ H) (hJ₀ : IsElemAbelian 2 J₀)
    (hmax : ∀ B : Subgroup G, B ≤ H → IsElemAbelian 2 B → Nat.card B ≤ Nat.card J₀)
    (huniq : ∀ B : Subgroup G, B ≤ H → IsElemAbelian 2 B → Nat.card B = Nat.card J₀ →
      B = J₀) :
    thompsonJ H = J₀ := by
  have claim : ∀ A : Subgroup G, IsMaxElemAbelian H A ↔ A = J₀ := by
    intro A
    constructor
    · intro hA
      obtain ⟨hAH, hAe, hAmax⟩ := hA
      have h1 : Nat.card J₀ ≤ Nat.card A := hAmax J₀ hJ₀H hJ₀
      have h2 : Nat.card A ≤ Nat.card J₀ := hmax A hAH hAe
      exact huniq A hAH hAe (le_antisymm h2 h1)
    · intro h
      rw [h]
      exact ⟨hJ₀H, hJ₀, hmax⟩
  apply le_antisymm
  · exact iSup₂_le fun A hA => (claim A).1 hA ▸ le_rfl
  · exact le_iSup₂_of_le J₀ ((claim J₀).2 rfl) le_rfl

end CFSG.ASVolI.ChH
