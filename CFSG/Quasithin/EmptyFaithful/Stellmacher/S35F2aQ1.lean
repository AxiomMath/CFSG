module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35F2aPos

public section

namespace CFSG.Quasithin.F53.Stellmacher.S35.F2a

open Equiv CFSG.Quasithin CFSG.Quasithin.F53Mod CFSG.Quasithin.F53.Stellmacher.S35.Fin

theorem That_sup_dichotomy {D E : Subgroup (Perm (Fin 5))} (hD : Nat.card D = 8)
    (hE : Nat.card E = 8) (hf : fixPt D ≠ fixPt E) :
    That D ⊔ That E = ⊤ ∨ (That D ⊔ That E).index = 10 := by
  rcases sylPair_position hD hE with ⟨h, _⟩ | ⟨_, h, _⟩ | ⟨_, _, _, h⟩ | ⟨_, _, _, h⟩
  · rw [h] at hf; exact absurd rfl hf
  · exact absurd h hf
  · exact Or.inr (index_of_card_twelve h)
  · exact Or.inl h

end CFSG.Quasithin.F53.Stellmacher.S35.F2a
