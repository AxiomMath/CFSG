module

public import CFSG.RankThree.GF2n.Stroth80.Sec5Defs

public section

namespace CFSG.RankThree.GF2n.Stroth80

open scoped commutatorElement

variable {G : Type} [Group G]

theorem isOppDecomp_of_split {P I L₁ L₂ A₁ A₂ A : Subgroup G}
    (hd : IsOppDecomp P I L₁ L₂ A₁ A₂) (hIA : I ≤ A) (hAP : A ≤ P)
    (hsplit : A ≤ (A ⊓ A₁) ⊔ (A ⊓ A₂)) :
    IsOppDecomp A I L₁ L₂ (A ⊓ A₁) (A ⊓ A₂) := by
  obtain ⟨h1, -, h3, -, -, h6, h7, h8, h9, h10⟩ := hd
  refine ⟨le_inf hIA h1, inf_le_left, le_inf hIA h3, inf_le_left,
    le_antisymm (sup_le inf_le_left inf_le_left) hsplit, ?_, ?_, ?_, ?_, ?_⟩
  · apply le_antisymm
    · have hsub : (A ⊓ A₁) ⊓ (A ⊓ A₂) ≤ A₁ ⊓ A₂ :=
        le_inf (le_trans inf_le_left inf_le_right) (le_trans inf_le_right inf_le_right)
      exact hsub.trans_eq h6
    · exact le_inf (le_inf hIA h1) (le_inf hIA h3)
  · intro x hx y hy
    exact h7 x (hAP hx) y (hAP hy)
  · intro x hx
    exact h8 x (hAP hx)
  · intro x hx
    constructor
    · intro h
      exact (h9 x (hAP hx)).1 (Subgroup.mem_inf.mp h).2
    · intro h
      exact Subgroup.mem_inf.mpr ⟨hx, (h9 x (hAP hx)).2 h⟩
  · intro x hx
    constructor
    · intro h
      exact (h10 x (hAP hx)).1 (Subgroup.mem_inf.mp h).2
    · intro h
      exact Subgroup.mem_inf.mpr ⟨hx, (h10 x (hAP hx)).2 h⟩

end CFSG.RankThree.GF2n.Stroth80
