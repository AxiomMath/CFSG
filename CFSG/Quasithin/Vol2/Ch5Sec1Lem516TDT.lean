module

public import CFSG.Quasithin.Vol2.Ch5Sec1Lem516TD
public import CFSG.Quasithin.EmptyFaithful.S151Statements

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G] {T M L H X W : Subgroup G} {n : ℕ}

namespace Hyp5_0_1

variable (h : Hyp5_0_1 G T M L n)
include h

theorem pCoreOf_ne_bot_or_qhat_le_of_316 (h316 : Theorem316Statement) (hH : IsHStar T M H)
    (hX : X ≤ borelL T L) (hW : IsTDMod T X W)
    (hI : H ⊓ M ≤ Subgroup.normalizer (oTwoUpper (T ⊔ X) : Set G)) :
    pCoreOf 2 (X ⊔ H) ≠ ⊥ ∨ qhatInt (T ⊔ X) W hW.1.2.2.1 ≤ 2 := by
  have h315 := h.hyp315_sup hH hX hW hI
  rcases h316 G T h.simple h.nonabelian h.qtke h.sylow M (T ⊔ X) H W h.inM h315
    with ⟨R₀, h1, h2, h3⟩ | ⟨-, h2, -⟩ | h2
  · exact Or.inl (h.pCoreOf_ne_bot_of_normal hH h1 h2 h3)
  · exact Or.inr h2
  · exact Or.inr ((qhatInt_le_qInt _ _ _).trans h2)

end Hyp5_0_1

end CFSG.Quasithin.H13

end
