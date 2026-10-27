module

public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.Assembly.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore

public section

namespace CFSG.Quasithin.SteinbergBK

open Subgroup Matrix Equiv CFSG CFSG.ABGLocalTools
open scoped commutatorElement

section Reduced

variable {X : Type*} [Group X]

theorem pCore_two_alternatingGroup_five_eq_bot : pCore 2 (alternatingGroup (Fin 5)) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsSimpleGroup (alternatingGroup (Fin 5)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin])
  rcases Subgroup.Normal.eq_bot_or_eq_top (pCore 2 (alternatingGroup (Fin 5))) with h | h
  · exact h
  · exfalso
    have h2 : IsPGroup 2 (alternatingGroup (Fin 5)) := by
      have := pCore_isPGroup (p := 2) (G := alternatingGroup (Fin 5))
      rw [h] at this
      exact this.of_equiv Subgroup.topEquiv
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp h2
    rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin] at hm
    have h3 : 3 ∣ 2 ^ m := by
      rw [← hm]
      decide
    have := Nat.prime_three.dvd_of_dvd_pow h3
    omega

end Reduced

end CFSG.Quasithin.SteinbergBK
