module

public import CFSG.LocalAnalysis.StandardType.GGSporKBMPreds

public section

namespace CFSG.StandardType.SporadicShape

open CFSG CFSG.StandardType CFSG.Assembly

theorem ggSporK_false_of_elevenComp_W {W : Type} [Group W] [Finite W] (h11 : BMElevenComp W)
    {H E : Subgroup W} (hyp : GGHypThreeSixteenFlat 11 H E) : False := by
  have hE : Nat.card E = 11 ^ 2 := hyp.1.2.2.2.1
  have hE1 : E ≠ ⊥ := by
    rintro rfl
    simp at hE
  obtain ⟨⟨e, heE⟩, he1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hE1
  have he1' : e ≠ 1 := fun h => he1 (Subtype.ext h)
  haveI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have hord : orderOf e = 11 := orderOf_eq_prime (hyp.1.2.2.1.2 e heE) he1'
  obtain ⟨C, hC, hnot⟩ := h11 e hord
  exact hnot (hyp.2.2.2.2.2.2 e heE he1' C hC)

end CFSG.StandardType.SporadicShape
