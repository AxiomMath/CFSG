module

public import CFSG.Sporadic.Bridge.BBound
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation

public section

namespace CFSG.RankThree.PartOne.TCB

open TauCeti CFSG.Blueprint

theorem nonempty_mulEquiv_B :
    Nonempty (NativeSporadic.B ≃* SporadicName.B.Group) := by
  obtain ⟨hfin, hcard⟩ := CFSG.Sporadic.Bridge.B.finite_card_le
  have hle : 4154781481226426191177580544000000 ≤ Nat.card NativeSporadic.B := by
    rw [CFSG.Monster.Existence.card_nativeB]
    exact le_of_eq (by unfold CFSG.Open.monsterBabyOrder; norm_num)
  exact @CFSG.Sporadic.Bridge.nonempty_mulEquiv_of_surjective
    CFSG.Sporadic.Bridge.B.pres.Group NativeSporadic.B _ _ hfin CFSG.Sporadic.Bridge.B.φ
    CFSG.Sporadic.Bridge.B.φ_surjective _ hcard hle

end CFSG.RankThree.PartOne.TCB
