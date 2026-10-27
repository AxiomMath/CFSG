module

public import CFSG.Sporadic.Th.Recog.DModel

public section

namespace CFSG.Sporadic.Th.Recog

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Max3
open CFSG.Sporadic.Recognition.PresentedWords

@[expose] noncomputable def incDJ : ↥DJ →* ↥Max3.M := Subgroup.inclusion DJ_le_M

@[expose] noncomputable def incDP : ↥DP →* ↥Max3.M := incDJ.comp (eDP : ↥DP →* ↥DJ)

theorem incDJ_injective : Function.Injective incDJ := Subgroup.inclusion_injective DJ_le_M

theorem incDP_injective : Function.Injective incDP := incDJ_injective.comp eDP.injective

theorem coe_incDP (x : ↥DP) :
    ((incDP x : ↥Max3.M) : J) = ((eDP x : ↥DJ) : J) := rfl

theorem coe_incDP_dPD (j : Fin 6) :
    ((incDP (dPD j) : ↥Max3.M) : J) = dJ j := by
  rw [coe_incDP, eDP_letter]
  rfl

theorem orderOf_incDP (x : ↥DP) : orderOf (incDP x) = orderOf x :=
  orderOf_injective incDP incDP_injective x

end CFSG.Sporadic.Th.Recog

