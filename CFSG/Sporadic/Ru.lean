module

public import CFSG.Sporadic.HS.Simple
public import CFSG.Sporadic.Ru.Certificate
public import CFSG.Blueprint.NativeSporadic
import all CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.Sporadic.Ru

open CFSG.Blueprint CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native

theorem ruFacts :
    Facts Native.ruData 3 := facts_of_vecCert _ ru_certificate

theorem isSimpleGroup_Ru : IsSimpleGroup NativeSporadic.Ru :=
  isSimpleGroup_seedUnits ruFacts (by decide) (by decide) (k := 2) rfl (by decide)
    (by norm_num [Native.ruData]) (by norm_num [Native.ruData]) (by norm_num [Native.ruData])
    (by decide) (by decide)

theorem card_Ru : Nat.card NativeSporadic.Ru = 145926144000 := by
  have h : Nat.card NativeSporadic.Ru = _ := card_seedUnits ruFacts
  rw [h]
  decide

theorem fam_ru_simplicity :
    Finite NativeSporadic.Ru ∧ Nontrivial NativeSporadic.Ru ∧
    IsSimpleGroup NativeSporadic.Ru := by
  have hs := isSimpleGroup_Ru
  refine ⟨Nat.finite_of_card_ne_zero (by rw [card_Ru]; norm_num), inferInstance, hs⟩

end CFSG.Sporadic.Ru
