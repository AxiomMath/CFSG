module

public import CFSG.Sporadic.HS.Simple
public import CFSG.Sporadic.Co2.Certificate
public import CFSG.Blueprint.NativeSporadic
import all CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.Sporadic.Co2

open CFSG.Blueprint CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native

theorem co2Facts :
    Facts Native.co2Data 3 := facts_of_vecCert _ co2_certificate

theorem isSimpleGroup_Co2 : IsSimpleGroup NativeSporadic.Co2 :=
  isSimpleGroup_seedUnits co2Facts (by decide) (by decide) (k := 2) rfl (by decide)
    (by norm_num [Native.co2Data]) (by norm_num [Native.co2Data]) (by norm_num [Native.co2Data])
    (by decide) (by decide)

theorem card_Co2 : Nat.card NativeSporadic.Co2 = 42305421312000 := by
  have h : Nat.card NativeSporadic.Co2 = _ := card_seedUnits co2Facts
  rw [h]
  decide

theorem fam_co2_simplicity :
    Finite NativeSporadic.Co2 ∧ Nontrivial NativeSporadic.Co2 ∧
    IsSimpleGroup NativeSporadic.Co2 := by
  have hs := isSimpleGroup_Co2
  refine ⟨Nat.finite_of_card_ne_zero (by rw [card_Co2]; norm_num), inferInstance, hs⟩

end CFSG.Sporadic.Co2
