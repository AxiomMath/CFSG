module

public import CFSG.Sporadic.HS.Simple
public import CFSG.Sporadic.Co3.Certificate
public import CFSG.Blueprint.NativeSporadic
import all CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.Sporadic.Co3

open CFSG.Blueprint CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native

theorem co3Facts :
    Facts Native.co3Data 3 := facts_of_vecCert _ co3_certificate

theorem isSimpleGroup_Co3 : IsSimpleGroup NativeSporadic.Co3 :=
  isSimpleGroup_seedUnits co3Facts (by decide) (by decide) (k := 4) rfl (by decide)
    (by norm_num [Native.co3Data]) (by norm_num [Native.co3Data]) (by norm_num [Native.co3Data])
    (by decide) (by decide)

theorem card_Co3 : Nat.card NativeSporadic.Co3 = 495766656000 := by
  have h : Nat.card NativeSporadic.Co3 = _ := card_seedUnits co3Facts
  rw [h]
  decide

theorem fam_co3_simplicity :
    Finite NativeSporadic.Co3 ∧ Nontrivial NativeSporadic.Co3 ∧
    IsSimpleGroup NativeSporadic.Co3 := by
  have hs := isSimpleGroup_Co3
  refine ⟨Nat.finite_of_card_ne_zero (by rw [card_Co3]; norm_num), inferInstance, hs⟩

end CFSG.Sporadic.Co3
