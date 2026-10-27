
module


public import CFSG.Sporadic.HS.Simple
public import CFSG.Sporadic.Co1.Certificate
public import CFSG.Blueprint.NativeSporadic
import all CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.Sporadic.Co1

open CFSG.Blueprint CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native

theorem co1Facts :
    Facts Native.co1Data 3 := facts_of_vecCert _ co1_certificate

theorem isSimpleGroup_Co1 : IsSimpleGroup NativeSporadic.Co1 :=
  isSimpleGroup_seedUnits co1Facts (by decide) (by decide) (k := 3) rfl (by decide)
    (by norm_num [Native.co1Data]) (by norm_num [Native.co1Data]) (by norm_num [Native.co1Data])
    (by decide) (by decide)

theorem card_Co1 :
    Nat.card NativeSporadic.Co1 = 4157776806543360000 := by
  have h : Nat.card NativeSporadic.Co1 = _ := card_seedUnits co1Facts
  rw [h]
  decide

theorem fam_co1_simplicity :
    Finite NativeSporadic.Co1 ∧ Nontrivial NativeSporadic.Co1 ∧
    IsSimpleGroup NativeSporadic.Co1 := by
  have hs := isSimpleGroup_Co1
  refine ⟨Nat.finite_of_card_ne_zero (by rw [card_Co1]; norm_num), inferInstance, hs⟩

end CFSG.Sporadic.Co1
