module

public import CFSG.Sporadic.HS.Simple
public import CFSG.Sporadic.HS.Certificate
public import CFSG.Blueprint.NativeSporadic
import all CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.Sporadic.HS

open CFSG.Blueprint CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native

theorem hsFacts :
    Facts Native.hsData 3 := facts_of_vecCert _ hs_certificate

theorem isSimpleGroup_HS : IsSimpleGroup NativeSporadic.HS :=
  isSimpleGroup_seedUnits hsFacts (by decide) (by decide) (k := 4) rfl (by decide)
    (by norm_num [Native.hsData]) (by norm_num [Native.hsData]) (by norm_num [Native.hsData])
    (by decide) (by decide)

theorem card_HS : Nat.card NativeSporadic.HS = 44352000 := by
  have h : Nat.card NativeSporadic.HS = _ := card_seedUnits hsFacts
  rw [h]
  decide

theorem fam_hs_simplicity :
    Finite NativeSporadic.HS ∧ Nontrivial NativeSporadic.HS ∧
    IsSimpleGroup NativeSporadic.HS := by
  have hs := isSimpleGroup_HS
  refine ⟨Nat.finite_of_card_ne_zero (by rw [card_HS]; norm_num), inferInstance, hs⟩

end CFSG.Sporadic.HS
