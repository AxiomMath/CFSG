module

public import CFSG.Sporadic.J3.Simple
public import CFSG.Sporadic.J3.Cert
public import CFSG.Blueprint.NativeSporadic
import all CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.Sporadic.J3

open CFSG.Blueprint

theorem j3Facts : Facts Native.j3Data 3 := facts_of_check j3_check

private theorem seedA_eq : Native.j3Data.seedA = NativeSporadic.J3Seed1 := rfl

private theorem seedB_eq : Native.j3Data.seedB = NativeSporadic.J3Seed2 := rfl

theorem j3_eq : NativeSporadic.J3 =
    (NativeSporadic.seedMonoid 2 80 1 Native.j3Data.seedA Native.j3Data.seedB)ˣ := by
  rw [seedA_eq, seedB_eq]

theorem isSimpleGroup_J3 : IsSimpleGroup NativeSporadic.J3 := by
  have h := isSimpleGroup_seedUnits j3Facts (by decide) (by decide) (by decide)
  rw [seedA_eq, seedB_eq] at h
  exact h

theorem card_J3 : Nat.card NativeSporadic.J3 = 50232960 := by
  rw [j3_eq, card_seedUnits j3Facts]
  decide

theorem fam_j3_simplicity :
    Finite NativeSporadic.J3 ∧ Nontrivial NativeSporadic.J3 ∧
    IsSimpleGroup NativeSporadic.J3 := by
  have hs := isSimpleGroup_J3
  exact ⟨Nat.finite_of_card_ne_zero (by rw [card_J3]; norm_num), inferInstance, hs⟩

end CFSG.Sporadic.J3
