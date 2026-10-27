module

public import CFSG.Quasithin.Vol2.GoldschmidtF431TwoF4Defs
public import CFSG.LieType.Ree.LargeReeFixedGroupOddCore

public section

namespace CFSG.Quasithin.H13.F431.TwoF4

open CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag

set_option linter.unusedSectionVars false


variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

theorem isSimpleGroup_gm (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    IsSimpleGroup (Gm K a) := by
  have h := CFSG.LieType.Simplicity.isSimpleGroup_quotient_center_reeFixed_F4 a ha hK
  let e := reeFixedEquivReeGamma K a
  have hz : Subgroup.center (reeFixed ReeTag.F4 K a) = ⊥ := by
    have h1 := CFSG.ComponentClassification.OuterAutomorphisms.center_map_equiv e
    rw [large_Ree_fixed_group_center_trivial a K hK] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).1 h1
  let q : (reeFixed ReeTag.F4 K a ⧸ Subgroup.center (reeFixed ReeTag.F4 K a)) ≃*
      reeFixed ReeTag.F4 K a :=
    (QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot
  exact (MulEquiv.isSimpleGroup_congr (q.trans e)).1 h

end CFSG.Quasithin.H13.F431.TwoF4
