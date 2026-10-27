module

public import CFSG.Quasithin.EmptyFaithfulMultiple.F618CompBasic
public import CFSG.Sporadic.Mathieu.M12

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

namespace F618Comp

open CFSG.Blueprint


theorem exists_ne_comm_m12 : ∃ a b : ↥NativeSporadic.M12, a * b ≠ b * a :=
  ⟨Sporadic.Mathieu.m12a, Sporadic.Mathieu.m12b, fun h => by
    have := congrArg Subtype.val h
    revert this
    decide⟩

theorem notSL2_m12 : NotSL2 ↥NativeSporadic.M12 :=
  notSL2_of_card 6 (by rw [Sporadic.Mathieu.card_M12]; norm_num)
    (by rw [Sporadic.Mathieu.card_M12]; norm_num)

theorem socle_m12 : Socle ↥NativeSporadic.M12 :=
  have := Sporadic.Mathieu.fam_m12_simplicity.2.2
  socle_of_isSimpleGroup exists_ne_comm_m12 notSL2_m12

theorem socle_autM12 : Socle (MulAut ↥NativeSporadic.M12) :=
  have := Sporadic.Mathieu.fam_m12_simplicity.2.2
  socle_mulAut exists_ne_comm_m12 notSL2_m12

end F618Comp

end CFSG.Quasithin.EmptyFaithfulMultiple
