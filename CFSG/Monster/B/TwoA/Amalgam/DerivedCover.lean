module

public import CFSG.Monster.B.E6.GStarStructure
public import CFSG.Monster.B.TwoA.Amalgam.CentralExt

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.E6
  CFSG.LieType.Chevalley.C2E6Std CFSG.LieType.Chevalley.C2E6Std.FieldExtension

theorem zpowers_cE'_le_center :
    Subgroup.zpowers cE' ≤ Subgroup.center Eam :=
  Subgroup.zpowers_le.2 cE'_mem_center

theorem natCard_zpowers_cE'_eq_two :
    Nat.card (Subgroup.zpowers cE') = 2 := by
  rw [Nat.card_zpowers]
  exact short_F4_central_extension_nonsplit.2.2.2.2.2.1

theorem zpowers_cE'_le_commutator :
    Subgroup.zpowers cE' ≤ commutator Eam :=
  Subgroup.zpowers_le.2 cE'_mem_commutator

theorem derived_cover_Eam
    (θ : Eam ⧸ Subgroup.zpowers cE' ≃* GStar) :
    Group.IsPerfect (commutator Eam) ∧ (commutator Eam).index = 2 ∧
      Subgroup.center Eam = Subgroup.zpowers cE' ∧
      (Subgroup.center (commutator Eam)).map (commutator Eam).subtype = Subgroup.zpowers cE' ∧
      Nonempty (commutator Eam ⧸ (Subgroup.zpowers cE').subgroupOf (commutator Eam) ≃*
        stdGroup) ∧
      (¬ ∃ L : Subgroup Eam, L ≤ commutator Eam ∧ Subgroup.zpowers cE' ⊓ L = ⊥ ∧
        Subgroup.zpowers cE' ⊔ L = commutator Eam) ∧
      Nat.card (commutator Eam) = 153064959367549707878400 ∧
      commutator Eam =
        Ginl.comap (θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.zpowers cE'))) :=
  derived_cover_of_iso _ zpowers_cE'_le_center natCard_zpowers_cE'_eq_two
    zpowers_cE'_le_commutator θ

end CFSG.Monster.B.TwoA.Amalgam
