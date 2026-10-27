module

public import CFSG.Monster.B.TwoA.Amalgam.DerivedCover
public import CFSG.Monster.B.TwoA.Amalgam.StdQuot

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.E6
  CFSG.LieType.Chevalley.C2E6Std CFSG.LieType.Chevalley.C2E6Std.FieldExtension

theorem short_F4_derived_standard_perfect_cover :
    (commutator Eam).index = 2 ∧ Group.IsPerfect (commutator Eam) ∧
      Subgroup.center Eam = Subgroup.zpowers cE' ∧
      (Subgroup.center (commutator Eam)).map (commutator Eam).subtype = Subgroup.zpowers cE' ∧
      Nat.card (Subgroup.zpowers cE') = 2 ∧
      Nonempty (commutator Eam ⧸ (Subgroup.zpowers cE').subgroupOf (commutator Eam) ≃*
        stdGroup) ∧
      (¬ ∃ L : Subgroup Eam, L ≤ commutator Eam ∧ Subgroup.zpowers cE' ⊓ L = ⊥ ∧
        Subgroup.zpowers cE' ⊔ L = commutator Eam) ∧
      Nat.card (commutator Eam) = 153064959367549707878400 ∧
      Nonempty (Eam ⧸ Subgroup.zpowers cE' ≃* GStar) ∧
      ∀ θ : Eam ⧸ Subgroup.zpowers cE' ≃* GStar, commutator Eam =
        Ginl.comap (θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.zpowers cE'))) := by
  obtain ⟨θ, -⟩ := short_F4_standard_twisted_E6_quotient
  obtain ⟨hperf, hidx, hZE, hZE', he, hsplit, hcard, -⟩ := derived_cover_Eam θ
  exact ⟨hidx, hperf, hZE, hZE', natCard_zpowers_cE'_eq_two, he, hsplit, hcard, ⟨θ⟩,
    fun θ' => (derived_cover_Eam θ').2.2.2.2.2.2.2⟩

end CFSG.Monster.B.TwoA.Amalgam
