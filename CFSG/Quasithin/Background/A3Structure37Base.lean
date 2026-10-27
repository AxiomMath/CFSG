
module

public import CFSG.Quasithin.Background.A3StructureDefs

@[expose] public section

namespace CFSG.Quasithin

namespace A37

open scoped commutatorElement

theorem quasisimple_quotient_oddCore {X : Type} [Group X] (h : A36Common X) :
    CFSG.IsQuasisimple (X ⧸ CFSG.oddCore X) :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv (QuotientGroup.quotientMulEquivOfEq h.1) h.2.1

theorem fitting_ne_top {X : Type} [Group X] (h : A36Common X) :
    CFSG.fittingSubgroup X ≠ ⊤ := by
  intro htop
  have : Subsingleton (X ⧸ CFSG.fittingSubgroup X) := QuotientGroup.subsingleton_iff.2 htop
  have := CFSG.LocalCores.isQuasisimple_nontrivial h.2.1
  exact not_subsingleton _ ‹Subsingleton (X ⧸ CFSG.fittingSubgroup X)›

theorem fitting_le_center {X : Type} [Group X] (hX : CFSG.IsQuasisimple X) (h : A36Common X) :
    CFSG.fittingSubgroup X ≤ Subgroup.center X :=
  (CFSG.LocalCores.quasisimple_normal_subgroups hX inferInstance).resolve_left (fitting_ne_top h)

theorem commutator_eq_bot_of_quasisimple {G : Type} [Group G] {L₁ L₂ : Subgroup G}
    [Group.IsPerfect ↥L₁] (hq : CFSG.IsQuasisimple ↥L₁) (hcom : A36Common ↥L₁)
    (hc : ⁅L₁, L₂⁆ ≤ (CFSG.fittingSubgroup ↥L₁).map L₁.subtype) : ⁅L₁, L₂⁆ = ⊥ := by
  have hZ := fitting_le_center hq hcom
  refine CFSG.LocalCores.perfect_double_commutator (P := L₁) (X := L₂) ‹Group.IsPerfect ↥L₁› ?_
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro d hd
  obtain ⟨f, hf, rfl⟩ := hc hd
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  exact congrArg Subtype.val (Subgroup.mem_center_iff.mp (hZ hf) ⟨l, hl⟩)

end A37

end CFSG.Quasithin
