module

public import CFSG.Monster.B.Cbar.LocalStructure
public import CFSG.Monster.B.Cbar.SylowTwoAux

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short

theorem natCard_Jbar_eq :
    Nat.card Jbar = 2 ^ 41 * 161382375 :=
  natCard_Jbar.trans (by norm_num)

theorem short_centralizer_quotient_sylow_two :
    (∀ P : Sylow 2 Jbar, ∃ S : Sylow 2 Cbar,
      (S : Subgroup Cbar) = (P : Subgroup Jbar).map Jbar.subtype ∧
      (Subgroup.center (S : Subgroup Cbar)).map (S : Subgroup Cbar).subtype =
        Subgroup.zpowers xbar) ∧
    (∃ m : ℕ, Odd m ∧ Nat.card Cbar = 2 ^ 41 * m) ∧
    (∃ m : ℕ, Odd m ∧ Nat.card Cgen = 2 ^ 42 * m) ∧
    Jbar.index = (Jstar.subgroupOf Cgen).index ∧ Odd Jbar.index ∧
    (∀ g : Cbar, (∃ n : ℕ, g ^ 2 ^ n = 1) → ∃ c : Cbar, c * g * c⁻¹ ∈ Jbar) ∧
    (∀ g : Cgen, (∃ n : ℕ, g ^ 2 ^ n = 1) →
      ∃ c : Cgen, ((c * g * c⁻¹ : Cgen) : SpaceB ≃ₗ[ℚ] SpaceB) ∈ Jstar) :=
  sylow_two_of_local centralizer_xbar centralizer_Ebar map_center_Ebar Ebar_extraspecial.1.1
    natCard_Jbar_eq

end CFSG.Monster.B
