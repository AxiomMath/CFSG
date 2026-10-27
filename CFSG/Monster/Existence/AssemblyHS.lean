module

public import CFSG.Monster.Existence.AssemblyCensus
public import CFSG.Monster.Existence.GMSF1
public import CFSG.Monster.AxisCount.HSCount

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short
  CFSG.Monster.B CFSG.Monster.GMS

theorem centralizer_FE_le_GmatGriess_uncond :
    Subgroup.centralizer (FE : Set MGriess) ≤ GmatGriess :=
  centralizer_FE_le_GmatGriess (xfusion_of_census Census.generated_group_two_involution_classes)
    (hEb_FE cosetTwoBCensus)

theorem mem_Cgen_of_conj_uA_uncond
    (c : CfullA)
    (hc : c * uA * c⁻¹ = uA ∨ c * uA * c⁻¹ = uA * tStarA) :
    (c : SpaceB ≃ₗ[ℚ] SpaceB) ∈ Cgen :=
  mem_Cgen_of_conj_uA centralizer_FE_le_GmatGriess_uncond AxisCount.HS.centralizer_tStar_le_Cgen
    c hc

theorem gmsF1Type_MGriess_uncond :
    GMSF1Type (phiB uBar) tGriess xGriess :=
  gmsF1Type_MGriess mem_Cgen_of_conj_uA_uncond

theorem monster_existence_clauses_one_two_of_stroth
    (hStroth : ∀ d₀ : Blueprint.NativeSporadic.B, orderOf d₀ = 2 →
      Matrix.rank (d₀.val.val - 1) = 1860 →
      ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (d : G), orderOf d = 2 →
        Nonempty (Subgroup.centralizer ({d} : Set G) ≃*
          Subgroup.centralizer ({d₀} : Set Blueprint.NativeSporadic.B)) →
        Nonempty (G ≃* Blueprint.NativeSporadic.B)) :
    (Finite MGriess ∧ IsSimpleGroup MGriess ∧ (∃ x y : MGriess, x * y ≠ y * x) ∧
      Nat.card MGriess = CFSG.Open.monsterOrder) ∧
    orderOf tGriess = 2 ∧ orderOf xGriess = 2 ∧ ¬ IsConj tGriess xGriess ∧
    (∀ t : MGriess, orderOf t = 2 → IsConj tGriess t ∨ IsConj xGriess t) ∧
    (∀ α, IsConj tGriess α → IsTwoACentralizer α) ∧
    (∀ ζ, IsConj xGriess ζ → IsTwoBCentralizer ζ) :=
  monster_existence_clauses_one_two_of_count AxisCount.HS.centralizer_tStar_le_Cgen
    AxisCount.HS.natCard_Gmat hStroth

theorem monsterExistenceStatement_MGriess_of_stroth
    (hStroth : ∀ d₀ : Blueprint.NativeSporadic.B, orderOf d₀ = 2 →
      Matrix.rank (d₀.val.val - 1) = 1860 →
      ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (d : G), orderOf d = 2 →
        Nonempty (Subgroup.centralizer ({d} : Set G) ≃*
          Subgroup.centralizer ({d₀} : Set Blueprint.NativeSporadic.B)) →
        Nonempty (G ≃* Blueprint.NativeSporadic.B))
    (hgraph : IsTwoAGraphData tGriess xGriess) :
    MonsterExistenceStatement MGriess :=
  monsterExistenceStatement_MGriess_of_count AxisCount.HS.centralizer_tStar_le_Cgen
    AxisCount.HS.natCard_Gmat hStroth hgraph

end CFSG.Monster.Existence
