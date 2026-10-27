module

public import CFSG.Monster.Existence.Assembly
public import CFSG.Monster.Existence.EbCensus
public import CFSG.Monster.Existence.Census.TwoClasses

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short
  CFSG.Monster.B

theorem cosetTwoBCensus :
    CosetTwoBCensus :=
  CosetTwoBCensus.of_witnesses Census.trialityWitness_two Census.trialityWitness_three
    Census.trialityWitness_four Census.fusion_to_seventeen

theorem monster_existence_clauses_one_two_of_count
    (hH : ∀ g ∈ Gmat, g * tStar = tStar * g → g ∈ Cgen)
    (hcount : Nat.card Gmat = 97239461142009186000 * Nat.card Cgen)
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
  monster_existence_clauses_one_two_of_inputs Census.generated_group_two_involution_classes
    (hEb_FE cosetTwoBCensus) hH hcount AxisCount.Baby.natCard_Cbar hStroth

theorem monsterExistenceStatement_MGriess_of_count
    (hH : ∀ g ∈ Gmat, g * tStar = tStar * g → g ∈ Cgen)
    (hcount : Nat.card Gmat = 97239461142009186000 * Nat.card Cgen)
    (hStroth : ∀ d₀ : Blueprint.NativeSporadic.B, orderOf d₀ = 2 →
      Matrix.rank (d₀.val.val - 1) = 1860 →
      ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (d : G), orderOf d = 2 →
        Nonempty (Subgroup.centralizer ({d} : Set G) ≃*
          Subgroup.centralizer ({d₀} : Set Blueprint.NativeSporadic.B)) →
        Nonempty (G ≃* Blueprint.NativeSporadic.B))
    (hgraph : IsTwoAGraphData tGriess xGriess) :
    MonsterExistenceStatement MGriess :=
  monsterExistenceStatement_MGriess_of_census Census.generated_group_two_involution_classes
    cosetTwoBCensus hH hcount hStroth hgraph

end CFSG.Monster.Existence
