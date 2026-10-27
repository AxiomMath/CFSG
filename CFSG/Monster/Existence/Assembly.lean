module

public import CFSG.Monster.Existence.ClausesOneTwo
public import CFSG.Monster.Existence.EbMain
public import CFSG.Monster.AxisCount.BabySetup

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short
  CFSG.Monster.B

theorem monsterExistenceStatement_MGriess_of_inputs
    (hcensus : ∀ g : Gmat, orderOf g = 2 → IsConj xGmat g ∨ IsConj tGmat g)
    (hEb : ∀ e ∈ Subgroup.centralizer (FE : Set MGriess) ⊓
        Subgroup.centralizer ({xGriess} : Set MGriess),
      e * e = 1 → e ∉ FE → ∃ f ∈ FE, IsConj xGriess (e * f))
    (hH : ∀ g ∈ Gmat, g * tStar = tStar * g → g ∈ Cgen)
    (hcount : Nat.card Gmat = 97239461142009186000 * Nat.card Cgen)
    (hS : Nat.card Cbar = 4154781481226426191177580544000000)
    (hStroth : ∀ d₀ : Blueprint.NativeSporadic.B, orderOf d₀ = 2 →
      Matrix.rank (d₀.val.val - 1) = 1860 →
      ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (d : G), orderOf d = 2 →
        Nonempty (Subgroup.centralizer ({d} : Set G) ≃*
          Subgroup.centralizer ({d₀} : Set Blueprint.NativeSporadic.B)) →
        Nonempty (G ≃* Blueprint.NativeSporadic.B))
    (hgraph : IsTwoAGraphData tGriess xGriess) :
    MonsterExistenceStatement MGriess := by
  obtain ⟨h1, ht, hx, hnc, hcl, hA, hB⟩ :=
    monster_existence_clauses_one_two_of_inputs hcensus hEb hH hcount hS hStroth
  exact ⟨h1, tGriess, xGriess, ht, hx, hnc, hcl, hA, hB, hgraph⟩

theorem monsterExistenceStatement_MGriess_of_census
    (hcensus : ∀ g : Gmat, orderOf g = 2 → IsConj xGmat g ∨ IsConj tGmat g)
    (hcen : CosetTwoBCensus)
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
  monsterExistenceStatement_MGriess_of_inputs hcensus (hEb_FE hcen) hH hcount
    AxisCount.Baby.natCard_Cbar hStroth hgraph

end CFSG.Monster.Existence
