module

public import CFSG.Monster.Existence.MilestoneHex
public import CFSG.Monster.Existence.StdOdd.Cert.TableOne

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence

open CFSG.Monster.GMS CFSG.Blueprint.NativeSporadic

theorem babyLineOddOrder :
    BabyLineOddOrder :=
  babyLineOddOrder_of_centralizerFacts StdOdd.Cert.centralizerFacts_std

theorem oddExhaustive_MGriess
    (I : GMSInterfaces (phiB uBar) MGriess) :
    OddExhaustive tGriess xGriess :=
  oddExhaustive_MGriess_of_centralizerFacts I StdOdd.Cert.centralizerFacts_std

theorem monsterExistenceStatement_MGriess_of_recognition
    (hStroth : ∀ d₀ : Blueprint.NativeSporadic.B, orderOf d₀ = 2 →
      Matrix.rank (d₀.val.val - 1) = 1860 →
      ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (d : G), orderOf d = 2 →
        Nonempty (Subgroup.centralizer ({d} : Set G) ≃*
          Subgroup.centralizer ({d₀} : Set Blueprint.NativeSporadic.B)) →
        Nonempty (G ≃* Blueprint.NativeSporadic.B)) :
    MonsterExistenceStatement MGriess :=
  monsterExistenceStatement_MGriess_of_centralizerFacts hStroth StdOdd.Cert.centralizerFacts_std

end CFSG.Monster.Existence
