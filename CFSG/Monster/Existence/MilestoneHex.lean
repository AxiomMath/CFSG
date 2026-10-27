module

public import CFSG.Monster.Existence.OddExhaustiveGriess
public import CFSG.Monster.Existence.StdOdd.ReduceThree
public import CFSG.Monster.Existence.StdOdd.Cert.ThreeLocal
public import CFSG.Monster.GMS.BabyReduce

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence

open CFSG.Monster.GMS CFSG.Blueprint.NativeSporadic

theorem babyLineOddOrder_of_centralizerFacts
    (hC : StdOdd.CentralizerFacts StdOdd.Rgrp) :
    BabyLineOddOrder :=
  StdOdd.babyLineOddThree_of_std (StdOdd.Cert.stdOddBounds3_std hC)

theorem oddExhaustive_MGriess_of_centralizerFacts
    (I : GMSInterfaces (phiB uBar) MGriess)
    (hC : StdOdd.CentralizerFacts StdOdd.Rgrp) : OddExhaustive tGriess xGriess :=
  oddExhaustive_MGriess_of I
    (lineOddOrder_of I gmsF1Type_MGriess_uncond (babyLineOddOrder_of_centralizerFacts hC))

theorem monsterExistenceStatement_MGriess_of_centralizerFacts
    (hStroth : ∀ d₀ : Blueprint.NativeSporadic.B, orderOf d₀ = 2 →
      Matrix.rank (d₀.val.val - 1) = 1860 →
      ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (d : G), orderOf d = 2 →
        Nonempty (Subgroup.centralizer ({d} : Set G) ≃*
          Subgroup.centralizer ({d₀} : Set Blueprint.NativeSporadic.B)) →
        Nonempty (G ≃* Blueprint.NativeSporadic.B))
    (hC : StdOdd.CentralizerFacts StdOdd.Rgrp) :
    MonsterExistenceStatement MGriess := by
  obtain ⟨-, -, -, -, hcls, hA, -⟩ := monster_existence_clauses_one_two_of_stroth hStroth
  have hSLS : SLSStatement (phiB uBar) :=
    hStroth (phiB uBar) orderOf_phiB_uBar rank_phiB_uBar_sub_one
  exact monsterExistenceStatement_MGriess_of_remaining hStroth
    (oddExhaustive_MGriess_of_centralizerFacts
      (gmsInterfaces_MGriess_of hSLS hcls (hA _ (IsConj.refl _))) hC)

end CFSG.Monster.Existence
