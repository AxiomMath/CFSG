module

public import CFSG.RankThree.PartOne.HNB.F25
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.ComponentInitial.LinearUnitaryField

public section

namespace CFSG.Quasithin.H13.KGU35

open CFSG.RankThree.PartOne.HNB CFSG.LocalAnalysis.ComponentInitial

@[expose] def Star5 {G : Type*} [Group G] (x : G) : Prop :=
  ∃ a b : G, x = a * b * a⁻¹ * b⁻¹ ∧
    ∀ g ∈ Subgroup.closure ({a, b} : Set G), g ^ 5 = 1 ∧ g * x = x * g

theorem f25Data : UnitaryFieldData 5 1 F25 :=
  ⟨by norm_num, le_rfl, by rw [F25.card]; norm_num⟩

end CFSG.Quasithin.H13.KGU35
