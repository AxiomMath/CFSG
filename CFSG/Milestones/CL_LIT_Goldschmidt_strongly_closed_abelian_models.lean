module

public import CFSG.Goldschmidt.ModelConclusion

public section

namespace CFSG.Open

theorem _root_.CFSG.Milestones.cl_lit_goldschmidt_strongly_closed_abelian_models
    (X : Type) [Group X] [Finite X]
    (S : Sylow 2 X) (A : Subgroup X) (hAS : A ≤ S) (hAab : IsMulCommutative A)
    (hclosed : ∀ a ∈ A, ∀ g : X, g⁻¹ * a * g ∈ (S : Subgroup X) → g⁻¹ * a * g ∈ A) :
    let M : Subgroup X := Subgroup.normalClosure (A : Set X)
    let π := QuotientGroup.mk' (goldschmidtOddCore M)
    let T := ((S : Subgroup X).subgroupOf M).map π ⊓ goldschmidtLayer (M ⧸ goldschmidtOddCore M)
    pCore 2 (M ⧸ goldschmidtOddCore M) ⊔ goldschmidtLayer (M ⧸ goldschmidtOddCore M) = ⊤ ∧
    (A.subgroupOf M).map π =
      pCore 2 (M ⧸ goldschmidtOddCore M) ⊔ Subgroup.closure {t | t ∈ T ∧ t ^ 2 = 1} ∧
    ∀ K : Subgroup (M ⧸ goldschmidtOddCore M), IsComponentOf K ⊤ →
      CFSG.Goldschmidt.SimpleModels (K ⧸ Subgroup.center K) :=
  CFSG.Goldschmidt.milestone_models X S A hAS hAab hclosed


end CFSG.Open
