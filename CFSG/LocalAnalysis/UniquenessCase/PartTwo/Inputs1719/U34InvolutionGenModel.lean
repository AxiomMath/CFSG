module

public import CFSG.GH74.KGroups.FieldGF
public import CFSG.RankThree.PartTwo.KFacts.AutPSU
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryTransvectionGeneration

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.ClassicalGroups.UnitaryFlag CFSG.GH74.KGroups CFSG.LocalAnalysis.ComponentInitial
open CFSG.RankThree.PartTwo.KFacts

theorem unitaryFieldData_GF16 : UnitaryFieldData 2 2 GF16 :=
  ⟨Nat.prime_two, by norm_num, by rw [Nat.card_eq_fintype_card]; rfl⟩

@[expose] def U34InvGenInner : Prop :=
  ∃ t x₁ x₂ : unitarySU 2 2 GF16 3, t * t = 1 ∧ t ≠ 1 ∧
    Subgroup.closure {t * x₁⁻¹ * t * x₁, t * x₂⁻¹ * t * x₂} = ⊤

@[expose] def U34InvGenOuter : Prop :=
  ∃ y₁ y₂ : unitarySU 2 2 GF16 3,
    Subgroup.closure
      {(suField unitaryFieldData_GF16 unitaryFieldData_GF16.barEquiv y₁)⁻¹ * y₁,
        (suField unitaryFieldData_GF16 unitaryFieldData_GF16.barEquiv y₂)⁻¹ * y₂} = ⊤

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
