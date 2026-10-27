module

public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.K1320.Struct

public section

namespace CFSG.RankThree.PartOne.Q1327

open CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.Sec1322Fin CFSG.RankThree.PartOne.Sec1322
  CFSG.RankThree.PartOne.K1320

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

set_option maxRecDepth 100000

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
theorem gp_conn1 : ∀ a b z : Gp, (isT a ∨ isV' a) → (isT b ∨ isV' b) → (a * b) ^ 4 = 1 →
    (a * b) ^ 2 ≠ 1 → (isT z ∨ isV' z) → a * z = z * a → b * z = z * b → z ≠ a → z ≠ b →
    z ≠ a * b * a⁻¹ → z ≠ b * a * b⁻¹ → (∃ g : Gp, g * b * g⁻¹ = z) →
    ∀ x : Gp, (∃ g : Gp, g * a * g⁻¹ = x) →
      x = a ∨ a * x ≠ x * a ∨ ∃ u : Gp, (∃ g : Gp, g * a * g⁻¹ = u) ∧ a * u ≠ u * a ∧
        x * u ≠ u * x := by
  decide +kernel

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
theorem gp_conn2 : ∀ a b z : Gp, (isT' a ∨ isV' a) → (isT' b ∨ isV' b) → (a * b) ^ 4 = 1 →
    (a * b) ^ 2 ≠ 1 → (isT' z ∨ isV' z) → a * z = z * a → b * z = z * b → z ≠ a → z ≠ b →
    z ≠ a * b * a⁻¹ → z ≠ b * a * b⁻¹ → (∃ g : Gp, g * b * g⁻¹ = z) →
    ∀ x : Gp, (∃ g : Gp, g * a * g⁻¹ = x) →
      x = a ∨ a * x ≠ x * a ∨ ∃ u : Gp, (∃ g : Gp, g * a * g⁻¹ = u) ∧ a * u ≠ u * a ∧
        x * u ≠ u * x := by
  decide +kernel

end CFSG.RankThree.PartOne.Q1327
