module

import CFSG.RankThree.PartTwo.Sec17.Item17Res12ProofNine
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.RankThree.PartTwo.Sec13.Notation
public import CFSG.RankThree.PartTwo.Sec15.Notation
public import CFSG.RankThree.PartTwo.Sec16.Notation

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Late
open scoped commutatorElement

namespace Proof17Res12

variable {G : Type} [Group G] [Finite G]

theorem quaternion_facts :
    (QuaternionGroup.a 1 : QuaternionGroup 2) * QuaternionGroup.xa 0 =
        QuaternionGroup.a 2 * QuaternionGroup.xa 0 * QuaternionGroup.a 1 ∧
      (QuaternionGroup.a 2 : QuaternionGroup 2) ^ 2 = 1 ∧
      (QuaternionGroup.a 2 : QuaternionGroup 2) ≠ 1 ∧
      ∀ x : QuaternionGroup 2, (∀ y : QuaternionGroup 2, y * x = x * y) →
        x = 1 ∨ x = QuaternionGroup.a 2 := by
  decide

omit [Finite G] in
theorem exists_quaternion_elems {R : Subgroup G} (e : ↥R ≃* QuaternionGroup 2) :
    ∃ b₁ ∈ R, ∃ b₂ ∈ R, ∃ z ∈ R, b₁ * b₂ = z * b₂ * b₁ ∧ z ^ 2 = 1 ∧ z ≠ 1 ∧
      ∀ x ∈ (Subgroup.center ↥R).map R.subtype, x = 1 ∨ x = z := by
  obtain ⟨h1, h2, h3, h4⟩ := quaternion_facts
  refine ⟨(e.symm (QuaternionGroup.a 1) : G), (e.symm _).2, (e.symm (QuaternionGroup.xa 0) : G),
    (e.symm _).2, (e.symm (QuaternionGroup.a 2) : G), (e.symm _).2, ?_, ?_, ?_, ?_⟩
  · rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul,
      ← map_mul, h1]
  · rw [← Subgroup.coe_pow, ← map_pow, h2, map_one, Subgroup.coe_one]
  · intro h
    apply h3
    have : e.symm (QuaternionGroup.a 2) = 1 := Subtype.ext (by rw [h, Subgroup.coe_one])
    rw [← e.apply_symm_apply (QuaternionGroup.a 2), this, map_one]
  · rintro _ ⟨x, hx, rfl⟩
    have hcen : ∀ y : QuaternionGroup 2, y * e x = e x * y := by
      intro y
      rw [← e.apply_symm_apply y, ← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hx _)]
    rcases h4 (e x) hcen with h | h
    · left
      have : x = 1 := by rw [← e.symm_apply_apply x, h, map_one]
      rw [this]
      rfl
    · right
      have : x = e.symm (QuaternionGroup.a 2) := by rw [← h, e.symm_apply_apply]
      rw [this]
      rfl

end Proof17Res12

end CFSG.RankThree.PartTwo.Sec17
