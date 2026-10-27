module

import CFSG.RankThree.PartTwo.Sec16.Item16Tail14Tools
import CFSG.RankThree.PartTwo.Sec16.Item16Tail13
import CFSG.RankThree.PartTwo.Sec16.Item16Tail
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.RankThree.PartTwo.Sec16.Proof1613Res

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Sec16.Proof169
  CFSG.RankThree.PartTwo.Sec16.Proof1613 CFSG.RankThree.PartTwo.Sec16.Proof1614 CFSG.GH74.GLS

variable {G : Type} [Group G]

theorem card_sup_eq_nine [Finite G] {A : Subgroup G} (hA : CFSG.Assembly.IsElemAbelian 3 A)
    (hA27 : Nat.card A = 27) {x y : G} (hxA : x ∈ A) (hyA : y ∈ A) (hx1 : x ≠ 1)
    (hyx : y ∉ Subgroup.zpowers x) :
    Nat.card (Subgroup.zpowers x ⊔ Subgroup.zpowers y : Subgroup G) = 9 := by
  have hy1 : y ≠ 1 := by
    rintro rfl
    exact hyx (Subgroup.one_mem _)
  have hx3 := card_zpowers_eq_three (hA.2 x hxA) hx1
  have hy3 := card_zpowers_eq_three (hA.2 y hyA) hy1
  have hxy : x * y = y * x :=
    congrArg Subtype.val (hA.1.is_comm.comm ⟨x, hxA⟩ ⟨y, hyA⟩)
  have hle : Subgroup.zpowers x ⊔ Subgroup.zpowers y ≤ A :=
    sup_le (Subgroup.zpowers_le.mpr hxA) (Subgroup.zpowers_le.mpr hyA)
  have h9 : 9 ≤ Nat.card (Subgroup.zpowers x ⊔ Subgroup.zpowers y : Subgroup G) :=
    nine_le_card_of_lt hle hA27 hx3 (lt_of_le_of_ne le_sup_left fun heq => hyx
      (heq ▸ (le_sup_right : Subgroup.zpowers y ≤ _) (Subgroup.mem_zpowers y)))
  exact le_antisymm (card_sup_zpowers_le hxy hx3 hy3) h9

theorem sup_eq_of_mem [Finite G] {A B : Subgroup G} (hA : CFSG.Assembly.IsElemAbelian 3 A)
    (hA27 : Nat.card A = 27) (hBA : B ≤ A) (hB9 : Nat.card B ≤ 9) {x y : G} (hxB : x ∈ B)
    (hyB : y ∈ B) (hx1 : x ≠ 1) (hyx : y ∉ Subgroup.zpowers x) :
    Subgroup.zpowers x ⊔ Subgroup.zpowers y = B := by
  refine Subgroup.eq_of_le_of_card_ge
    (sup_le (Subgroup.zpowers_le.mpr hxB) (Subgroup.zpowers_le.mpr hyB)) ?_
  rw [card_sup_eq_nine hA hA27 (hBA hxB) (hBA hyB) hx1 hyx]
  exact hB9

theorem exists_zpow_mul_of_mem_sup' {H : Subgroup G} {c : G}
    (hcH : ∀ h ∈ H, h * c = c * h) {y : G} (hy : y ∈ Subgroup.zpowers c ⊔ H) :
    ∃ k : ℤ, ∃ z ∈ H, y = c ^ k * z := by
  have hN : Subgroup.zpowers c ≤ Subgroup.normalizer (H : Set G) := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr hcH)
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hN] at hy
  obtain ⟨w, hw, z, hz, rfl⟩ := hy
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
  exact ⟨k, z, hz, rfl⟩

end CFSG.RankThree.PartTwo.Sec16.Proof1613Res

