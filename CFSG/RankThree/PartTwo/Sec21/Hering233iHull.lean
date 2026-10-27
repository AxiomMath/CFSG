module

import CFSG.GroupTheory.ConjugatePairSubnormality
public import CFSG.RankThree.PartTwo.Sec21.Item233Pieces
public import CFSG.RankThree.PartTwo.Sec6.Item65Tools

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.RankThreeEven (projSL)

variable {G : Type} [Group G]

namespace Hering233i

theorem le_or_commute_inf [Finite G] {H J : Subgroup G} {X : Subgroup (J ⊓ H : Subgroup G)}
    (hX : IsComponent X) {X₀ : Subgroup G} (hX₀ : X₀ ∈ thetaComponentsIn H) :
    X.map (J ⊓ H).subtype ≤ X₀ ∨
      ∀ x ∈ X.map (J ⊓ H).subtype, ∀ y ∈ X₀ ⊓ J, x * y = y * x := by
  obtain ⟨hX₀H, hX₀θ⟩ := mem_thetaComponentsIn_iff.mp hX₀
  have hsn : (X₀.subgroupOf (J ⊓ H)).IsSubnormal :=
    CFSG.GroupTheory.isSubnormal_subgroupOf_of_le inf_le_right hX₀θ.2.1
  rcases CFSG.LocalCores.component_subnormal_subgroup hX hsn with h | h
  · left
    rintro _ ⟨x, hx, rfl⟩
    exact Subgroup.mem_subgroupOf.mp (h hx)
  · right
    rintro _ ⟨x, hx, rfl⟩ y hy
    have hy' : (⟨y, ⟨hy.2, hX₀H hy.1⟩⟩ : (J ⊓ H : Subgroup G)) ∈ X₀.subgroupOf (J ⊓ H) :=
      Subgroup.mem_subgroupOf.mpr hy.1
    have hc := Subgroup.commutator_mem_commutator hx hy'
    rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
    exact congrArg Subtype.val hc

theorem map_conj_mem_thetaComponentsIn_of_mem_normalizer [Finite G] {B : Subgroup G}
    (hB3 : Nat.card B = 3) {g : G} (hg : g ∈ Subgroup.normalizer (B : Set G)) {Y : Subgroup G}
    (hY : Y ∈ thetaComponentsIn (Subgroup.centralizer (B : Set G))) :
    Y.map (MulAut.conj g).toMonoidHom ∈ thetaComponentsIn (Subgroup.centralizer (B : Set G)) := by
  have hB1 : B ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hB3
    omega
  obtain ⟨⟨b, hbB⟩, hb'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hB1
  have hb1 : b ≠ 1 := fun h => hb' (Subtype.ext h)
  have hBb : B = Subgroup.zpowers b := eq_zpowers_of_card_three hB3 hbB hb1
  have hgb : g * b * g⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.mp hg b).mp hbB
  have hgb1 : g * b * g⁻¹ ≠ 1 := by
    intro h
    apply hb1
    have := congrArg (fun y => g⁻¹ * y * g) h
    simpa [mul_assoc] using this
  have hBgb : B = Subgroup.zpowers (g * b * g⁻¹) := eq_zpowers_of_card_three hB3 hgb hgb1
  have hY' : Y ∈ thetaComponentsAt 3 b := by
    rw [thetaComponentsAt_eq_thetaComponentsIn, ← Sec6.centralizer_zpowers_eq, ← hBb]
    exact hY
  have h := map_mem_thetaComponentsAt (MulAut.conj g) hY'
  rw [thetaComponentsAt_eq_thetaComponentsIn, ← Sec6.centralizer_zpowers_eq b] at hY'
  have h2 : Y.map (MulAut.conj g).toMonoidHom ∈ thetaComponentsAt 3 (g * b * g⁻¹) := by
    simpa using h
  rw [thetaComponentsAt_eq_thetaComponentsIn, ← Sec6.centralizer_zpowers_eq, ← hBgb] at h2
  exact h2

end Hering233i

end CFSG.RankThree.PartTwo.Sec21
