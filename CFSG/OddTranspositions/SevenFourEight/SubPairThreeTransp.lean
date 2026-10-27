module

public import CFSG.OddTranspositions.SevenFourEight.SecondKindConclusion
public import CFSG.OddTranspositions.SevenFourEight.O4Triangle
public import CFSG.OddTranspositions.TheoremTwo.ImageConnected

public section

namespace CFSG.OddTranspositions

open CFSG.Timmesfeld.Bridge Asc72 CFSG.Timmesfeld.Connectivity
open CFSG.OddTranspositions.QZ

theorem threeTransp_conjSet_of_secondKind
    {Y : Type} [Group Y] [Finite Y] {Θ : Set Y} (hS : Setup Y Θ)
    (hsec : ∀ x y t : Y, IsTriangle Θ x y t → orderOf (x * t * y) = 4)
    {M₀ : Subgroup Y} [M₀.Normal] (hM₀ : IsSimpleGroup M₀)
    (hCM₀ : Subgroup.centralizer (M₀ : Set Y) = ⊥) {x : Y} (hx : x ∈ Θ)
    (hcls : IsOddTranspClass (conjSet M₀ x)) {m : ℕ} (hmin : SmallerTwoStar m)
    (hcard : Nat.card ↥(M₀ ⊔ Subgroup.zpowers x) < m) :
    ∀ a ∈ conjSet M₀ x, ∀ b ∈ conjSet M₀ x, orderOf (a * b) ∈ ({1, 2, 3} : Set ℕ) := by
  classical
  have hx2 : x * x = 1 := hS.oddT.mul_self_eq_one hx
  have hM1 : M₀ ≠ ⊥ := (Subgroup.nontrivial_iff_ne_bot M₀).mp inferInstance
  have hMK : M₀ ≤ M₀ ⊔ Subgroup.zpowers x := le_sup_left
  have hΛΘ : ∀ y ∈ conjSet M₀ x, (y : Y) ∈ Θ := by
    rintro y ⟨g, -, hy⟩
    rw [hy]
    exact hS.normal g x hx
  obtain ⟨hΛcls, hΛodd, hΛgen⟩ := hcls
  have hSΛ : Setup ↥(M₀ ⊔ Subgroup.zpowers x) (conjSet M₀ x) := ⟨hΛcls, hΛodd, hΛgen⟩
  have hradK := solvable_normal_eq_bot_of_le hMK hM₀ hCM₀ hM1
  have hsecΛ : ∀ a b c : ↥(M₀ ⊔ Subgroup.zpowers x), IsTriangle (conjSet M₀ x) a b c →
      orderOf (a * c * b) = 4 := by
    intro a b c htri
    obtain ⟨ha, hc, hb, hac, hcac, hcab, hccb⟩ := htri
    have h := hsec a b c ⟨hΛΘ a ha, hΛΘ c hc, hΛΘ b hb, fun h => hac (Subtype.ext h),
      commute_coe_iff_of_subgroup.mpr hcac, fun h => hcab (commute_coe_iff_of_subgroup.mp h),
      fun h => hccb (commute_coe_iff_of_subgroup.mp h)⟩
    rw [← Subgroup.orderOf_coe]
    simpa using h
  have hLΛ : LocalSecond (conjSet M₀ x) := localSecond_of_forall_secondKind hsecΛ
  have hnsΛ := not_meetsSq_of_secondKind hSΛ hradK hsecΛ
  have hM0 : Asc72.IsMinimalNormal (M₀.subgroupOf (M₀ ⊔ Subgroup.zpowers x)) :=
    isMinimalNormal_subgroupOf hMK hM₀
  have hidx : (M₀.subgroupOf (M₀ ⊔ Subgroup.zpowers x)).index ≤ 2 :=
    relIndex_sup_zpowers_le_two hx2
  have hconn : ¬ Disconnected (conjSet M₀ x) := by
    intro hdisc
    obtain ⟨M', -, -, huniq, -, -, hidx', -⟩ :=
      almostSimpleCase_of_disconnected hSΛ hradK hLΛ hnsΛ hdisc
    rw [← huniq _ hM0] at hidx'
    omega
  rcases hmin _ _ hcard hSΛ hconn hradK hLΛ with h | h
  · exact h
  · obtain ⟨a, b, c, htri, hne⟩ := exists_triangle_ne_four_of_o4PairData h
    exact (hne (hsecΛ a b c htri)).elim

end CFSG.OddTranspositions

end
