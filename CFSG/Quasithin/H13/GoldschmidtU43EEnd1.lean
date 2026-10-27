module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.GH74.Uniqueness.Statements
public import CFSG.LocalAnalysis.ComponentInitial.AlternatingFourGroup
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.Quasithin.H13.U43

open CFSG.GH74.Uniqueness

variable {G : Type} [Group G]

theorem u43_involutionClosure_normal (G : Type) [Group G] : (involutionClosure G).Normal := by
  refine ⟨fun n hn g => ?_⟩
  have hle : involutionClosure G ≤ (involutionClosure G).comap (MulAut.conj g).toMonoidHom := by
    unfold involutionClosure
    rw [Subgroup.closure_le]
    intro s hs
    refine Subgroup.subset_closure ?_
    show orderOf (g * s * g⁻¹) = 2
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact hs
  exact hle hn

theorem le_involutionClosure_of_simple {X : Subgroup G} (hX : IsSimpleGroup ↥X) {x : G}
    (hx : x ∈ X) (hxo : orderOf x = 2) : X ≤ involutionClosure G := by
  have := u43_involutionClosure_normal G
  have hxL : x ∈ involutionClosure G := Subgroup.subset_closure hxo
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((involutionClosure G).subgroupOf X) with h | h
  · exfalso
    have hmem : (⟨x, hx⟩ : ↥X) ∈ (involutionClosure G).subgroupOf X :=
      Subgroup.mem_subgroupOf.mpr hxL
    rw [h, Subgroup.mem_bot] at hmem
    have hx1 : x = 1 := congrArg Subtype.val hmem
    rw [hx1, orderOf_one] at hxo
    exact absurd hxo (by norm_num)
  · intro t ht
    have : (⟨t, ht⟩ : ↥X) ∈ (involutionClosure G).subgroupOf X := by
      rw [h]
      exact Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp this

theorem two_le_pRank_involutionClosure [Finite G] {x y : G} (hx : orderOf x = 2)
    (hy : orderOf y = 2) (hxy : x * y = y * x) (hne : x ≠ y) :
    2 ≤ CFSG.Open.pRank 2 (involutionClosure G) := by
  obtain ⟨V, hVle, hV, hVcard⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.AlternatingFourGroup.exists_elementary_four_of_commute
      hx hy hxy hne
  have hL : Subgroup.closure ({x, y} : Set G) ≤ involutionClosure G := by
    rw [Subgroup.closure_le]
    intro s hs
    rcases hs with rfl | rfl
    · exact Subgroup.subset_closure hx
    · exact Subgroup.subset_closure hy
  refine le_csSup ⟨Nat.card G, ?_⟩ ⟨V, hVle.trans hL,
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 2 V).mp hV, by rw [hVcard]; norm_num⟩
  rintro r ⟨B, -, -, hB⟩
  calc r ≤ 2 ^ r := (Nat.lt_pow_self (by norm_num)).le
    _ = Nat.card B := hB.symm
    _ ≤ Nat.card G := Subgroup.card_le_card_group B

end CFSG.Quasithin.H13.U43
