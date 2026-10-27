module

public import CFSG.LocalAnalysis.StandardType.GGA11CohDefs
public import CFSG.Assembly.Subnormal
public import CFSG.LocalAnalysis.ComponentClassification.LocalComponents

public section

open CFSG CFSG.Assembly CFSG.StandardType Matrix CFSG.LieType.Universal
  CFSG.LieType.Universal.SpecialLinear

namespace CFSG.StandardType.A11

theorem a11CompEqInput_holds :
    ∀ (G : Type) [Group G] [Finite G] (X A A' : Subgroup G) (g : G), IsComponentOf A X →
      IsComponentOf A' X → g ∈ A → g ∈ A' → g ≠ 1 → Subgroup.center ↥A = ⊥ → A = A' := by
  intro G _ _ X A A' g hA hA' hgA hgA' hg1 hz
  by_contra hne
  have hA0 : CFSG.Open.IsComponentOf (A.subgroupOf X) ⊤ := by
    refine ⟨le_top, ?_, ?_⟩
    · exact CFSG.Open.IsSubnormal.top_iff.mpr (CFSG.Assembly.IsSubnormal.subgroupOf hA.2.1)
    · exact CFSG.ComponentClassification.Components.quasisimple_of_equiv
        (Subgroup.subgroupOfEquivOfLe hA.1) hA.2.2
  have hA1 : CFSG.Open.IsComponentOf (A'.subgroupOf X) ⊤ := by
    refine ⟨le_top, ?_, ?_⟩
    · exact CFSG.Open.IsSubnormal.top_iff.mpr (CFSG.Assembly.IsSubnormal.subgroupOf hA'.2.1)
    · exact CFSG.ComponentClassification.Components.quasisimple_of_equiv
        (Subgroup.subgroupOfEquivOfLe hA'.1) hA'.2.2
  have hne0 : A.subgroupOf X ≠ A'.subgroupOf X := by
    intro heq
    apply hne
    have hmap := congrArg (Subgroup.map X.subtype) heq
    rwa [Subgroup.map_subgroupOf_eq_of_le hA.1,
      Subgroup.map_subgroupOf_eq_of_le hA'.1] at hmap
  have hcomm : ⁅A.subgroupOf X, A'.subgroupOf X⁆ = ⊥ :=
    CFSG.ComponentClassification.LocalComponents.commute_of_ne
      (A.subgroupOf X) (A'.subgroupOf X) hA0 hA1 hne0
  have hle : A.subgroupOf X ≤ Subgroup.centralizer (A'.subgroupOf X : Set ↥X) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm
  have hcomm_elem : ∀ a ∈ A, ∀ b ∈ A', a * b = b * a := by
    intro a ha b hb
    have hmem : (⟨a, hA.1 ha⟩ : ↥X) ∈ Subgroup.centralizer (A'.subgroupOf X : Set ↥X) :=
      hle (show (⟨a, hA.1 ha⟩ : ↥X) ∈ A.subgroupOf X from ha)
    have hb' : (⟨b, hA'.1 hb⟩ : ↥X) ∈ A'.subgroupOf X := hb
    exact congrArg Subtype.val
      (((Subgroup.mem_centralizer_iff.1 hmem) ⟨b, hA'.1 hb⟩ hb').symm)
  have hcenter : (⟨g, hgA⟩ : ↥A) ∈ Subgroup.center ↥A := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨a, ha⟩ := y
    exact Subtype.ext (hcomm_elem a ha g hgA')
  have hgbot : (⟨g, hgA⟩ : ↥A) = 1 := by
    have hmem := hcenter
    rw [hz] at hmem
    exact Subgroup.mem_bot.mp hmem
  exact hg1 (congrArg Subtype.val hgbot)

end CFSG.StandardType.A11

end
