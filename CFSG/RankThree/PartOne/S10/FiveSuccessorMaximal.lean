module

import CFSG.RankThree.PartOne.S10.ThetaNodesUnconditional
public import CFSG.LocalAnalysis.ComponentInitial.KProperPumpUpStatement
public import CFSG.RankThree.PartOne.S10.Defs

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.GroupTheory
  CFSG.LocalAnalysis.ComponentInitial

theorem exists_forall_rel_symm_of_refl_trans {α : Type*} [Finite α] (r : α → α → Prop)
    {B : Set α} (hrefl : ∀ x ∈ B, r x x)
    (htrans : ∀ x ∈ B, ∀ y ∈ B, ∀ z ∈ B, r x y → r y z → r x z) (hB : B.Nonempty) :
    ∃ L ∈ B, ∀ Y ∈ B, r L Y → r Y L := by
  obtain ⟨L, hLB, hmin⟩ := Set.exists_min_image B (fun x => {z | z ∈ B ∧ r x z}.ncard)
    B.toFinite hB
  refine ⟨L, hLB, fun Y hY hLY => ?_⟩
  by_contra hYL
  have hsub : {z | z ∈ B ∧ r Y z} ⊂ {z | z ∈ B ∧ r L z} := by
    refine ⟨fun z hz => ⟨hz.1, htrans L hLB Y hY z hz.1 hLY hz.2⟩, fun h => ?_⟩
    exact hYL (h ⟨hLB, hrefl L hLB⟩).2
  exact absurd (hmin Y hY) (not_le.mpr (Set.ncard_lt_ncard hsub (Set.toFinite _)))

theorem exists_five_maximal_nonquasisimple (hS : SchreierFor InCatalog) {G : Type} [Group G]
    [Finite G] {A : Subgroup G} (hS10 : SteinbergBM.SectionTenSetup G 5 A)
    (hne : ∃ L ∈ sectionTenZero 5 A, ¬ CFSG.IsQuasisimple L) :
    ∃ L ∈ sectionTenZero 5 A, ¬ CFSG.IsQuasisimple L ∧
      ∀ Y ∈ sectionTenZero 5 A, ¬ CFSG.IsQuasisimple Y → sectionTenRel 5 L Y →
        sectionTenRel 5 Y L := by
  obtain ⟨hsimple, hnonab, hK, -, -, -, hAe, -, -, -⟩ := id hS10
  have : IsSimpleGroup G := hsimple
  have hp : (5 : ℕ).Prime := by norm_num
  have he : evenRank G ≤ 3 := (sectionTenSetup_evenRank_eq hS10).le
  have hAe' : IsElementaryAbelian 5 A := hAe
  obtain ⟨L₀, hL₀, hL₀q⟩ := hne
  obtain ⟨L, ⟨hLZ, hLq⟩, hmax⟩ := exists_forall_rel_symm_of_refl_trans (sectionTenRel 5)
    (B := {Y | Y ∈ sectionTenZero 5 A ∧ ¬ CFSG.IsQuasisimple Y})
    (fun x _ => sectionTenRel_refl 5 x)
    (fun x hx y hy z hz hxy hyz => section_ten_component_supplement_transitivity hS G hnonab hK
      he 5 hp (by norm_num) A hAe' x hx.1.1 y hy.1.1 z hz.1.1 hxy hyz) ⟨L₀, hL₀, hL₀q⟩
  exact ⟨L, hLZ, hLq, fun Y hY hYq => hmax Y ⟨hY, hYq⟩⟩

end CFSG.RankThree.PartOne
