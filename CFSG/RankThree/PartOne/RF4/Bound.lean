module

public import CFSG.RankThree.PartOne.RF4.Graph
import CFSG.LieType.AlgebraicGroups.ConvolutionPoints

public noncomputable section

namespace CFSG.RankThree.PartOne.RF4

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.AlgebraicGroups WithConv TensorProduct

open scoped CFSG.ConvolutionPoints


abbrev reePosCount (t : ReeTag) : ℕ :=
  ((rootFinset t.tag).filter fun v => 0 < height v).card

theorem reeCount_le (t : ReeTag) : t.tag.rank + 2 * reePosCount t ≤ reeM t := by
  cases t
  · have h : Fintype.card (Label Tag.G2) = 14 := by
      rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_of_subtype (rootFinset Tag.G2)
        fun _ => mem_rootFinset]
      decide +kernel
    have h6 : ((rootFinset Tag.G2).filter fun v => 0 < height v).card = 6 := by
      decide +kernel
    change Tag.G2.rank + 2 * ((rootFinset Tag.G2).filter fun v => 0 < height v).card ≤
      Fintype.card (Label Tag.G2)
    rw [h, h6]
    decide
  · have h : Fintype.card (Label Tag.F4) = 52 := by
      rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_of_subtype (rootFinset Tag.F4)
        fun _ => mem_rootFinset]
      decide +kernel
    have h24 : ((rootFinset Tag.F4).filter fun v => 0 < height v).card = 24 := by
      decide +kernel
    change Tag.F4.rank + 2 * ((rootFinset Tag.F4).filter fun v => 0 < height v).card ≤
      Fintype.card (Label Tag.F4)
    rw [h, h24]
    decide

section Count

variable {t : ReeTag}

theorem le_posCount_of_injective_posRoot {n : ℕ} (f : Fin n → Fin t.tag.rank → ℤ)
    (hf : Function.Injective f) (hr : ∀ j, IsRoot t.tag (f j) ∧ 0 < height (f j)) :
    n ≤ reePosCount t :=
  calc n = (Finset.univ.image f).card := by
        rw [Finset.card_image_of_injective _ hf, Finset.card_univ, Fintype.card_fin]
    _ ≤ ((rootFinset t.tag).filter fun v => 0 < height v).card :=
        Finset.card_le_card fun v hv => by
          obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hv
          exact Finset.mem_filter.2 ⟨mem_rootFinset.2 (hr j).1, (hr j).2⟩

theorem rank_add_bruhatParam_le {N : ℕ} {α : Fin N → Fin t.tag.rank → ℤ}
    (hα : Function.Injective α) (hαr : Set.range α = {β | IsRoot t.tag β ∧ 0 < height β})
    {m : ℕ} {β : Fin m → Fin t.tag.rank → ℤ} (hβ : Function.Injective β)
    {w : WeylGroup t.tag} (hβr : Set.range β = inversionSet w) :
    t.tag.rank + (N + m) ≤ reeM t := by
  have hN : N ≤ reePosCount t := le_posCount_of_injective_posRoot α hα fun j => by
    have h : α j ∈ Set.range α := Set.mem_range_self j
    rw [hαr] at h
    exact h
  have hm : m ≤ reePosCount t := le_posCount_of_injective_posRoot β hβ fun j => by
    have h : β j ∈ Set.range β := Set.mem_range_self j
    rw [hβr] at h
    exact ⟨h.1, h.2.1⟩
  have := reeCount_le t
  omega

end Count

section Bound

variable {t : ReeTag} {L : Type} [Field L] [IsAlgClosed L]

theorem finrank_tangentSpace_realizedCoord_le (x : realizedCoord t.tag L →ₐ[L] L) :
    Module.finrank L (TangentSpace L (realizedCoord t.tag L) x) ≤ reeM t := by
  have hreal := isConnectedAlgebraicSubgroup_adjointPointSubgroup t.tag L
  have := hreal.finiteType
  obtain ⟨N, α, hα, hαr⟩ := exists_enum (finite_posRoots t.tag)
  choose m β hβ hβr using fun w : WeylGroup t.tag => exists_enum (inversionSet_finite w)
  obtain ⟨-, -, hcov, -, -, -⟩ := exceptional_Lang_rootword_Bruhat_regular_cover t.tag L
  refine finrank_tangentSpace_quotient_le (subgroupPoints (adjointPointSubgroup t.tag L))
    hreal.pointsZero_eq (fun _ => t.tag.rank) (fun w => N + m w)
    (fun w => bruhatCo t.tag L w α (β w)) ?_
    (fun w => rank_add_bruhatParam_le hα hαr (hβ w) (hβr w)) x
  rw [hcov α hα hαr m β hβ hβr, subgroupPoints_map, transportPoints_modGLPoint]
  rfl

theorem finrank_tangentSpace_reeGraphCoord_le {Φ : MulAut (adjointGroup t.tag L)}
    (hΦ : IsReeExceptional t L Φ) (x : reeGraphCoord t L Φ →ₐ[L] L) :
    Module.finrank L (TangentSpace L (reeGraphCoord t L Φ) x) ≤ reeM t := by
  have hreal := reeGraph_realization (t := t) (L := L) hΦ
  have := hreal.2.1.finiteType
  have := hreal.2.1.isDomain
  have := hreal.2.2.1
  obtain ⟨N, α, hα, hαr⟩ := exists_enum (finite_posRoots t.tag)
  choose m β hβ hβr using fun w : WeylGroup t.tag => exists_enum (inversionSet_finite w)
  obtain ⟨-, -, -, hgraph, -, -⟩ := exceptional_Lang_rootword_Bruhat_regular_cover t.tag L
  obtain ⟨ν, -, hcov, -, -⟩ := hgraph (reeM t) (reeGraphHom t Φ) (reeGraphHom_regular_x hΦ)
    (reeGraphHom_regular_y hΦ)
  refine finrank_tangentSpace_quotient_le (subgroupPoints (graphPointSubgroup (reeGraphHom t Φ)))
    hreal.2.1.pointsZero_eq (fun _ => t.tag.rank) (fun w => N + m w)
    (fun w => Algebra.TensorProduct.productMap (bruhatCo t.tag L w α (β w)) (ν w α (β w))) ?_
    (fun w => rank_add_bruhatParam_le hα hαr (hβ w) (hβr w)) x
  rw [hcov α hα hαr m β hβ hβr, subgroupPoints_map, transportPoints_graphSubgroup]
  rfl

end Bound

end CFSG.RankThree.PartOne.RF4
