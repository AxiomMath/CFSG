module

public import CFSG.LocalAnalysis.StandardType.GGKGroupFusionAltOn

public section

namespace CFSG.StandardType

open Equiv Equiv.Perm

section Sat

variable {V : Type} [DecidableEq V] {N : Subgroup (Perm V)}

theorem ggAltIn_triple {a b c : V} (h : GGContains3 N a b c) (hab : a ≠ b) (hbc : b ≠ c)
    (hac : a ≠ c) : GGAltIn N {a, b, c} := by
  have r1 := h.rot hab hbc hac
  have r2 := r1.rot hbc hac.symm hab.symm
  have f0 := h.flip hab hbc hac
  have f1 := f0.rot hac hbc.symm hab
  have f2 := f1.rot hbc.symm hab.symm hac.symm
  intro u hu v hv w hw huv hvw huw
  simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv hw
  rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl <;>
    rcases hw with rfl | rfl | rfl <;>
    (first | exact (huv rfl).elim | exact (hvw rfl).elim | exact (huw rfl).elim | assumption)

@[expose] def GGAbsorbing (N : Subgroup (Perm V)) (X : Finset V) : Prop :=
  3 ≤ X.card ∧ GGAltIn N X ∧
    ∀ Y : Finset V, 3 ≤ Y.card → GGAltIn N Y → (X ∩ Y).Nonempty → Y ⊆ X

variable [Fintype V]

open Classical in
theorem ggExists_absorbing {X₀ : Finset V} (h3 : 3 ≤ X₀.card) (hX₀ : GGAltIn N X₀) :
    ∃ X, X₀ ⊆ X ∧ GGAbsorbing N X := by
  set S : Finset (Finset V) :=
    Finset.univ.filter (fun X => X₀ ⊆ X ∧ 3 ≤ X.card ∧ GGAltIn N X) with hS
  have hne : S.Nonempty := ⟨X₀, by simp [hS, h3, hX₀]⟩
  obtain ⟨X, hXS, hmax⟩ := S.exists_maximal hne
  simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and] at hXS
  obtain ⟨hX₀X, hX3, hX⟩ := hXS
  refine ⟨X, hX₀X, hX3, hX, fun Y hY3 hY hXY => ?_⟩
  have hU : X ∪ Y ∈ S := by
    simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hX₀X.trans Finset.subset_union_left,
      hX3.trans (Finset.card_le_card Finset.subset_union_left),
      ggAltIn_union hX hY hX3 hY3 hXY⟩
  exact Finset.subset_union_right.trans (hmax hU Finset.subset_union_left)

omit [Fintype V] in
theorem GGAbsorbing.eq_or_disjoint {X Y : Finset V} (hX : GGAbsorbing N X)
    (hY : GGAbsorbing N Y) : X = Y ∨ Disjoint X Y := by
  by_cases h : (X ∩ Y).Nonempty
  · left
    refine le_antisymm (hY.2.2 X hX.1 hX.2.1 ?_) (hX.2.2 Y hY.1 hY.2.1 h)
    rwa [Finset.inter_comm]
  · right
    rw [Finset.not_nonempty_iff_eq_empty] at h
    exact Finset.disjoint_iff_inter_eq_empty.mpr h

omit [Fintype V] in
theorem GGAbsorbing.image {X : Finset V} (hX : GGAbsorbing N X) {g : Perm V} (hg : g ∈ N) :
    GGAbsorbing N (X.image g) := by
  refine ⟨by rw [Finset.card_image_of_injective _ g.injective]; exact hX.1,
    ggAltIn_image hX.2.1 hg, fun Y hY3 hY hXY => ?_⟩
  have hY' : GGAltIn N (Y.image ⇑(g⁻¹ : Perm V)) := ggAltIn_image hY (N.inv_mem hg)
  have hY3' : 3 ≤ (Y.image ⇑(g⁻¹ : Perm V)).card := by
    rw [Finset.card_image_of_injective _ (g⁻¹).injective]; exact hY3
  have hmeet : (X ∩ Y.image ⇑(g⁻¹ : Perm V)).Nonempty := by
    obtain ⟨v, hv⟩ := hXY
    rw [Finset.mem_inter, Finset.mem_image] at hv
    obtain ⟨⟨w, hw, rfl⟩, hwY⟩ := hv
    exact ⟨w, Finset.mem_inter.mpr ⟨hw, Finset.mem_image.mpr ⟨g w, hwY, by simp⟩⟩⟩
  have hsub := hX.2.2 _ hY3' hY' hmeet
  intro v hv
  rw [Finset.mem_image]
  exact ⟨g⁻¹ v, hsub (Finset.mem_image.mpr ⟨v, hv, rfl⟩), by simp⟩

end Sat

end CFSG.StandardType
