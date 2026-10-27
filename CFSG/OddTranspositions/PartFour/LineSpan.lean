module

public import CFSG.OddTranspositions.PartFour.LineTransport

public section

namespace CFSG.OddTranspositions.PartFour

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open CFSG.Timmesfeld.Connectivity

variable {G : Type} [Group G] {D : Set G}

theorem mem_perp_of_mem_blockLine {α β δ ε : Set G} (hα : α ⊆ D) (hβ : β ∈ Dalpha D α)
    (hδ : δ ∈ blockLine D α β) (hε : ε ∈ blockLine D α β) : ε ∈ perp D δ := by
  have hαperp : α ∈ perp D α ∩ perp D β :=
    ⟨mem_perp_iff.mpr (Or.inr rfl), mem_perp_iff.mpr (Or.inl (mem_Dalpha_symm hβ hα))⟩
  have hβperp : β ∈ perp D α ∩ perp D β :=
    ⟨mem_perp_iff.mpr (Or.inl hβ), mem_perp_iff.mpr (Or.inr rfl)⟩
  exact hε.2 δ ⟨hδ.2 α hαperp, hδ.2 β hβperp⟩

theorem mem_Dalpha_of_mem_blockLine {α β δ : Set G} (hα : α ⊆ D) (hβ : β ∈ Dalpha D α)
    (hδ : δ ∈ blockLine D α β) (hne : δ ≠ α) : δ ∈ Dalpha D α := by
  have hαperp : α ∈ perp D α ∩ perp D β :=
    ⟨mem_perp_iff.mpr (Or.inr rfl), mem_perp_iff.mpr (Or.inl (mem_Dalpha_symm hβ hα))⟩
  rcases mem_perp_iff.mp (hδ.2 α hαperp) with h | h
  · exact h
  · exact absurd h hne

theorem blockLine_subset_of_mem {α β δ : Set G} (hα : α ⊆ D) (hδ : δ ∈ blockLine D α β) :
    blockLine D α δ ⊆ blockLine D α β := by
  intro ε hε
  refine ⟨hε.1, ?_⟩
  intro γ hγ
  have hγD : γ ⊆ D := by
    rcases mem_perp_iff.mp hγ.1 with h | rfl
    · exact h.2.1
    · exact hα
  exact hε.2 γ ⟨hγ.1, mem_perp_symm (hδ.2 γ hγ) hγD⟩

variable [Finite G]

theorem blockLine_eq_of_mem (hC : HypothesisC D) {β δ : Set G} (hβ : β ∈ Dalpha D hC.alpha)
    (hδ : δ ∈ Dalpha D hC.alpha) (hδβ : δ ∈ blockLine D hC.alpha β) :
    blockLine D hC.alpha δ = blockLine D hC.alpha β := by
  obtain ⟨g, hgN, hgβ⟩ := hC.normalizer_transitive β hβ δ hδ
  have hgβ' : cimg g β = δ := hgβ
  have hline : blockLine D hC.alpha δ = (cimg g) '' blockLine D hC.alpha β := by
    rw [← blockLine_cimg hC.setup.normal, cimg_eq_self_of_mem_normalizer hgN, hgβ']
  have hcard : (blockLine D hC.alpha δ).ncard = (blockLine D hC.alpha β).ncard := by
    rw [hline, Set.ncard_image_of_injective _ (cimg_injective g)]
  exact Set.eq_of_subset_of_ncard_le (blockLine_subset_of_mem hC.isBlock_alpha.subset hδβ)
    hcard.ge (Set.toFinite _)

theorem blockLine_eq_of_mem_of_mem (hC : HypothesisC D) {β δ ε : Set G}
    (hβ : β ∈ Dalpha D hC.alpha) (hδ : δ ∈ blockLine D hC.alpha β)
    (hε : ε ∈ blockLine D hC.alpha β) (hne : δ ≠ ε) :
    blockLine D δ ε = blockLine D hC.alpha β := by
  by_cases hδα : δ = hC.alpha
  · rw [hδα]
    exact blockLine_eq_of_mem hC hβ
      (mem_Dalpha_of_mem_blockLine hC.isBlock_alpha.subset hβ hε
        (fun h => hne (hδα.trans h.symm))) hε
  by_cases hεα : ε = hC.alpha
  · rw [hεα, blockLine_comm hδ.1]
    exact blockLine_eq_of_mem hC hβ
      (mem_Dalpha_of_mem_blockLine hC.isBlock_alpha.subset hβ hδ hδα) hδ
  have hδDα : δ ∈ Dalpha D hC.alpha :=
    mem_Dalpha_of_mem_blockLine hC.isBlock_alpha.subset hβ hδ hδα
  have hℓδ : blockLine D hC.alpha δ = blockLine D hC.alpha β :=
    blockLine_eq_of_mem hC hβ hδDα hδ
  have hεδα : ε ∈ blockLine D δ hC.alpha := by
    rw [blockLine_comm hδ.1, hℓδ]
    exact hε
  have hαDδ : hC.alpha ∈ Dalpha D δ :=
    mem_Dalpha_symm hδDα hC.isBlock_alpha.subset
  have hεDδ : ε ∈ Dalpha D δ :=
    mem_Dalpha_of_mem_blockLine hδDα.2.1 hαDδ hεδα (Ne.symm hne)
  obtain ⟨g, hgδ⟩ := mem_blockClass_iff.mp hδDα.1
  have hgδ' : cimg g hC.alpha = δ := hgδ.symm
  have hconjα : (hC.conj g).alpha = δ := (HypothesisC.conj_alpha hC g).trans hgδ'
  have hα' : hC.alpha ∈ Dalpha D (hC.conj g).alpha := by rwa [hconjα]
  have hε' : ε ∈ Dalpha D (hC.conj g).alpha := by rwa [hconjα]
  have hεα' : ε ∈ blockLine D (hC.conj g).alpha hC.alpha := by rwa [hconjα]
  have key : blockLine D (hC.conj g).alpha ε = blockLine D (hC.conj g).alpha hC.alpha :=
    blockLine_eq_of_mem (hC.conj g) hα' hε' hεα'
  calc blockLine D δ ε = blockLine D (hC.conj g).alpha ε := by rw [hconjα]
    _ = blockLine D (hC.conj g).alpha hC.alpha := key
    _ = blockLine D δ hC.alpha := by rw [hconjα]
    _ = blockLine D hC.alpha δ := blockLine_comm hδ.1
    _ = blockLine D hC.alpha β := hℓδ

end CFSG.OddTranspositions.PartFour
