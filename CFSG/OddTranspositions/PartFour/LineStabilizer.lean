module

public import CFSG.OddTranspositions.PartFour.LineSpan
public import CFSG.OddTranspositions.PartFour.SeventeenTwo

public section

namespace CFSG.OddTranspositions.PartFour

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open CFSG.Timmesfeld.Connectivity

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem cimg_mem_blockLine_of_mem_Malpha (h113 : PartThree.Theorem11_3) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    {β ε : Set G} (hβ : β ∈ Dalpha D hC.alpha) (hε : ε ∈ blockLine D hC.alpha β) {x : G}
    (hx : x ∈ Malpha D hC.alpha) :
    cimg x ε ∈ blockLine D hC.alpha β := by
  have hx' : x ∈ (CFSG.solvableRadical (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype := by
    simpa [Malpha] using hx
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx'
  by_cases hεα : ε = hC.alpha
  · have hfix : cimg ((Halpha D hC.alpha).subtype y) hC.alpha = hC.alpha :=
      cimg_eq_self_of_mem_normalizer (Halpha_le_normalizer_block D hC.alpha y.2)
    rw [hεα, hfix]
    exact left_mem_blockLine hC.isBlock_alpha.subset
  · have hεD : ε ∈ Dalpha D hC.alpha :=
      mem_Dalpha_of_mem_blockLine hC.isBlock_alpha.subset hβ hε hεα
    have h := conj_mem_blockLine h113 hC hrad hn3 hεD hy
    rw [blockLine_eq_of_mem hC hβ hεD hε] at h
    simpa [cimg] using h

theorem exists_mem_normalizer_cimg_eq (hC : HypothesisC D) {β δ : Set G}
    (hβ : β ∈ Dalpha D hC.alpha) (hδ : δ ∈ blockLine D hC.alpha β) (hne : δ ≠ hC.alpha) :
    ∃ g ∈ Subgroup.normalizer hC.alpha, cimg g β = δ ∧
      (cimg g) '' blockLine D hC.alpha β = blockLine D hC.alpha β := by
  have hδ' : δ ∈ Dalpha D hC.alpha :=
    mem_Dalpha_of_mem_blockLine hC.isBlock_alpha.subset hβ hδ hne
  obtain ⟨g, hg, hgβ⟩ := hC.normalizer_transitive β hβ δ hδ'
  have hgβ' : cimg g β = δ := hgβ
  refine ⟨g, hg, hgβ', ?_⟩
  rw [← blockLine_cimg hC.setup.normal g hC.alpha β,
    cimg_eq_self_of_mem_normalizer hg, hgβ',
    blockLine_eq_of_mem hC hβ hδ' hδ]

theorem exists_mem_normalizer_cimg_eq' (hC : HypothesisC D) {β δ : Set G}
    (hβ : β ∈ Dalpha D hC.alpha) (hδ : δ ∈ blockLine D hC.alpha β) (hne : δ ≠ β) :
    ∃ g ∈ Subgroup.normalizer β, cimg g hC.alpha = δ ∧
      (cimg g) '' blockLine D hC.alpha β = blockLine D hC.alpha β := by
  obtain ⟨k, hk⟩ := mem_blockClass_iff.mp hβ.1
  have hα' : (hC.conj k).alpha = β := by
    rw [HypothesisC.conj_alpha]
    exact hk.symm
  have hαD : hC.alpha ∈ Dalpha D (hC.conj k).alpha := by
    rw [hα']
    exact mem_Dalpha_symm hβ hC.isBlock_alpha.subset
  have hδ' : δ ∈ blockLine D (hC.conj k).alpha hC.alpha := by
    rw [hα', blockLine_comm hβ.1]
    exact hδ
  have hne' : δ ≠ (hC.conj k).alpha := by
    rw [hα']
    exact hne
  obtain ⟨g, hg, hgα, hℓ⟩ :=
    exists_mem_normalizer_cimg_eq (hC.conj k) hαD hδ' hne'
  refine ⟨g, ?_, hgα, ?_⟩
  · rwa [hα'] at hg
  · rwa [hα', blockLine_comm hβ.1] at hℓ

theorem exists_cimg_eq_alpha_of_mem_blockLine (hC : HypothesisC D) {β ε : Set G}
    (hβ : β ∈ Dalpha D hC.alpha) (hε : ε ∈ blockLine D hC.alpha β)
    (h2 : 2 < (blockLine D hC.alpha β).encard) :
    ∃ g : G, cimg g hC.alpha = ε ∧
      (cimg g) '' blockLine D hC.alpha β = blockLine D hC.alpha β := by
  by_cases hεα : ε = hC.alpha
  · refine ⟨1, by rw [hεα, cimg_one], ?_⟩
    ext S
    simp [cimg]
  · by_cases hεβ : ε = β
    · subst ε
      have hαneβ : hC.alpha ≠ β := (Dalpha.ne_self hβ).symm
      have hγ : ∃ γ ∈ blockLine D hC.alpha β, γ ≠ hC.alpha ∧ γ ≠ β := by
        by_contra hno
        push Not at hno
        have hsub : blockLine D hC.alpha β ⊆ ({hC.alpha, β} : Set (Set G)) := by
          intro γ hγ
          rw [Set.mem_insert_iff, Set.mem_singleton_iff]
          by_cases hγα : γ = hC.alpha
          · exact Or.inl hγα
          · exact Or.inr (hno γ hγ hγα)
        have hle := Set.encard_le_encard hsub
        have hpair : ({hC.alpha, β} : Set (Set G)).encard = 2 := Set.encard_pair hαneβ
        have hlt : (2 : ℕ∞) < (2 : ℕ∞) := by
          calc (2 : ℕ∞) < (blockLine D hC.alpha β).encard := h2
            _ ≤ ({hC.alpha, β} : Set (Set G)).encard := hle
            _ = 2 := hpair
        exact (lt_irrefl (2 : ℕ∞)) hlt
      obtain ⟨γ, hγℓ, hγα, hγβ⟩ := hγ
      obtain ⟨g₁, -, hg₁α, hg₁ℓ⟩ :=
        exists_mem_normalizer_cimg_eq' hC hβ hγℓ hγβ
      obtain ⟨g₂, -, hg₂β, hg₂ℓ⟩ :=
        exists_mem_normalizer_cimg_eq hC hβ hγℓ hγα
      refine ⟨g₂⁻¹ * g₁, ?_, ?_⟩
      · rw [cimg_mul, hg₁α, ← hg₂β, cimg_inv_cimg]
      · rw [← image_cimg_mul, hg₁ℓ]
        calc (cimg g₂⁻¹) '' blockLine D hC.alpha β =
            (cimg g₂⁻¹) '' ((cimg g₂) '' blockLine D hC.alpha β) := by rw [hg₂ℓ]
          _ = blockLine D hC.alpha β := image_cimg_inv_cimg g₂ _
    · obtain ⟨g, -, hgα, hgℓ⟩ := exists_mem_normalizer_cimg_eq' hC hβ hε hεβ
      exact ⟨g, hgα, hgℓ⟩

theorem exists_cimg_eq_of_mem_blockLine (h89 : PartThree.Lemma8_9)
    (h113 : PartThree.Theorem11_3) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hW : ¬ ∃ f n : ℕ, 2 ≤ f ∧ Nonempty (G ≃* L2Wreath f n))
    (hn3 : ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hMZ : ¬ CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    {β δ ε : Set G} (hβ : β ∈ Dalpha D hC.alpha) (hδ : δ ∈ blockLine D hC.alpha β)
    (hε : ε ∈ blockLine D hC.alpha β) :
    ∃ g : G, cimg g δ = ε ∧ (cimg g) '' blockLine D hC.alpha β = blockLine D hC.alpha β := by
  have h2 : 2 < (blockLine D hC.alpha β).encard :=
    two_lt_encard_blockLine h89 h113 hC hrad hW hn3 hMZ hβ
  obtain ⟨gδ, hgδα, hgδℓ⟩ :=
    exists_cimg_eq_alpha_of_mem_blockLine hC hβ hδ h2
  obtain ⟨gε, hgεα, hgεℓ⟩ :=
    exists_cimg_eq_alpha_of_mem_blockLine hC hβ hε h2
  have hδα : cimg gδ⁻¹ δ = hC.alpha := by
    rw [← hgδα, cimg_inv_cimg]
  have hδℓ : (cimg gδ⁻¹) '' blockLine D hC.alpha β = blockLine D hC.alpha β := by
    calc (cimg gδ⁻¹) '' blockLine D hC.alpha β =
        (cimg gδ⁻¹) '' ((cimg gδ) '' blockLine D hC.alpha β) := by rw [hgδℓ]
      _ = blockLine D hC.alpha β := image_cimg_inv_cimg gδ _
  refine ⟨gε * gδ⁻¹, ?_, ?_⟩
  · rw [cimg_mul, hδα, hgεα]
  · rw [← image_cimg_mul, hδℓ, hgεℓ]

end CFSG.OddTranspositions.PartFour
