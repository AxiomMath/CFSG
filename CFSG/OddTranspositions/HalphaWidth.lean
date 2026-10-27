module

public import CFSG.OddTranspositions.Width
public import CFSG.OddTranspositions.HalphaLocalSecond

public section

namespace CFSG.OddTranspositions

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72

section
variable {G : Type*} [Group G] [Finite G] {D : Set G}

theorem widthLe_DalphaStar_two (hC : HypothesisC D) (hW3 : WidthLe D 3) :
    WidthLe (DalphaStar D hC.alpha) 2 := by
  classical
  intro S hS hcomm
  have hd_not_mem : hC.d ∉ S := by
    intro hdS
    have hdE : hC.d ∈ hC.E := by
      rw [← hC.DalphaStar_alpha]
      exact hS hdS
    have hdα : hC.d ∈ hC.alpha := hC.d_mem_alpha
    rw [hC.alpha_eq_normSet_diff] at hdα
    exact hdα.2 hdE
  have hS'D : (↑(insert hC.d S) : Set G) ⊆ D := by
    intro x hx
    rw [Finset.coe_insert, Set.mem_insert_iff] at hx
    rcases hx with rfl | hx
    · exact hC.isBlock_alpha.subset hC.d_mem_alpha
    · exact DalphaStar_subset hC.isBlock_alpha (hS hx)
  have hS'comm : ∀ x ∈ insert hC.d S, ∀ y ∈ insert hC.d S, x ≠ y → Commute x y := by
    intro x hx y hy hxy
    rw [Finset.mem_insert] at hx hy
    rcases hx with rfl | hx <;> rcases hy with rfl | hy
    · exact absurd rfl hxy
    · exact (hC.DalphaStar_subset_commute (hS hy)).2.symm
    · exact (hC.DalphaStar_subset_commute (hS hx)).2
    · exact hcomm x hx y hy hxy
  have hle := hW3 (insert hC.d S) hS'D hS'comm
  rw [Finset.card_insert_of_notMem hd_not_mem] at hle
  omega

end

section
variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem widthLe_imageClass_two (hC : HypothesisC D) (hW3 : WidthLe D 3) :
    WidthLe (imageClass hC) 2 := by
  classical
  intro T hT hcommT
  let H : Subgroup G := Halpha D hC.alpha
  let R : Subgroup H := CFSG.solvableRadical H
  let mk : H →* H ⧸ R := QuotientGroup.mk' R
  have hmem : ∀ t (ht : t ∈ T), ∃ a ∈ DstarH hC, mk a = t := by
    intro t ht
    have h : t ∈ (QuotientGroup.mk' R) '' DstarH hC := by
      simpa only [imageClass, mk] using hT ht
    exact (Set.mem_image (QuotientGroup.mk' R) (DstarH hC) t).mp h
  let f : {t // t ∈ T} → H := fun t => Classical.choose (hmem t.1 t.2)
  have f_mem : ∀ t : {t // t ∈ T}, f t ∈ DstarH hC := fun t =>
    (Classical.choose_spec (hmem t.1 t.2)).1
  have f_mk : ∀ t : {t // t ∈ T}, mk (f t) = t.1 := fun t =>
    (Classical.choose_spec (hmem t.1 t.2)).2
  set T' : Finset H := T.attach.image f with hT'
  have hT'card : T'.card = T.card := by
    rw [hT']
    have hinj : Set.InjOn f (↑T.attach : Set {t // t ∈ T}) := by
      intro s _ t _ hst
      apply Subtype.ext
      have h := congrArg mk hst
      rwa [f_mk s, f_mk t] at h
    rw [Finset.card_image_of_injOn hinj, Finset.card_attach]
  have hT'mem : ∀ a ∈ T', a ∈ DstarH hC := by
    intro a ha
    rw [hT', Finset.mem_image] at ha
    obtain ⟨t, -, rfl⟩ := ha
    exact f_mem t
  have hT'comm : ∀ a ∈ T', ∀ b ∈ T', a ≠ b → Commute a b := by
    intro a ha b hb hab
    rw [hT', Finset.mem_image] at ha hb
    obtain ⟨s, -, rfl⟩ := ha
    obtain ⟨t, -, rfl⟩ := hb
    have hst : s.1 ≠ t.1 := by
      intro h
      exact hab (by rw [Subtype.ext h])
    refine commute_of_commute_mk_of_ne_H hC (f_mem s) (f_mem t) ?_ ?_
    · rw [f_mk s, f_mk t]
      exact hcommT s.1 s.2 t.1 t.2 hst
    · rw [f_mk s, f_mk t]
      exact hst
  set T'' : Finset G := T'.image (Subtype.val) with hT''
  have hT''card : T''.card = T.card := by
    rw [hT'', Finset.card_image_of_injective _ Subtype.val_injective, hT'card]
  have hT''mem : (↑T'' : Set G) ⊆ DalphaStar D hC.alpha := by
    intro x hx
    simp only [hT'', Finset.mem_coe, Finset.mem_image] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    exact (mem_DstarH_iff hC).mp (hT'mem a ha)
  have hT''comm : ∀ x ∈ T'', ∀ y ∈ T'', x ≠ y → Commute x y := by
    intro x hx y hy hxy
    rw [hT'', Finset.mem_image] at hx hy
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    have hab : a ≠ b := fun h => hxy (by rw [h])
    exact (hT'comm a ha b hb hab).map (Halpha D hC.alpha).subtype
  have hle := widthLe_DalphaStar_two hC hW3 T'' hT''mem hT''comm
  omega

end

end CFSG.OddTranspositions
