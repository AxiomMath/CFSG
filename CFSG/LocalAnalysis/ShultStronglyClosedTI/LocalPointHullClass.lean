module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionGeometryEmbedding

public section

namespace CFSG.ShultStronglyClosedTI

open CFSG.Open CFSG.BenderSuzuki
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open scoped Pointwise

universe u

variable {G : Type u} [Group G]

theorem localPointHullClass_eq_conjugatesOf (z : G) :
    involutionPointClass z = conjugatesOf z := by
  ext x
  constructor
  · rintro ⟨g, rfl⟩
    exact isConj_iff.mpr ⟨g⁻¹, by simp [rightConjugateElem]⟩
  · intro hx
    obtain ⟨g, hg⟩ := isConj_iff.mp hx
    exact ⟨g⁻¹, by simpa [rightConjugateElem] using hg⟩

theorem localPointHull_eq_closure_conjugatesOf (z : G) :
    involutionPointHull z = Subgroup.closure (conjugatesOf z) := by
  rw [involutionPointHull, localPointHullClass_eq_conjugatesOf]

theorem localPointHull_distinguished_mem (z : G) : z ∈ involutionPointHull z :=
  Subgroup.subset_closure (distinguished_mem_pointClass z)

variable [Finite G]

theorem localPointHull_pair_flip_nonempty {H : Subgroup G} {z : G}
    (h : InvolutionPointLocalEmbedding H z) (beta : rightCosetSpace H)
    (hbeta : beta ≠ rightCosetMk H 1) :
    (rightPairFlipFiber H z beta).Nonempty := by
  have hpositive : 0 < Nat.card (rightPairFlipFiber H z beta) := by
    rw [(involution_point_uniform_pair_flips h beta hbeta).1]
    let : Nonempty (conjugacyWithin H z) :=
      ⟨⟨z, ⟨1, by simp⟩⟩⟩
    exact Nat.card_pos
  obtain ⟨t, ht⟩ := (Nat.card_pos_iff.mp hpositive).1
  exact ⟨t, ht⟩

theorem localPointHull_base_coset_reached {H : Subgroup G} {z : G}
    (h : InvolutionPointLocalEmbedding H z) (beta : rightCosetSpace H) :
    ∃ l : involutionPointHull z,
      rightCosetTranslate H (rightCosetMk H 1) (l : G) = beta := by
  classical
  by_cases hbeta : beta = rightCosetMk H 1
  · exact ⟨1, by simpa only [Subgroup.coe_one, rightCosetTranslate_one] using hbeta.symm⟩
  · obtain ⟨t, ht⟩ := localPointHull_pair_flip_nonempty h beta hbeta
    exact ⟨⟨t, Subgroup.subset_closure ht.1⟩, ht.2⟩

theorem localPointHull_right_coset_transitive {H : Subgroup G} {z : G}
    (h : InvolutionPointLocalEmbedding H z) :
    ∀ alpha beta : rightCosetSpace H, ∃ l : involutionPointHull z,
      rightCosetTranslate H alpha (l : G) = beta := by
  intro alpha beta
  obtain ⟨a, ha⟩ := localPointHull_base_coset_reached h alpha
  obtain ⟨b, hb⟩ := localPointHull_base_coset_reached h beta
  refine ⟨a⁻¹ * b, ?_⟩
  change rightCosetTranslate H alpha ((a : G)⁻¹ * (b : G)) = beta
  rw [← ha, rightCosetTranslate_mul, mul_inv_cancel_left]
  exact hb

theorem localPointHull_group_eq_point_mul {H : Subgroup G} {z : G}
    (h : InvolutionPointLocalEmbedding H z) :
    (Set.univ : Set G) = (H : Set G) * (involutionPointHull z : Set G) := by
  ext g
  constructor
  · intro _
    obtain ⟨l, hl⟩ := localPointHull_base_coset_reached h (rightCosetMk H g)
    have hcoset : rightCosetMk H (l : G) = rightCosetMk H g := by
      simpa only [rightCosetTranslate_mk, one_mul] using hl
    have hrel : QuotientGroup.rightRel H (l : G) g := Quotient.exact hcoset
    rw [QuotientGroup.rightRel_apply] at hrel
    exact Set.mem_mul.mpr
      ⟨g * (l : G)⁻¹, hrel, l, l.property, inv_mul_cancel_right g (l : G)⟩
  · intro _
    trivial

theorem localPointHull_pair_products_le_intersection {H : Subgroup G} {z : G}
    (h : InvolutionPointLocalEmbedding H z) (beta : rightCosetSpace H)
    (hbeta : beta ≠ rightCosetMk H 1) (t₀ : G)
    (ht₀ : t₀ ∈ rightPairFlipFiber H z beta) :
    rightPairFlipProducts H z beta t₀ ⊆
      (H ⊓ involutionPointHull z : Subgroup G) := by
  intro k hk
  have hstabilizer := ((involution_point_uniform_pair_flips h beta hbeta).2.2 t₀ ht₀).1 hk
  rw [rightCosetStabilizer_base] at hstabilizer
  refine ⟨hstabilizer.1, ?_⟩
  obtain ⟨t, ht, rfl⟩ := hk
  exact (involutionPointHull z).mul_mem
    (Subgroup.subset_closure ht.1) (Subgroup.subset_closure ht₀.1)

theorem localPointHull_point_eq_centralizer_mul {H : Subgroup G} {z : G}
    (h : InvolutionPointLocalEmbedding H z) :
    (H : Set G) = (Subgroup.centralizer ({z} : Set G) : Set G) *
      (H ⊓ involutionPointHull z : Subgroup G) := by
  classical
  obtain ⟨a, ha⟩ : ∃ a : G, a ∉ H := by
    by_contra hnone
    apply h.proper
    apply top_unique
    intro a _
    by_contra ha
    exact hnone ⟨a, ha⟩
  let beta := rightCosetMk H a
  have hbeta : beta ≠ rightCosetMk H 1 := by
    intro heq
    have hrel : QuotientGroup.rightRel H a 1 := Quotient.exact heq
    rw [QuotientGroup.rightRel_apply] at hrel
    exact ha (H.inv_mem_iff.mp (by simpa only [one_mul] using hrel))
  obtain ⟨t₀, ht₀⟩ := localPointHull_pair_flip_nonempty h beta hbeta
  have htransversal := ((involution_point_uniform_pair_flips h beta hbeta).2.2 t₀ ht₀).2
  have hproducts := localPointHull_pair_products_le_intersection h beta hbeta t₀ ht₀
  ext b
  constructor
  · intro hb
    obtain ⟨k, hk, _⟩ := htransversal (⟨b, hb⟩ : H)
    have hdiff : (k : G) * b⁻¹ ∈ Subgroup.centralizer ({z} : Set G) :=
      (mem_rightCoset_iff b).mp hk
    have hc : b * (k : G)⁻¹ ∈ Subgroup.centralizer ({z} : Set G) := by
      simpa only [mul_inv_rev, inv_inv] using
        (Subgroup.centralizer ({z} : Set G)).inv_mem hdiff
    exact Set.mem_mul.mpr
      ⟨b * (k : G)⁻¹, hc, k, hproducts k.property, inv_mul_cancel_right b (k : G)⟩
  · intro hb
    obtain ⟨c, hc, k, hk, rfl⟩ := Set.mem_mul.mp hb
    exact H.mul_mem (point_centralizer_le h hc) hk.1

theorem localPointHull_group_eq_centralizer_mul {H : Subgroup G} {z : G}
    (h : InvolutionPointLocalEmbedding H z) :
    (Set.univ : Set G) = (Subgroup.centralizer ({z} : Set G) : Set G) *
      (involutionPointHull z : Set G) := by
  ext g
  constructor
  · intro _
    have hg : g ∈ (H : Set G) * (involutionPointHull z : Set G) := by
      rw [← localPointHull_group_eq_point_mul h]
      trivial
    obtain ⟨a, ha, l, hl, hal⟩ := Set.mem_mul.mp hg
    rw [localPointHull_point_eq_centralizer_mul h] at ha
    obtain ⟨c, hc, k, hk, hck⟩ := Set.mem_mul.mp ha
    exact Set.mem_mul.mpr
      ⟨c, hc, k * l, (involutionPointHull z).mul_mem hk.2 hl,
        by rw [← mul_assoc, hck, hal]⟩
  · intro _
    trivial

theorem localPointHull_pointClass_eq_internal_class {H : Subgroup G} {z : G}
    (h : InvolutionPointLocalEmbedding H z) :
    let L := involutionPointHull z
    let zL : L := ⟨z, localPointHull_distinguished_mem z⟩
    involutionPointClass z = L.subtype '' involutionPointClass zL := by
  let L := involutionPointHull z
  let zL : L := ⟨z, localPointHull_distinguished_mem z⟩
  ext t
  constructor
  · rintro ⟨g, rfl⟩
    have hg : g ∈ (Subgroup.centralizer ({z} : Set G) : Set G) * (L : Set G) := by
      rw [← localPointHull_group_eq_centralizer_mul h]
      trivial
    obtain ⟨c, hc, l, hl, hcl⟩ := Set.mem_mul.mp hg
    let lL : L := ⟨l, hl⟩
    refine ⟨rightConjugateElem zL lL, ⟨lL, rfl⟩, ?_⟩
    have hfix : c⁻¹ * z * c = z := by
      have hh := (right_conjugates_eq_iff (z := z) (a := c) (b := 1)).mpr
        (by
          change c * (1 : G)⁻¹ ∈ (Subgroup.centralizer ({z} : Set G) : Set G)
          simpa only [inv_one, mul_one] using hc)
      simpa only [inv_one, one_mul, mul_one] using hh
    change l⁻¹ * z * l = g⁻¹ * z * g
    calc
      l⁻¹ * z * l = l⁻¹ * (c⁻¹ * z * c) * l := by rw [hfix]
      _ = (c * l)⁻¹ * z * (c * l) := by simp only [mul_inv_rev, mul_assoc]
      _ = g⁻¹ * z * g := by rw [hcl]
  · rintro ⟨t, ⟨l, rfl⟩, rfl⟩
    exact ⟨(l : G), rfl⟩

theorem localPointHull_conjugatesOf_eq_internal_class {H : Subgroup G} {z : G}
    (h : InvolutionPointLocalEmbedding H z) :
    let L := involutionPointHull z
    let zL : L := ⟨z, localPointHull_distinguished_mem z⟩
    conjugatesOf z = L.subtype '' conjugatesOf zL := by
  dsimp only
  rw [← localPointHullClass_eq_conjugatesOf z,
    ← localPointHullClass_eq_conjugatesOf]
  exact localPointHull_pointClass_eq_internal_class h

theorem localPointHull_eq_closure_internal_class {H : Subgroup G} {z : G}
    (h : InvolutionPointLocalEmbedding H z) :
    let L := involutionPointHull z
    let zL : L := ⟨z, localPointHull_distinguished_mem z⟩
    L = Subgroup.closure (L.subtype '' conjugatesOf zL) := by
  dsimp only
  rw [← localPointHull_conjugatesOf_eq_internal_class h]
  exact localPointHull_eq_closure_conjugatesOf z

theorem localPointHull_internal_class_generates {H : Subgroup G} {z : G}
    (h : InvolutionPointLocalEmbedding H z) :
    let L := involutionPointHull z
    let zL : L := ⟨z, localPointHull_distinguished_mem z⟩
    Subgroup.closure (conjugatesOf zL) = (⊤ : Subgroup L) := by
  let L := involutionPointHull z
  apply Subgroup.map_injective (f := L.subtype) Subtype.val_injective
  rw [MonoidHom.map_closure, Subgroup.map_top, Subgroup.range_subtype,
    ← localPointHull_conjugatesOf_eq_internal_class h]
  exact (localPointHull_eq_closure_conjugatesOf z).symm

theorem localPointHull_internal_normalClosure_top {H : Subgroup G} {z : G}
    (h : InvolutionPointLocalEmbedding H z) :
    let L := involutionPointHull z
    let zL : L := ⟨z, localPointHull_distinguished_mem z⟩
    Subgroup.normalClosure ({zL} : Set L) = ⊤ := by
  let L := involutionPointHull z
  let zL : L := ⟨z, localPointHull_distinguished_mem z⟩
  change Subgroup.normalClosure ({zL} : Set L) = ⊤
  have hclass : Group.conjugatesOfSet ({zL} : Set L) = conjugatesOf zL := by
    ext x
    rw [Group.mem_conjugatesOfSet_iff]
    change (∃ a, a ∈ ({zL} : Set L) ∧ IsConj a x) ↔ IsConj zL x
    simp only [Set.mem_singleton_iff, exists_eq_left]
  change Subgroup.closure (Group.conjugatesOfSet ({zL} : Set L)) = ⊤
  rw [hclass]
  exact localPointHull_internal_class_generates h

theorem involution_point_hull_controls_class {H : Subgroup G} {z : G}
    (h : InvolutionPointLocalEmbedding H z) :
    let L := involutionPointHull z
    let zL : L := ⟨z, localPointHull_distinguished_mem z⟩
    L = Subgroup.closure (conjugatesOf z) ∧
    (∀ alpha beta : rightCosetSpace H, ∃ l : L,
      rightCosetTranslate H alpha (l : G) = beta) ∧
    (Set.univ : Set G) = (H : Set G) * (L : Set G) ∧
    (H : Set G) = (Subgroup.centralizer ({z} : Set G) : Set G) *
      (H ⊓ L : Subgroup G) ∧
    (Set.univ : Set G) = (Subgroup.centralizer ({z} : Set G) : Set G) * (L : Set G) ∧
    conjugatesOf z = L.subtype '' conjugatesOf zL ∧
    L = Subgroup.closure (L.subtype '' conjugatesOf zL) ∧
    Subgroup.closure (conjugatesOf zL) = (⊤ : Subgroup L) ∧
    Subgroup.normalClosure ({zL} : Set L) = ⊤ := by
  exact ⟨localPointHull_eq_closure_conjugatesOf z,
    localPointHull_right_coset_transitive h, localPointHull_group_eq_point_mul h,
    localPointHull_point_eq_centralizer_mul h, localPointHull_group_eq_centralizer_mul h,
    localPointHull_conjugatesOf_eq_internal_class h, localPointHull_eq_closure_internal_class h,
    localPointHull_internal_class_generates h, localPointHull_internal_normalClosure_top h⟩

end CFSG.ShultStronglyClosedTI
