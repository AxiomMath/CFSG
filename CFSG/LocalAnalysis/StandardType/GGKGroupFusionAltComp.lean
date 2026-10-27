module

public import CFSG.LocalAnalysis.StandardType.GGKGroupFusionAltCount
public import CFSG.Assembly.Defs
public import Mathlib.GroupTheory.Subgroup.Centralizer

public section

namespace CFSG.StandardType

open Equiv Equiv.Perm

section Quasisimple

open scoped commutatorElement

theorem ggCenter_eq_bot_of_simple {G : Type*} [Group G] [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) : Subgroup.center G = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    exact hab ((Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b)) a)

theorem ggIsQuasisimple_of_simple {G : Type*} [Group G] [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) : CFSG.Assembly.IsQuasisimple G := by
  have hc := ggCenter_eq_bot_of_simple hnab
  refine ⟨?_, ?_⟩
  · rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator G) with h | h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      apply hab
      have hmem : ⁅a, b⁆ ∈ commutator G := Subgroup.commutator_mem_commutator
        (Subgroup.mem_top a) (Subgroup.mem_top b)
      rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
      exact hmem
    · exact h
  · have e : G ⧸ Subgroup.center G ≃* G :=
      (QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot
    exact (MulEquiv.isSimpleGroup_congr e).mpr inferInstance

end Quasisimple

section Comp

variable {V : Type} [DecidableEq V] [Fintype V] {N : Subgroup (Perm V)}

omit [Fintype V] in
theorem ggAltOn_nonabelian {X : Finset V} (hX : 4 ≤ X.card) :
    ∃ a b : ↥(GGAltOn X), a * b ≠ b * a := by
  have hnc : ¬ IsMulCommutative ↥(alternatingGroup (Fin X.card)) := by
    rw [alternatingGroup.isMulCommutative_iff_card_le_three]
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin]
    omega
  by_contra h
  push Not at h
  apply hnc
  refine ⟨⟨fun a b => ?_⟩⟩
  apply (ggAltOnMulEquiv X).symm.injective
  rw [map_mul, map_mul]
  exact h _ _

omit [Fintype V] in
theorem ggImage_image_mul (X : Finset V) (g h : Perm V) :
    (X.image g).image h = X.image (h * g) := by
  rw [Finset.image_image]
  rfl

@[expose] noncomputable def ggAltTranslates (N : Subgroup (Perm V)) (X : Finset V) :
    Subgroup (Perm V) :=
  ⨆ g : ↥N, GGAltOn (X.image (g : Perm V))

theorem ggIsSubnormal_altOn {X : Finset V} (hX : GGAbsorbing N X) :
    CFSG.Assembly.IsSubnormal (GGAltOn X) N := by
  set A := ggAltTranslates N X with hAdef
  have hAN : A ≤ N := iSup_le fun g => ggAltOn_le_of_altIn (hX.image g.2).2.1
  have hXA : GGAltOn X ≤ A := by
    refine le_trans (le_of_eq ?_) (le_iSup _ (1 : ↥N))
    congr 1
    ext v
    simp
  have hAnorm : A ≤ Subgroup.normalizer (GGAltOn X : Set (Perm V)) := by
    refine iSup_le fun g => ?_
    rcases GGAbsorbing.eq_or_disjoint (hX.image g.2) hX with h | h
    · rw [h]
      exact Subgroup.le_normalizer
    · intro b hb
      apply Subgroup.centralizer_le_normalizer
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      exact ggAltOn_commute_of_disjoint h.symm ha hb
  have hconj : ∀ m ∈ N, ∀ a ∈ A, m * a * m⁻¹ ∈ A := by
    intro m hm a ha
    refine Subgroup.iSup_induction (C := fun a => m * a * m⁻¹ ∈ A) _ ha ?_ ?_ ?_
    · intro g b hb
      have h1 := ggConj_mem_altOn hb m
      rw [ggImage_image_mul] at h1
      exact le_iSup (fun g : ↥N => GGAltOn (X.image (g : Perm V))) ⟨m * g, N.mul_mem hm g.2⟩ h1
    · simp
    · intro x y hx hy
      have := A.mul_mem hx hy
      simpa [mul_assoc] using this
  have hNnorm : N ≤ Subgroup.normalizer (A : Set (Perm V)) := by
    intro m hm
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · exact hconj m hm h
    · intro hh
      have := hconj m⁻¹ (N.inv_mem hm) _ hh
      simpa [mul_assoc] using this
  exact .step hXA ((Subgroup.normal_subgroupOf_iff_le_normalizer hXA).mpr hAnorm)
    (.step hAN ((Subgroup.normal_subgroupOf_iff_le_normalizer hAN).mpr hNnorm) (.refl N))

theorem ggIsComponentOf_altOn {X : Finset V} (hX : GGAbsorbing N X) (h5 : 5 ≤ X.card) :
    CFSG.Assembly.IsComponentOf (GGAltOn X) N := by
  have : IsSimpleGroup ↥(GGAltOn X) := ggAltOn_isSimpleGroup h5
  exact ⟨ggAltOn_le_of_altIn hX.2.1, ggIsSubnormal_altOn hX,
    ggIsQuasisimple_of_simple (ggAltOn_nonabelian (by omega))⟩

end Comp

end CFSG.StandardType
