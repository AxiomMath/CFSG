module

public import CFSG.LocalAnalysis.StandardType.FF81.CentE6.XFusion

public section

namespace CFSG.StandardType.FF81.CentE6

open scoped MatrixGroups

private theorem stdTransvection_sq :
    CFSG.Holt.SL6.stdTransvection * CFSG.Holt.SL6.stdTransvection = 1 := by
  have h2 : (1 : ZMod 2) + 1 = 0 := by decide
  rw [CFSG.Holt.SL6.stdTransvection,
    ← Matrix.SpecialLinearGroup.transvection_add (i := 0) (j := 5) (by decide) (1 : ZMod 2) 1, h2,
    Matrix.SpecialLinearGroup.transvection_coeff_zero]

private theorem stdTransvection_ne_one : CFSG.Holt.SL6.stdTransvection ≠ 1 := by
  intro h
  have hh := congrArg (fun g : SL(6, ZMod 2) => (g : Matrix (Fin 6) (Fin 6) (ZMod 2)) 0 5) h
  rw [CFSG.Holt.SL6.coe_stdTransvection] at hh
  simp at hh

private theorem orderOf_stdTransvection : orderOf CFSG.Holt.SL6.stdTransvection = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (by rw [pow_two]; exact stdTransvection_sq) stdTransvection_ne_one

private theorem Sone_ne_Ssix : Sone ≠ Ssix := by
  intro h
  have h2 : Subgroup.zpowers CFSG.Holt.SL6.stdTransvection = Sone := by
    rw [← Sone_inf_Ssix, h, inf_idem]
  have hcard : Nat.card (Subgroup.zpowers CFSG.Holt.SL6.stdTransvection) = 32 := by
    rw [h2, card_Sone]
  rw [Nat.card_zpowers, orderOf_stdTransvection] at hcard
  norm_num at hcard

private theorem img_hom_injective {X : Type} [Group X] (S : CubeSetting X) :
    Function.Injective (S.L.subtype.comp S.eL.symm.toMonoidHom) := by
  intro a b hab
  exact S.eL.symm.injective (Subtype.ext hab)

private theorem img_Sone_ne_img_Ssix {X : Type} [Group X] (S : CubeSetting X) :
    S.img Sone ≠ S.img Ssix := by
  intro h
  apply Sone_ne_Ssix
  refine Subgroup.map_injective (f := S.L.subtype.comp S.eL.symm.toMonoidHom)
    (img_hom_injective S) ?_
  simpa only [CubeSetting.img] using h

private theorem map_conj_img_eq_Sone_or_Ssix {X : Type} [Group X] (S : CubeSetting X)
    {c : X} (hnorm : ∀ x ∈ S.img Sgrp, c * x * c⁻¹ ∈ S.img Sgrp)
    {A : Subgroup SL(6, ZMod 2)} (hA : A ≤ Sgrp) (hAcard : Nat.card A = 32)
    (hAT : ∀ g ∈ A, g ≠ 1 → IsTransvec g) :
    (S.img A).map (MulAut.conj c).toMonoidHom = S.img Sone ∨
      (S.img A).map (MulAut.conj c).toMonoidHom = S.img Ssix := by
  let φ : SL(6, ZMod 2) →* X := S.L.subtype.comp S.eL.symm.toMonoidHom
  have hφinj : Function.Injective φ := img_hom_injective S
  let E1 : Subgroup X := (S.img A).map (MulAut.conj c).toMonoidHom
  have hE1le : E1 ≤ S.img Sgrp := by
    refine (Subgroup.map_mono (Subgroup.map_mono hA)).trans ?_
    rw [Subgroup.map_le_iff_le_comap]
    intro x hx
    exact hnorm x hx
  have hE1card : Nat.card E1 = 32 := by
    show Nat.card ((S.img A).map (MulAut.conj c).toMonoidHom) = 32
    rw [Subgroup.card_map_of_injective (MulAut.conj c).injective]
    change Nat.card (A.map φ) = 32
    rw [Subgroup.card_map_of_injective hφinj, hAcard]
  have hE1range : E1 ≤ φ.range :=
    hE1le.trans (Subgroup.map_le_range (f := φ) Sgrp)
  let E1' : Subgroup SL(6, ZMod 2) := E1.comap φ
  have hE1'map : E1'.map φ = E1 := Subgroup.map_comap_eq_self hE1range
  have hE1'sub : E1' ≤ Sgrp := by
    intro g hg
    have hgE1 : φ g ∈ E1 := hg
    rcases Subgroup.mem_map.mp (hE1le hgE1) with ⟨s, hs, hsφ⟩
    have : s = g := hφinj hsφ
    simpa [this] using hs
  have hE1'card : Nat.card E1' = 32 := by
    have h1 : Nat.card (E1'.map φ) = Nat.card E1' := Subgroup.card_map_of_injective hφinj
    rw [hE1'map, hE1card] at h1
    exact h1.symm
  have hE1'T : ∀ g ∈ E1', g ≠ 1 → IsTransvec g := by
    intro g hg hg1
    have hgE1 : φ g ∈ E1 := hg
    rcases Subgroup.mem_map.mp hgE1 with ⟨x, hx, hxφ⟩
    rcases Subgroup.mem_map.mp hx with ⟨s, hs, hsφ⟩
    have hφg : φ g = c * φ s * c⁻¹ := by
      rw [← hxφ, ← hsφ]
      rfl
    have hs1 : s ≠ 1 := by
      intro hs1
      refine hg1 (hφinj ?_)
      rw [hφg, hs1]
      simp
    have hconj_s : IsConj S.z (φ s) := by
      have := MonoidHom.map_isConj φ (isConj_of_isTransvec (hAT s hs hs1))
      simpa [φ, CubeSetting.z] using this
    have hconj_g : IsConj S.z (φ g) :=
      hconj_s.trans (isConj_iff.mpr ⟨c, hφg.symm⟩)
    have hxSL : φ g ∈ S.L := by
      rcases Subgroup.mem_map.mp (hE1le hgE1) with ⟨s', _, hs'⟩
      rw [← hs']
      exact (S.eL.symm s').2
    have htrans := isTransvec_eL_of_isConj S hxSL hconj_g
    have hsub : (⟨φ g, hxSL⟩ : ↥S.L) = S.eL.symm g := Subtype.ext rfl
    rw [hsub] at htrans
    simpa using htrans
  rcases eq_Sone_or_eq_Ssix_of_transvec (E := E1') hE1'sub hE1'card hE1'T with h | h
  · left
    change E1 = S.img Sone
    rw [← hE1'map, h]
    rfl
  · right
    change E1 = S.img Ssix
    rw [← hE1'map, h]
    rfl

theorem conj_img_Sone_or_Ssix {X : Type} [Group X] [Finite X] (S : CubeSetting X) {c : X}
    (hnorm : ∀ x ∈ S.img Sgrp, c * x * c⁻¹ ∈ S.img Sgrp) :
    ((∀ x ∈ S.img Sone, c * x * c⁻¹ ∈ S.img Sone) ∧
        (∀ y ∈ S.img Ssix, c * y * c⁻¹ ∈ S.img Ssix)) ∨
      ((∀ x ∈ S.img Sone, c * x * c⁻¹ ∈ S.img Ssix) ∧
        (∀ y ∈ S.img Ssix, c * y * c⁻¹ ∈ S.img Sone)) := by
  have hTone : ∀ g ∈ Sone, g ≠ 1 → IsTransvec g := fun g hg hg1 =>
    (isTransvec_iff_of_mem_Sgrp ((le_sup_left : Sone ≤ Sgrp) hg) hg1).mpr (Or.inl hg)
  have hTsix : ∀ g ∈ Ssix, g ≠ 1 → IsTransvec g := fun g hg hg1 =>
    (isTransvec_iff_of_mem_Sgrp ((le_sup_right : Ssix ≤ Sgrp) hg) hg1).mpr (Or.inr hg)
  have hE1 := map_conj_img_eq_Sone_or_Ssix S hnorm (A := Sone) le_sup_left card_Sone hTone
  have hE6 := map_conj_img_eq_Sone_or_Ssix S hnorm (A := Ssix) le_sup_right card_Ssix hTsix
  have hAB : S.img Sone ≠ S.img Ssix := img_Sone_ne_img_Ssix S
  have hinj : Function.Injective (Subgroup.map (MulAut.conj c).toMonoidHom) :=
    Subgroup.map_injective (MulAut.conj c).injective
  rcases hE1 with h1 | h1 <;> rcases hE6 with h6 | h6
  · exfalso
    exact hAB (hinj (h1.trans h6.symm))
  · left
    constructor
    · intro x hx
      have hx' : c * x * c⁻¹ ∈ (S.img Sone).map (MulAut.conj c).toMonoidHom :=
        Subgroup.mem_map_of_mem _ hx
      rwa [h1] at hx'
    · intro y hy
      have hy' : c * y * c⁻¹ ∈ (S.img Ssix).map (MulAut.conj c).toMonoidHom :=
        Subgroup.mem_map_of_mem _ hy
      rwa [h6] at hy'
  · right
    constructor
    · intro x hx
      have hx' : c * x * c⁻¹ ∈ (S.img Sone).map (MulAut.conj c).toMonoidHom :=
        Subgroup.mem_map_of_mem _ hx
      rwa [h1] at hx'
    · intro y hy
      have hy' : c * y * c⁻¹ ∈ (S.img Ssix).map (MulAut.conj c).toMonoidHom :=
        Subgroup.mem_map_of_mem _ hy
      rwa [h6] at hy'
  · exfalso
    exact hAB (hinj (h1.trans h6.symm))

end CFSG.StandardType.FF81.CentE6
