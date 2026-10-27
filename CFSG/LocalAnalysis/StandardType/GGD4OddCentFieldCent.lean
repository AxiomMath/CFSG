module

public import CFSG.LocalAnalysis.StandardType.GGD4OddCentFieldReduce
import CFSG.LocalAnalysis.StandardType.GGD4OddCentFieldFixed
import CFSG.LocalAnalysis.StandardType.GGD4OddCentFieldBridge
import CFSG.LocalAnalysis.StandardType.GGRecipeFieldOmegaConjLabels
import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorComponents

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section Helpers

theorem gdt_fixed_conj {R : Type*} [Group R] (c f : MulAut R) :
    ggAutFixedSubgroup (c * f * c⁻¹) = (ggAutFixedSubgroup f).map c.toMonoidHom := by
  ext x
  rw [mem_ggAutFixedSubgroup, Subgroup.mem_map]
  constructor
  · intro h
    refine ⟨c⁻¹ x, ?_, by simp⟩
    rw [mem_ggAutFixedSubgroup]
    apply c.injective
    simpa [MulAut.mul_apply, MulAut.inv_apply] using h
  · rintro ⟨y, hy, rfl⟩
    rw [mem_ggAutFixedSubgroup] at hy
    simp [MulAut.mul_apply, MulAut.inv_apply, hy]

theorem gdt_conj_mul_conj_mul_inv {R : Type*} [Group R] (φ : MulAut R) (x : R) :
    φ * MulAut.conj x * φ⁻¹ = MulAut.conj (φ x) := by
  ext y
  simp [MulAut.mul_apply, MulAut.inv_apply]

theorem gdt_conj_mul_eq {R : Type*} [Group R] (j r : R) (g : MulAut R) :
    MulAut.conj (j * r * (g r⁻¹)) =
      MulAut.conj j * MulAut.conj r * g * (MulAut.conj r)⁻¹ * g⁻¹ := by
  rw [show MulAut.conj (j * r * (g r⁻¹)) =
      MulAut.conj j * MulAut.conj r * MulAut.conj (g r⁻¹) by simp only [map_mul]]
  rw [← gdt_conj_mul_conj_mul_inv g r⁻¹, map_inv]
  group

theorem gdt_innField_of_stab {R : Type} [Group R] {F : Set (MulAut R)} {f' : MulAut R}
    (hf' : f' ∈ F) {r : R}
    (hstab : ∀ β : MulAut R,
      (∀ x ∈ ggAutFixedSubgroup f', β x = x) → β ∈ Subgroup.zpowers f')
    {a : MulAut R} {j : R}
    (hj : ∀ x ∈ ggAutFixedSubgroup (MulAut.conj r * f' * (MulAut.conj r)⁻¹),
      a x = j * x * j⁻¹) :
    GGInnField (LargeEvenInnSet R) F a := by
  set b : MulAut R := (MulAut.conj j)⁻¹ * a with hb
  have hb_fix : ∀ x ∈ ggAutFixedSubgroup (MulAut.conj r * f' * (MulAut.conj r)⁻¹),
      b x = x := by
    intro x hx
    rw [hb, MulAut.mul_apply, MulAut.inv_apply, hj x hx]
    simp only [MulAut.conj_symm_apply]
    group
  set β : MulAut R := (MulAut.conj r)⁻¹ * b * MulAut.conj r with hβ
  have hfix : ggAutFixedSubgroup (MulAut.conj r * f' * (MulAut.conj r)⁻¹) =
      (ggAutFixedSubgroup f').map (MulAut.conj r).toMonoidHom :=
    gdt_fixed_conj (MulAut.conj r) f'
  have hβ_fix : ∀ y ∈ ggAutFixedSubgroup f', β y = y := by
    intro y hy
    have hcy : (MulAut.conj r) y ∈
        ggAutFixedSubgroup (MulAut.conj r * f' * (MulAut.conj r)⁻¹) := by
      rw [hfix, Subgroup.mem_map]
      exact ⟨y, hy, rfl⟩
    calc
      β y = (MulAut.conj r)⁻¹ (b ((MulAut.conj r) y)) := by
        simp only [hβ, MulAut.mul_apply]
      _ = (MulAut.conj r)⁻¹ ((MulAut.conj r) y) := by
        rw [hb_fix ((MulAut.conj r) y) hcy]
      _ = y := MulAut.inv_apply_self R (MulAut.conj r) y
  have hβ_zp : β ∈ Subgroup.zpowers f' := hstab β hβ_fix
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hβ_zp
  have hb_eq : b = MulAut.conj r * f' ^ i * (MulAut.conj r)⁻¹ := by
    rw [hi, hβ]
    group
  have ha_form : a = MulAut.conj j * (MulAut.conj r * f' ^ i * (MulAut.conj r)⁻¹) := by
    rw [← hb_eq, hb]
    group
  refine ⟨MulAut.conj (j * r * ((f' ^ i) r⁻¹)), ⟨j * r * ((f' ^ i) r⁻¹), rfl⟩,
    f' ^ i, Subgroup.zpow_mem (Subgroup.closure F) (Subgroup.subset_closure hf') i, ?_⟩
  rw [ha_form, gdt_conj_mul_eq j r (f' ^ i)]
  group

end Helpers

section Cent


theorem ggD4FieldCentralizerInput_holds : GGD4FieldCentralizerInput := by
  intro K _ _ n hK _ s hs3 hinn hout J hJ
  obtain ⟨hs, hna⟩ := d4Recipe_isSimpleGroup K
  haveI : CharP K 2 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : Fintype K := Fintype.ofFinite K
    refine charP_of_card_eq_prime_pow (p := 2) (f := n) ?_
    rw [← Nat.card_eq_fintype_card]
    exact hK
  obtain ⟨u, hu, f, hf, hsuf⟩ := hinn
  have huf : u * f ∉ LargeEvenInnSet (D4Recipe K) := by
    rw [← hsuf]
    exact hout
  have hpow : (u * f) ^ 3 = 1 := by
    rw [← hsuf]
    exact hs3
  obtain ⟨f', hf'F, u', hu'I, hf'3, heq⟩ :=
    (RecipeFieldOmega.ggRawFieldConj_omegaPlus (K := K) (m := 4) (hm3 := by norm_num)
      (p := 3) (hp := by norm_num) (hp2 := by norm_num)) hs hna u hu f hf huf hpow
  obtain ⟨r, hr⟩ := hu'I
  have hs_eq : s = MulAut.conj r * f' * (MulAut.conj r)⁻¹ := by
    rw [hsuf, heq, hr]
  obtain ⟨k, _, _, n', hcard, hn, ⟨ek⟩, hstab⟩ :=
    d4Recipe_fieldAut_centralizer hK hf'F hf'3
  obtain ⟨hs_k, hna_k⟩ := d4Recipe_isSimpleGroup k
  haveI : IsSimpleGroup ↥(ggAutFixedSubgroup f') :=
    (MulEquiv.isSimpleGroup_congr ek).1 hs_k
  have hfix : ggAutFixedSubgroup s =
      (ggAutFixedSubgroup f').map (MulAut.conj r).toMonoidHom := by
    rw [hs_eq]
    exact gdt_fixed_conj (MulAut.conj r) f'
  have hcomp₁ : (MulAut.conj r).symm.toMonoidHom.comp (MulAut.conj r).toMonoidHom =
      MonoidHom.id (D4Recipe K) := by
    ext x
    simp
  have hmap : IsComponentOf (J.map (MulAut.conj r).symm.toMonoidHom)
      (ggAutFixedSubgroup f') := by
    have h1 := isComponentOf_map_mulEquiv (MulAut.conj r).symm hJ
    rw [hfix, Subgroup.map_map, hcomp₁, Subgroup.map_id] at h1
    exact h1
  have hcomp_eq : J.map (MulAut.conj r).symm.toMonoidHom = ggAutFixedSubgroup f' :=
    CFSG.ComponentClassification.ExcSelector.eq_of_isComponentOf_of_isSimpleGroup hmap
  have hcomp₂ : (MulAut.conj r).toMonoidHom.comp (MulAut.conj r).symm.toMonoidHom =
      MonoidHom.id (D4Recipe K) := by
    ext x
    simp
  have hJeq : J = (ggAutFixedSubgroup f').map (MulAut.conj r).toMonoidHom := by
    have h2 := congrArg (Subgroup.map (MulAut.conj r).toMonoidHom) hcomp_eq
    rw [Subgroup.map_map, hcomp₂, Subgroup.map_id] at h2
    exact h2
  have hJfixed : J = ggAutFixedSubgroup (MulAut.conj r * f' * (MulAut.conj r)⁻¹) := by
    rw [hJeq, ← hfix, hs_eq]
  refine ⟨k, inferInstance, inferInstance, n', hcard, hn, hs_k, hna_k, ?_, ?_⟩
  · exact ⟨ek.trans ((Subgroup.equivMapOfInjective (ggAutFixedSubgroup f')
      (MulAut.conj r).toMonoidHom (MulAut.conj r).injective).trans
      (MulEquiv.subgroupCongr hJeq.symm))⟩
  · intro a ha
    rintro ⟨j, _, hj⟩
    exact ha (gdt_innField_of_stab (F := D4FieldSet K) (f' := f') (r := r) hf'F hstab
      (fun x hx => by
        rw [← hJfixed] at hx
        exact hj x hx))

end Cent

end CFSG.StandardType
