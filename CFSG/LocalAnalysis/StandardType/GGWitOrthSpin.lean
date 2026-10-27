module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveZSInputs

import CFSG.LocalAnalysis.StandardType.GGFLWReflForm
import CFSG.ClassicalInvolution.Orders.OrthogonalIndex
import CFSG.ClassicalGroups.Orthogonal.Basic
import TauCeti.FieldTheory.SquareClassGroup.Basic
import TauCeti.Algebra.Group.Units.Basic
import CFSG.LieType.Universal.SpinOmega.Range

public section

namespace CFSG.StandardType.ZS

open Subgroup

private lemma owSp_two_ne_zero {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h
  have hdvd : p ∣ 2 := (CharP.cast_eq_zero_iff (ZMod p) p 2).mp h
  have hpge : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  exact hp2 (le_antisymm hle hpge)

private theorem owSp_form_of_isRefl_form {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [Invertible (2 : K)] (Q : QuadraticForm K V)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {t : V ≃ₗ[K] V} (ht : ∀ v, Q (t v) = Q v)
    {c : V} (hc : c ≠ 0) (β : V →ₗ[K] K) (hβc : β c = 2)
    (hform : ∀ v, t v = v - β v • c) :
    Q c ≠ 0 ∧ ∀ x, t x = x - (QuadraticMap.polar Q c x / Q c) • c := by
  have h2 : (2 : K) ≠ 0 := (isUnit_of_invertible (2 : K)).ne_zero
  have hpol : ∀ x y, QuadraticMap.polar Q (t x) (t y) = QuadraticMap.polar Q x y :=
    fun x y => CFSG.ClassicalGroups.Orthogonal.polar_map_of_mem
      (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr ht) x y
  have hβ : ∀ v, β v * (2 * Q c) = 2 * QuadraticMap.polar Q c v := by
    intro v
    have h := hpol c v
    rw [hform c, hform v, hβc] at h
    rw [show c - (2 : K) • c = -c by rw [two_smul]; abel] at h
    rw [QuadraticMap.polar_neg_left, QuadraticMap.polar_sub_right,
      QuadraticMap.polar_smul_right, smul_eq_mul, QuadraticMap.polar_self,
      nsmul_eq_mul] at h
    linear_combination h
  have hQc : Q c ≠ 0 := by
    intro h0
    refine hc (hQ.1 c (fun y => ?_))
    rw [QuadraticMap.polarBilin_apply_apply]
    have h := hβ y
    rw [h0, mul_zero, mul_zero] at h
    exact (mul_eq_zero.mp h.symm).resolve_left h2
  refine ⟨hQc, fun x => ?_⟩
  rw [hform x]
  have hβx : β x = QuadraticMap.polar Q c x / Q c := by
    rw [eq_div_iff hQc]
    apply mul_left_cancel₀ h2
    rw [← hβ x]
    ring
  rw [hβx]

private lemma owSp_smul_ratio {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [Invertible (2 : K)] {β : V →ₗ[K] K} {a a' : V} (h : a - β a • a' = -a) :
    a = (β a / 2) • a' := by
  have h2 : (2 : K) ≠ 0 := (isUnit_of_invertible (2 : K)).ne_zero
  have hneg : β a • a' - a = a := by
    have := congrArg (fun x : V => -x) h
    simpa [neg_sub] using this
  have hX : β a • a' = (2 : K) • a := by
    rw [show (2 : K) • a = a + a by rw [two_smul]]
    exact sub_eq_iff_eq_add.mp hneg
  calc a = (2 : K)⁻¹ • ((2 : K) • a) := by
        rw [smul_smul, inv_mul_cancel₀ h2, one_smul]
    _ = (2 : K)⁻¹ • (β a • a') := by rw [← hX]
    _ = ((2 : K)⁻¹ * β a) • a' := by rw [smul_smul]
    _ = (β a / 2) • a' := by
        congr 1
        rw [div_eq_inv_mul, mul_comm]

private lemma owSp_squareClass_eq {K : Type*} [Field K] {c x y : K} (hc : c ≠ 0)
    (hy : y ≠ 0) (h : c = x * x * y) :
    TauCeti.squareClass (Units.mk0 y hy) = TauCeti.squareClass (Units.mk0 c hc) := by
  have hx : x ≠ 0 := by
    rintro rfl
    rw [zero_mul, zero_mul] at h
    exact hc h
  have hunit : Units.mk0 c hc = Units.mk0 x hx * Units.mk0 x hx * Units.mk0 y hy := by
    apply Units.ext
    simp only [Units.val_mul, Units.val_mk0]
    exact h
  rw [hunit, TauCeti.squareClass_mul]
  have hsq : TauCeti.squareClass (Units.mk0 x hx * Units.mk0 x hx) = 0 := by
    rw [TauCeti.squareClass_eq_zero_iff]
    exact ⟨Units.mk0 x hx, rfl⟩
  rw [hsq]
  abel

private lemma owSp_squareClass_eq_of_form {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [Invertible (2 : K)] {Q : QuadraticForm K V} {t : V ≃ₗ[K] V} {β : V →ₗ[K] K}
    {a a' : V} {c : K} (hc : c ≠ 0) (hQa' : Q a' ≠ 0)
    (hform' : ∀ v, t v = v - β v • a') (ha : Q a = c) (hta : t a = -a) :
    TauCeti.squareClass (Units.mk0 (Q a') hQa') = TauCeti.squareClass (Units.mk0 c hc) := by
  have ha_eq : a = (β a / 2) • a' := by
    apply owSp_smul_ratio
    rw [← hform' a, hta]
  have hc_eq : c = (β a / 2) * (β a / 2) * Q a' := by
    have hqa : Q a = (β a / 2) * (β a / 2) * Q a' := by
      conv_lhs => rw [ha_eq]
      rw [QuadraticMap.map_smul, smul_eq_mul]
    rw [← ha]
    exact hqa
  exact owSp_squareClass_eq hc hQa' hc_eq

private theorem owSp_detSpinorNorm_of_form {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [Finite K] [FiniteDimensional K V] [Invertible (2 : K)]
    (Q : QuadraticForm K V) (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {t : V ≃ₗ[K] V} (hto : t ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    {a : V} (ha : Q a ≠ 0) (β : V →ₗ[K] K) (hβa : β a = 2)
    (hform : ∀ v, t v = v - β v • a) :
    CFSG.ClassicalInvolution.detSpinorNorm (QuadraticMap.nondegenerate_polar_iff.mp hQ) ⟨t, hto⟩ =
      (-1, TauCeti.squareClassHom (Units.mk0 (Q a) ha)) := by
  have horth : ∀ v, Q (t v) = Q v := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hto
  have ha0 : a ≠ 0 := fun h => ha (by rw [h, map_zero])
  have hformula : ∀ x, t x = x - (QuadraticMap.polar Q a x / Q a) • a :=
    (owSp_form_of_isRefl_form Q hQ horth ha0 β hβa hform).2
  haveI : Invertible (Q a) := invertibleOfNonzero ha
  have hrefl : t = TauCeti.QuadraticMap.reflection Q a := by
    ext x
    rw [hformula x, TauCeti.QuadraticMap.reflection_apply_eq_sub_div]
  have hOeq : (⟨t, hto⟩ : TauCeti.QuadraticMap.orthogonalGroup Q) =
      TauCeti.QuadraticMap.reflectionOrthogonal Q a := by
    apply Subtype.ext
    rw [CFSG.ClassicalInvolution.coe_reflectionOrthogonal_eq_reflect,
      CFSG.ClassicalGroups.Orthogonal.reflect_eq_reflection]
    exact hrefl
  rw [hOeq]
  rw [CFSG.ClassicalInvolution.detSpinorNorm_reflectionOrthogonal]
  rw [show unitOfInvertible (Q a) = Units.mk0 (Q a) ha from Units.ext rfl]

theorem wit_classRefl_of_mem_closure {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {U : Type} [AddCommGroup U] [Module (ZMod p) U]
    [Module.Finite (ZMod p) U] (Q : QuadraticForm (ZMod p) U) (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (c : ZMod p) (hc : c ≠ 0) {r : U ≃ₗ[ZMod p] U} (hr : IsRefl p r)
    (hmem : r ∈ closure (ClassRefl p Q c)) : r ∈ ClassRefl p Q c := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Invertible (2 : ZMod p) := invertibleOfNonzero (owSp_two_ne_zero hp2)
  have hClassOrth : ∀ t ∈ ClassRefl p Q c, t ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
    intro t ht
    exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr ht.2.1
  let u : (ZMod p)ˣ := Units.mk0 c hc
  have hu : (u : ZMod p) = c := rfl
  let x : (ZMod p)ˣ × Multiplicative (TauCeti.SquareClassGroup (ZMod p)) :=
    ((-1 : (ZMod p)ˣ), TauCeti.squareClassHom u)
  have hxx : x * x = 1 := by
    have h1 : (-1 : (ZMod p)ˣ) * (-1 : (ZMod p)ˣ) = 1 := by simp
    have h2 : TauCeti.squareClassHom u * TauCeti.squareClassHom u = 1 := by
      rw [← map_mul, TauCeti.squareClassHom_apply]
      have hu2 : TauCeti.squareClass (u * u) = 0 := by
        rw [TauCeti.squareClass_eq_zero_iff]
        exact ⟨u, rfl⟩
      rw [hu2]
      rfl
    show (((-1 : (ZMod p)ˣ) * (-1 : (ZMod p)ˣ)),
      TauCeti.squareClassHom u * TauCeti.squareClassHom u) = 1
    rw [h1, h2]
    rfl
  let S : Subgroup ((ZMod p)ˣ × Multiplicative (TauCeti.SquareClassGroup (ZMod p))) :=
    Subgroup.closure ({x} : Set _)
  let H : Subgroup (U ≃ₗ[ZMod p] U) :=
    (Subgroup.comap (CFSG.ClassicalInvolution.detSpinorNorm
      (QuadraticMap.nondegenerate_polar_iff.mp hQ)) S).map
      (TauCeti.QuadraticMap.orthogonalGroup Q).subtype
  have hclassH : ClassRefl p Q c ⊆ H := by
    intro t ht
    have hto : t ∈ TauCeti.QuadraticMap.orthogonalGroup Q := hClassOrth t ht
    have horth : ∀ v, Q (t v) = Q v := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hto
    obtain ⟨a', β', ha', hβa', hform'⟩ := CFSG.StandardType.ggFLW_isRefl_form (p := p) hp2 ht.1
    have hQa' : Q a' ≠ 0 := (owSp_form_of_isRefl_form Q hQ horth ha' β' hβa' hform').1
    have hdet := owSp_detSpinorNorm_of_form Q hQ hto hQa' β' hβa' hform'
    obtain ⟨a, ha, hta⟩ := ht.2.2
    have hsc := owSp_squareClass_eq_of_form hc hQa' hform' ha hta
    have hschom : TauCeti.squareClassHom (Units.mk0 (Q a') hQa') = TauCeti.squareClassHom u := by
      have h := congrArg Multiplicative.ofAdd hsc
      simpa [TauCeti.squareClassHom_apply] using h
    refine Subgroup.mem_map.mpr ⟨⟨t, hto⟩, Subgroup.mem_comap.mpr ?_, rfl⟩
    rw [hdet, hschom]
    exact Subgroup.subset_closure (by simp [x])
  have hr_orth : r ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    (Subgroup.closure_le (TauCeti.QuadraticMap.orthogonalGroup Q)).mpr hClassOrth hmem
  have hrH : r ∈ H := (Subgroup.closure_le H).mpr hclassH hmem
  have hxS : CFSG.ClassicalInvolution.detSpinorNorm (QuadraticMap.nondegenerate_polar_iff.mp hQ)
      ⟨r, hr_orth⟩ ∈ S :=
    Subgroup.mem_comap.mp
      ((Subgroup.mem_map_iff_mem
        (f := (TauCeti.QuadraticMap.orthogonalGroup Q).subtype)
        (Subgroup.subtype_injective _)).mp hrH)
  have horth_r : ∀ v, Q (r v) = Q v := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hr_orth
  obtain ⟨a_r, β_r, ha_r, hβa_r, hform_r⟩ := CFSG.StandardType.ggFLW_isRefl_form (p := p) hp2 hr
  have hQa_r : Q a_r ≠ 0 := (owSp_form_of_isRefl_form Q hQ horth_r ha_r β_r hβa_r hform_r).1
  have hdet_r := owSp_detSpinorNorm_of_form Q hQ hr_orth hQa_r β_r hβa_r hform_r
  have hycases : CFSG.ClassicalInvolution.detSpinorNorm (QuadraticMap.nondegenerate_polar_iff.mp hQ)
      ⟨r, hr_orth⟩ = 1 ∨ CFSG.ClassicalInvolution.detSpinorNorm
        (QuadraticMap.nondegenerate_polar_iff.mp hQ) ⟨r, hr_orth⟩ = x := by
    have hx2 : CFSG.ClassicalInvolution.detSpinorNorm (QuadraticMap.nondegenerate_polar_iff.mp hQ)
          ⟨r, hr_orth⟩ ∈
        Subgroup.closure ({x, x} : Set
          ((ZMod p)ˣ × Multiplicative (TauCeti.SquareClassGroup (ZMod p)))) := by
      have h := hxS
      change CFSG.ClassicalInvolution.detSpinorNorm (QuadraticMap.nondegenerate_polar_iff.mp hQ)
          ⟨r, hr_orth⟩ ∈ Subgroup.closure ({x} : Set
            ((ZMod p)ˣ × Multiplicative (TauCeti.SquareClassGroup (ZMod p)))) at h
      simpa using h
    rcases CFSG.ClassicalInvolution.eq_one_or_eq_or_eq_mul_of_mem_closure_pair hxx hxx rfl hx2 with
      h | h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact Or.inr h
    · exact Or.inl (h.trans hxx)
  haveI : Fact (2 < p) := ⟨lt_of_le_of_ne hp.two_le (Ne.symm hp2)⟩
  have hneg1 : (-1 : (ZMod p)ˣ) ≠ 1 := by
    intro h
    have h' : (↑(-1 : (ZMod p)ˣ) : ZMod p) = ↑(1 : (ZMod p)ˣ) :=
      congrArg (fun z : (ZMod p)ˣ => (z : ZMod p)) h
    rw [Units.val_neg, Units.val_one] at h'
    exact ZMod.neg_one_ne_one h'
  rcases hycases with hy1 | hyx
  · exfalso
    have hfst : (-1 : (ZMod p)ˣ) = 1 := by
      have := congrArg Prod.fst (hdet_r.symm.trans hy1)
      simpa using this
    exact hneg1 hfst
  · have hsc_r : TauCeti.squareClassHom (Units.mk0 (Q a_r) hQa_r) =
        TauCeti.squareClassHom u := by
      have h : TauCeti.squareClassHom (Units.mk0 (Q a_r) hQa_r) = x.2 :=
        congrArg Prod.snd (hdet_r.symm.trans hyx)
      exact h
    have hsc_r' : TauCeti.squareClass (Units.mk0 (Q a_r) hQa_r) = TauCeti.squareClass u := by
      have h := congrArg Multiplicative.toAdd hsc_r
      simpa [TauCeti.squareClassHom_apply] using h
    obtain ⟨s, hs⟩ : ∃ s : ZMod p, Q a_r * c = s * s := by
      have hsq : IsSquare (Units.mk0 (Q a_r) hQa_r * u) :=
        (TauCeti.squareClass_eq_iff_isSquare_mul _ _).mp hsc_r'
      obtain ⟨s, hs⟩ := TauCeti.isSquare_units_val_iff.mpr hsq
      exact ⟨s, by simpa [Units.val_mul, Units.val_mk0, hu] using hs⟩
    have hs0 : s ≠ 0 := by
      intro hs0
      rw [hs0, mul_zero] at hs
      exact (mul_ne_zero hQa_r hc) hs
    have hQar : Q a_r = s * s / c := by
      rw [eq_div_iff hc]
      exact hs
    refine ⟨hr, TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hr_orth, (c / s) • a_r, ?_, ?_⟩
    · show Q ((c / s) • a_r) = c
      rw [QuadraticMap.map_smul, hQar, smul_eq_mul]
      field_simp [hc, hs0]
    · have hr_a : r a_r = -a_r := by
        rw [hform_r a_r, hβa_r, two_smul]
        abel
      show r ((c / s) • a_r) = -((c / s) • a_r)
      rw [map_smul, hr_a, smul_neg]

end CFSG.StandardType.ZS

end
