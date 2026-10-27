module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveZSInputs
import TauCeti.LinearAlgebra.QuadraticForm.CartanDieudonne.Basic
import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.StandardType.ZS.DimThree

open Subgroup

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]
  {Q : QuadraticForm (ZMod p) U}

private lemma mem_range_sub_id_of_apply_eq_neg_zr (h2 : (2 : ZMod p) ≠ 0)
    {t : U ≃ₗ[ZMod p] U} {a : U} (hta : t a = -a) :
    a ∈ LinearMap.range ((t : U →ₗ[ZMod p] U) - LinearMap.id) := by
  have hval : ((t : U →ₗ[ZMod p] U) - (LinearMap.id : U →ₗ[ZMod p] U)) a =
      (-2 : ZMod p) • a := by
    rw [LinearMap.sub_apply, LinearMap.id_apply]
    change t a - a = (-2 : ZMod p) • a
    rw [hta]
    rw [show (-a - a : U) = (-2 : ZMod p) • a by
      rw [neg_smul, two_smul, neg_add, sub_eq_add_neg]]
  have h2u : (-2 : ZMod p) ≠ 0 := neg_ne_zero.mpr h2
  have ha : a = (-2 : ZMod p)⁻¹ •
      (((t : U →ₗ[ZMod p] U) - (LinearMap.id : U →ₗ[ZMod p] U)) a) := by
    rw [hval, smul_smul, inv_mul_cancel₀ h2u, one_smul]
  rw [ha]
  exact Submodule.smul_mem _ _ (LinearMap.mem_range_self _ a)

private lemma range_sub_id_eq_span_of_apply_eq_neg_zr (h2 : (2 : ZMod p) ≠ 0)
    {t : U ≃ₗ[ZMod p] U} (ht : IsRefl p t) {a : U} (ha : a ≠ 0) (hta : t a = -a) :
    LinearMap.range ((t : U →ₗ[ZMod p] U) - LinearMap.id) = ZMod p ∙ a :=
  eq_span_singleton_of_mem_of_finrank_eq_one ht.2
    (mem_range_sub_id_of_apply_eq_neg_zr h2 hta) ha

private lemma anisotropic_root_zr (h2 : (2 : ZMod p) ≠ 0) [Module.Finite (ZMod p) U]
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {t : U ≃ₗ[ZMod p] U}
    (ht : IsRefl p t) (hiso : IsIsom p Q t) {a : U} (ha : a ≠ 0) (hta : t a = -a) :
    Q a ≠ 0 := by
  intro hQa
  have hrange := range_sub_id_eq_span_of_apply_eq_neg_zr h2 ht ha hta
  have ht2u : ∀ u : U, t (t u) = u := by
    intro u
    have := congrArg (fun f : U ≃ₗ[ZMod p] U => f u) ht.1
    simpa [LinearEquiv.mul_apply] using this
  have htmem : t ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr hiso
  have hfix : ∀ v : U, t v = v → QuadraticMap.polar Q a v = 0 := by
    intro v hv
    have hpol : QuadraticMap.polar Q (t a) (t v) = QuadraticMap.polar Q a v :=
      TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup htmem a v
    rw [hta, hv, QuadraticMap.polar_neg_left] at hpol
    have htwo : (2 : ZMod p) • QuadraticMap.polar Q a v = 0 := by
      rw [two_smul]
      exact add_eq_zero_iff_eq_neg.mpr hpol.symm
    exact (smul_eq_zero.mp htwo).resolve_left h2
  have hzero : ∀ u : U, QuadraticMap.polar Q a u = 0 := by
    intro u
    have hfixed : t (u + t u) = u + t u := by
      rw [map_add, ht2u u]
      abel
    have hmem : u - t u ∈ ZMod p ∙ a := by
      have h' : t u - u ∈ ZMod p ∙ a := by
        rw [← hrange]
        exact LinearMap.mem_range_self ((t : U →ₗ[ZMod p] U) -
          (LinearMap.id : U →ₗ[ZMod p] U)) u
      have hneg : -(t u - u) ∈ ZMod p ∙ a :=
        Submodule.neg_mem (p := ZMod p ∙ a) h'
      simpa [sub_eq_add_neg] using hneg
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
    have hperp : QuadraticMap.polar Q a (u - t u) = 0 := by
      rw [← hc, QuadraticMap.polar_smul_right, QuadraticMap.polar_self, hQa]
      simp
    have hdecomp : (2 : ZMod p) • u = (u + t u) + (u - t u) := by
      rw [two_smul]
      abel
    have hsum : (2 : ZMod p) • QuadraticMap.polar Q a u = 0 := by
      rw [← QuadraticMap.polar_smul_right]
      rw [hdecomp, QuadraticMap.polar_add_right, hfix _ hfixed, hperp, add_zero]
    exact (smul_eq_zero.mp hsum).resolve_left h2
  exact ha ((hQ.1 a) fun u => hzero u)

theorem exists_root_of_isRefl_isIsom (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {t : U ≃ₗ[ZMod p] U} (ht : IsRefl p t)
    (hiso : IsIsom p Q t) : ∃ a, Q a ≠ 0 ∧ t a = -a := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have hpos : 0 < Module.finrank (ZMod p)
      (LinearMap.range ((t : U →ₗ[ZMod p] U) - LinearMap.id)) := by
    rw [ht.2]
    norm_num
  let _ : Nontrivial (LinearMap.range ((t : U →ₗ[ZMod p] U) - LinearMap.id)) :=
    Module.nontrivial_of_finrank_pos hpos
  obtain ⟨⟨a, ha_mem⟩, ha_ne_sub⟩ :=
    exists_ne (0 : LinearMap.range ((t : U →ₗ[ZMod p] U) - LinearMap.id))
  have ha : a ≠ 0 := fun h => ha_ne_sub (Subtype.ext h)
  obtain ⟨w, hw⟩ := ha_mem
  have haw : a = t w - w := by
    simpa [LinearMap.sub_apply, LinearMap.id_apply] using hw.symm
  have ht2w : t (t w) = w := by
    have := congrArg (fun f : U ≃ₗ[ZMod p] U => f w) ht.1
    simpa [LinearEquiv.mul_apply] using this
  have hta : t a = -a := by
    rw [haw, map_sub, ht2w]
    abel
  exact ⟨a, anisotropic_root_zr h2 hQ ht hiso ha hta, hta⟩

private lemma apply_eq_of_polar_eq_zero_zr (h2 : (2 : ZMod p) ≠ 0) [Module.Finite (ZMod p) U]
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {s : U ≃ₗ[ZMod p] U}
    (hs : IsRefl p s) (hsi : IsIsom p Q s) {a : U} (ha : a ≠ 0) (hsa : s a = -a)
    {v : U} (hv : QuadraticMap.polar Q a v = 0) : s v = v := by
  have haQ : Q a ≠ 0 := anisotropic_root_zr h2 hQ hs hsi ha hsa
  have hrange := range_sub_id_eq_span_of_apply_eq_neg_zr h2 hs ha hsa
  have hpaa : QuadraticMap.polar Q a a ≠ 0 := by
    rw [QuadraticMap.polar_self]
    simpa [smul_eq_mul] using mul_ne_zero h2 haQ
  have hmem : s v - v ∈ ZMod p ∙ a := by
    rw [← hrange]
    exact ⟨v, by simp [LinearMap.sub_apply]⟩
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
  have horth : QuadraticMap.polar Q a (s v - v) = 0 := by
    have hsv : QuadraticMap.polar Q a (s v) = 0 := by
      have hpol : QuadraticMap.polar Q (s a) (s v) = QuadraticMap.polar Q a v :=
        TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup
          (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr hsi) a v
      rw [hsa, QuadraticMap.polar_neg_left, hv, neg_eq_zero] at hpol
      exact hpol
    rw [QuadraticMap.polar_sub_right, hsv, hv, sub_zero]
  have hczero : c = 0 := by
    have hcpol : c • QuadraticMap.polar Q a a = 0 := by
      rw [← hc] at horth
      simpa [QuadraticMap.polar_smul_right] using horth
    exact (smul_eq_zero.mp hcpol).resolve_right hpaa
  exact sub_eq_zero.mp (by rw [← hc, hczero, zero_smul])

theorem eq_of_isRefl_isIsom_of_apply_eq_neg (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {s t : U ≃ₗ[ZMod p] U} (hs : IsRefl p s)
    (hsi : IsIsom p Q s) (ht : IsRefl p t) (hti : IsIsom p Q t) {a : U} (ha : a ≠ 0)
    (hsa : s a = -a) (hta : t a = -a) : s = t := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have haQ : Q a ≠ 0 := anisotropic_root_zr h2 hQ hs hsi ha hsa
  have hpaa : QuadraticMap.polar Q a a ≠ 0 := by
    rw [QuadraticMap.polar_self]
    simpa [smul_eq_mul] using mul_ne_zero h2 haQ
  refine LinearEquiv.ext fun u => ?_
  set c : ZMod p := QuadraticMap.polar Q a u / QuadraticMap.polar Q a a with hcdef
  have hv : QuadraticMap.polar Q a (u - c • a) = 0 := by
    rw [QuadraticMap.polar_sub_right, QuadraticMap.polar_smul_right, hcdef, smul_eq_mul,
      div_mul_cancel₀ _ hpaa, sub_self]
  have hdec : u = c • a + (u - c • a) := by abel
  have hsu : s u = -(c • a) + (u - c • a) := by
    conv_lhs => rw [hdec]
    rw [map_add, map_smul, hsa, smul_neg,
      apply_eq_of_polar_eq_zero_zr h2 hQ hs hsi ha hsa hv]
  have htu : t u = -(c • a) + (u - c • a) := by
    conv_lhs => rw [hdec]
    rw [map_add, map_smul, hta, smul_neg,
      apply_eq_of_polar_eq_zero_zr h2 hQ ht hti ha hta hv]
  rw [hsu, htu]

private lemma isRefl_reflection_zr (h2 : (2 : ZMod p) ≠ 0) {a : U} [Invertible (Q a)] :
    IsRefl p (TauCeti.QuadraticMap.reflection Q a) := by
  have ha : Q a ≠ 0 := (isUnit_of_invertible (Q a)).ne_zero
  refine ⟨TauCeti.QuadraticMap.reflection_mul_self Q a, ?_⟩
  have hrange : LinearMap.range
      ((TauCeti.QuadraticMap.reflection Q a : U →ₗ[ZMod p] U) - LinearMap.id) = ZMod p ∙ a := by
    apply le_antisymm
    · rintro x ⟨y, rfl⟩
      change TauCeti.QuadraticMap.reflection Q a y - y ∈ ZMod p ∙ a
      rw [TauCeti.QuadraticMap.reflection_apply_eq_sub_div, Submodule.mem_span_singleton]
      refine ⟨-(QuadraticMap.polar Q a y / Q a), ?_⟩
      simp [sub_eq_add_neg, neg_smul]
    · rw [Submodule.span_singleton_le_iff_mem]
      exact mem_range_sub_id_of_apply_eq_neg_zr h2
        (TauCeti.QuadraticMap.reflection_apply_self Q a)
  have ha0 : a ≠ 0 := by
    intro h
    exact ha (by rw [h]; exact map_zero Q)
  rw [hrange, finrank_span_singleton ha0]

private lemma isIsom_reflection_zr {a : U} [Invertible (Q a)] :
    IsIsom p Q (TauCeti.QuadraticMap.reflection Q a) :=
  TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp
    (TauCeti.QuadraticMap.reflection_mem_orthogonalGroup Q a)

theorem exists_isIsom_apply_eq (hp : p ≠ 2) {u v : U} (hu : Q u ≠ 0) (huv : Q u = Q v) :
    ∃ g : U ≃ₗ[ZMod p] U, IsIsom p Q g ∧ (g u = v ∨ g u = -v) := by
  let _ : NeZero (2 : ZMod p) := ⟨ZMod.prime_ne_zero p 2 hp⟩
  obtain ⟨f, hf⟩ := QuadraticMap.exists_isometryEquiv_apply_eq_of_map_eq Q huv (huv ▸ hu)
  exact ⟨f.toLinearEquiv, fun x => f.map_app x, Or.inl (by simpa using hf)⟩

theorem mem_of_isIsom_of_isRefl_mem (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {A : Subgroup (U ≃ₗ[ZMod p] U)}
    (hA : ∀ t : U ≃ₗ[ZMod p] U, IsRefl p t → IsIsom p Q t → t ∈ A) {g : U ≃ₗ[ZMod p] U}
    (hg : IsIsom p Q g) : g ∈ A := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  let _ : NeZero (2 : ZMod p) := ⟨h2⟩
  let _ : Invertible (2 : ZMod p) := invertibleOfNonzero h2
  have hQ' : Q.Nondegenerate := QuadraticMap.nondegenerate_polar_iff.mp hQ
  let H : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q) :=
    Subgroup.comap (TauCeti.QuadraticMap.orthogonalGroup Q).subtype A
  have hH : H = ⊤ := by
    refine TauCeti.QuadraticMap.subgroup_eq_top_of_reflection_mem Q hQ' H ?_
    intro v hv
    have hrefl : TauCeti.QuadraticMap.reflection Q v ∈ A :=
      hA _ (isRefl_reflection_zr h2) isIsom_reflection_zr
    change ((TauCeti.QuadraticMap.reflectionOrthogonal Q v :
      TauCeti.QuadraticMap.orthogonalGroup Q) : U ≃ₗ[ZMod p] U) ∈ A
    simpa [TauCeti.QuadraticMap.coe_reflectionOrthogonal] using hrefl
  have hgmem : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr hg
  have hgH : (⟨g, hgmem⟩ : TauCeti.QuadraticMap.orthogonalGroup Q) ∈ H := by
    rw [hH]
    exact Subgroup.mem_top _
  change ((TauCeti.QuadraticMap.orthogonalGroup Q).subtype
    (⟨g, hgmem⟩ : TauCeti.QuadraticMap.orthogonalGroup Q)) ∈ A at hgH
  simpa using hgH

end CFSG.StandardType.ZS.DimThree
