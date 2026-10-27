module

public import CFSG.LocalAnalysis.WeakClosure81.SevenNineOrthSiegel

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Matrix CFSG.Quasithin

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem two_ne_zero_zmod_three : (2 : ZMod 3) ≠ 0 := by decide

private theorem two_ne_zero_zmod_five : (2 : ZMod 5) ≠ 0 := by decide

private theorem neg_two_ne_zero_zmod_three : (-2 : ZMod 3) ≠ 0 := by decide

private theorem neg_two_ne_zero_zmod_five : (-2 : ZMod 5) ≠ 0 := by decide

variable {p m : ℕ} (f : LinearMap.BilinForm (ZMod p) (Fin m → ZMod p))

@[expose] def OrthReflConj (x y : Fin m → ZMod p) : Prop :=
  ∃ g ∈ Subgroup.closure (orthReflSet p m f),
    (g : Matrix (Fin m) (Fin m) (ZMod p)) *ᵥ x = y ∨ (g : Matrix (Fin m) (Fin m) (ZMod p)) *ᵥ x = -y

theorem OrthReflConj.trans {f} {x y z : Fin m → ZMod p} (h₁ : OrthReflConj f x y)
    (h₂ : OrthReflConj f y z) : OrthReflConj f x z := by
  obtain ⟨g, hg, hgx⟩ := h₁
  obtain ⟨h, hh, hhy⟩ := h₂
  refine ⟨h * g, Subgroup.mul_mem _ hh hg, ?_⟩
  have hmul : (((h * g : GL (Fin m) (ZMod p)) : Matrix (Fin m) (Fin m) (ZMod p))) *ᵥ x =
      ((h : GL (Fin m) (ZMod p)) : Matrix (Fin m) (Fin m) (ZMod p)) *ᵥ
        (((g : GL (Fin m) (ZMod p)) : Matrix (Fin m) (Fin m) (ZMod p)) *ᵥ x) := by
    rw [Matrix.GeneralLinearGroup.coe_mul]
    exact (Matrix.mulVec_mulVec x ((h : GL (Fin m) (ZMod p)) :
      Matrix (Fin m) (Fin m) (ZMod p))
      ((g : GL (Fin m) (ZMod p)) : Matrix (Fin m) (Fin m) (ZMod p))).symm
  rcases hgx with hgx | hgx <;> rcases hhy with hhy | hhy
  · exact Or.inl (by rw [hmul, hgx, hhy])
  · exact Or.inr (by rw [hmul, hgx, hhy])
  · exact Or.inr (by rw [hmul, hgx, Matrix.mulVec_neg, hhy])
  · exact Or.inl (by rw [hmul, hgx, Matrix.mulVec_neg, hhy, neg_neg])

private theorem orthReflConj_of_mul_self_add {f} {x y : Fin m → ZMod p}
    (hf : ∀ x y, f x y = f y x) (hx : f x x = -2) (hy : f y y = -2) {c : ZMod p}
    (hc : c * c * (2 + f x y) = 1) : OrthReflConj f x y := by
  have huu : f (c • (x - y)) (c • (x - y)) = -2 := by
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, hx, hy,
      ← hf x y, smul_eq_mul]
    linear_combination (-2 : ZMod p) * hc
  refine ⟨orthRefl f (c • (x - y)), Subgroup.subset_closure (orthRefl_mem f huu), Or.inl ?_⟩
  rw [orthRefl_mulVec f huu]
  have hxu : f x (c • (x - y)) = c * (-2 - f x y) := by
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, hx, smul_eq_mul]
  rw [hxu]
  rw [smul_smul, show c * (-2 - f x y) * c = -1 by linear_combination -hc]
  module

private theorem orthReflConj_of_mul_self_sub {f} {x y : Fin m → ZMod p}
    (hf : ∀ x y, f x y = f y x) (hx : f x x = -2) (hy : f y y = -2) {c : ZMod p}
    (hc : c * c * (2 - f x y) = 1) : OrthReflConj f x y := by
  have huu : f (c • (x + y)) (c • (x + y)) = -2 := by
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, hx, hy,
      ← hf x y, smul_eq_mul]
    linear_combination (-2 : ZMod p) * hc
  refine ⟨orthRefl f (c • (x + y)), Subgroup.subset_closure (orthRefl_mem f huu), Or.inr ?_⟩
  rw [orthRefl_mulVec f huu]
  have hxu : f x (c • (x + y)) = c * (-2 + f x y) := by
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, hx, smul_eq_mul]
  rw [hxu]
  rw [smul_smul, show c * (-2 + f x y) * c = -1 by linear_combination -hc]
  module

theorem orthReflConj_of_ne_zero (hp : p = 3 ∨ p = 5) (hf : ∀ x y, f x y = f y x)
    {x y : Fin m → ZMod p} (hx : f x x = -2) (hy : f y y = -2) (hxy : f x y ≠ 0) :
    OrthReflConj f x y := by
  rcases hp with rfl | rfl
  · have hδ : f x y = 1 ∨ f x y = 2 := by
      revert hxy
      generalize f x y = δ
      revert δ
      decide
    rcases hδ with hδ | hδ
    · exact orthReflConj_of_mul_self_sub hf hx hy (c := 1) (by rw [hδ]; decide)
    · exact orthReflConj_of_mul_self_add hf hx hy (c := 1) (by rw [hδ]; decide)
  · have hδ : f x y = 1 ∨ f x y = 2 ∨ f x y = 3 ∨ f x y = 4 := by
      revert hxy
      generalize f x y = δ
      revert δ
      decide
    rcases hδ with hδ | hδ | hδ | hδ
    · exact orthReflConj_of_mul_self_sub hf hx hy (c := 1) (by rw [hδ]; decide)
    · exact orthReflConj_of_mul_self_add hf hx hy (c := 2) (by rw [hδ]; decide)
    · exact orthReflConj_of_mul_self_sub hf hx hy (c := 2) (by rw [hδ]; decide)
    · exact orthReflConj_of_mul_self_add hf hx hy (c := 1) (by rw [hδ]; decide)

private theorem orthRefl_zpowers_isPGroup (v : Fin m → ZMod p) :
    IsPGroup 2 ↥(Subgroup.zpowers (orthRefl f v)) := by
  have hsq : (orthRefl f v) ^ 2 = 1 := by
    rw [pow_two]
    calc orthRefl f v * orthRefl f v = (orthRefl f v)⁻¹ * orthRefl f v := by
          rw [orthRefl_inv f v]
      _ = 1 := inv_mul_cancel _
  refine IsPGroup.of_card_dvd_pow (n := 1) ?_
  rw [Nat.card_zpowers, pow_one]
  exact orderOf_dvd_of_pow_eq_one hsq

private theorem orthRefl_zpowers_le_normalizer (hf : ∀ x y, f x y = f y x)
    {a y : Fin m → ZMod p} (hay : f a y = 0) :
    Subgroup.zpowers (orthRefl f a) ≤
      Subgroup.normalizer (Subgroup.zpowers (orthRefl f y) :
        Set (GL (Fin m) (ZMod p))) := by
  have hcomm : Commute (orthRefl f a) (orthRefl f y) := orthRefl_comm f hf hay
  intro z hz
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  rw [Subgroup.mem_normalizer_iff]
  intro w
  constructor
  · intro hw
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    rw [(hcomm.zpow_left i).zpow_right j |>.mul_inv_cancel]
    exact Subgroup.mem_zpowers_iff.mpr ⟨j, rfl⟩
  · intro hw
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hw
    rw [Subgroup.mem_zpowers_iff]
    refine ⟨j, ?_⟩
    have hw' : w = (orthRefl f y) ^ j := by
      calc w = ((orthRefl f a) ^ i)⁻¹ *
            ((orthRefl f a) ^ i * w * ((orthRefl f a) ^ i)⁻¹) *
              ((orthRefl f a) ^ i) := by group
        _ = ((orthRefl f a) ^ i)⁻¹ * (orthRefl f y) ^ j *
              ((orthRefl f a) ^ i) := by rw [hj]
        _ = (orthRefl f y) ^ j :=
              ((hcomm.zpow_left i).zpow_right j).inv_mul_cancel
    exact hw'.symm

@[expose] def orthConjSup (a : Fin m → ZMod p) : Subgroup (GL (Fin m) (ZMod p)) :=
  ⨆ (g : GL (Fin m) (ZMod p)) (_ : g ∈ Subgroup.closure (orthReflSet p m f))
    (_ : IsPGroup 2 ↥(Subgroup.zpowers (orthRefl f a) ⊔
      conjSubgroup (Subgroup.zpowers (orthRefl f a)) g)),
    conjSubgroup (Subgroup.zpowers (orthRefl f a)) g

theorem orthRefl_mem_orthConjSup (hf : ∀ x y, f x y = f y x) {a y : Fin m → ZMod p}
    (hay : f a y = 0) (h : OrthReflConj f a y) : orthRefl f y ∈ orthConjSup f a := by
  obtain ⟨g, hg, hgx⟩ := h
  have hconj : g * orthRefl f a * g⁻¹ = orthRefl f y := by
    rcases hgx with hgx | hgx
    · rw [orthRefl_conj (isOrthIsometry_of_mem_closure f hf hg) a, hgx]
    · rw [orthRefl_conj (isOrthIsometry_of_mem_closure f hf hg) a, hgx, orthRefl_neg]
  have hconj' : conjSubgroup (Subgroup.zpowers (orthRefl f a)) g⁻¹ =
      Subgroup.zpowers (orthRefl f y) := by
    rw [conjSubgroup, inv_inv, MonoidHom.map_zpowers]
    rw [show (MulEquiv.toMonoidHom (MulAut.conj g)) (orthRefl f a) = g * orthRefl f a * g⁻¹
      from MulAut.conj_apply g _]
    rw [hconj]
  have hpgrp : IsPGroup 2 ↥(Subgroup.zpowers (orthRefl f a) ⊔
      conjSubgroup (Subgroup.zpowers (orthRefl f a)) g⁻¹) := by
    rw [hconj']
    exact IsPGroup.to_sup_of_normal_right' (orthRefl_zpowers_isPGroup f a)
      (orthRefl_zpowers_isPGroup f y) (orthRefl_zpowers_le_normalizer f hf hay)
  have hmemb : orthRefl f y ∈ conjSubgroup (Subgroup.zpowers (orthRefl f a)) g⁻¹ := by
    rw [hconj']
    exact Subgroup.mem_zpowers_iff.mpr ⟨(1 : ℤ), by simp⟩
  exact Subgroup.mem_iSup_of_mem g⁻¹ (Subgroup.mem_iSup_of_mem (Subgroup.inv_mem _ hg)
    (Subgroup.mem_iSup_of_mem hpgrp hmemb))

namespace OrthFrame

variable {f} (F : OrthFrame p m f)

theorem orthReflConj_a_of_mem_U (hp : p = 3 ∨ p = 5) {v : Fin m → ZMod p} (hv : v ∈ F.U)
    (hvv : f v v = -2) (hva : f v F.a = 0) : OrthReflConj f F.a v := by
  have hvs := (F.mem_U.1 hv).1
  have hvs' := (F.mem_U.1 hv).2
  have hzz : f (F.s + F.s' - F.a - v) (F.s + F.s' - F.a - v) = -2 := by
    simp only [map_sub, map_add, LinearMap.sub_apply, LinearMap.add_apply,
      F.isotropic_s, F.isotropic_s', F.pair, F.norm_a, F.a_orth_s, F.a_orth_s',
      hvs, hvs', hvv, hva, F.symm F.a v, F.symm v F.a, F.symm F.s F.a, F.symm F.s' F.a,
      F.symm F.s v, F.symm F.s' v, F.symm v F.s, F.symm v F.s', ← F.symm F.s F.s',
      F.symm F.a F.s, F.symm F.a F.s']
    ring
  have haz : f F.a (F.s + F.s' - F.a - v) = 2 := by
    simp only [map_sub, map_add, LinearMap.sub_apply, LinearMap.add_apply,
      F.isotropic_s, F.isotropic_s', F.pair, F.norm_a, F.a_orth_s, F.a_orth_s',
      hvs, hvs', hvv, hva, F.symm F.a v, F.symm v F.a, F.symm F.s F.a, F.symm F.s' F.a,
      F.symm F.s v, F.symm F.s' v, F.symm v F.s, F.symm v F.s', ← F.symm F.s F.s',
      F.symm F.a F.s, F.symm F.a F.s']
    ring
  have hzv : f (F.s + F.s' - F.a - v) v = 2 := by
    simp only [map_sub, map_add, LinearMap.sub_apply, LinearMap.add_apply,
      F.isotropic_s, F.isotropic_s', F.pair, F.norm_a, F.a_orth_s, F.a_orth_s',
      hvs, hvs', hvv, hva, F.symm F.a v, F.symm v F.a, F.symm F.s F.a, F.symm F.s' F.a,
      F.symm F.s v, F.symm F.s' v, F.symm v F.s, F.symm v F.s', ← F.symm F.s F.s',
      F.symm F.a F.s, F.symm F.a F.s']
    ring
  have h2 : (2 : ZMod p) ≠ 0 := by
    rcases hp with rfl | rfl
    · exact two_ne_zero_zmod_three
    · exact two_ne_zero_zmod_five
  exact (orthReflConj_of_ne_zero f hp F.symm F.norm_a hzz (by rw [haz]; exact h2)).trans
    (orthReflConj_of_ne_zero f hp F.symm hzz hvv (by rw [hzv]; exact h2))

theorem siegel_smul_mem_orthConjSup [Fact p.Prime] (hp : p = 3 ∨ p = 5) {v : Fin m → ZMod p}
    (hv : v ∈ F.U) (hvv : f v v = -2) (hva : f v F.a = 0) (c : ZMod p) :
    F.siegel (c • v) ∈ orthConjSup f F.a := by
  have hvs := (F.mem_U.1 hv).1
  have hn2 : (-2 : ZMod p) ≠ 0 := by
    rcases hp with rfl | rfl
    · exact neg_two_ne_zero_zmod_three
    · exact neg_two_ne_zero_zmod_five
  have hT : F.siegel (c • v) = orthRefl f v * orthRefl f (v + (-c) • F.s) := by
    rw [show c • v = -((-c) • v) by rw [neg_smul, neg_neg]]
    exact F.siegel_neg_smul hvv hvs (-c)
  have hw_norm : f (v + (-c) • F.s) (v + (-c) • F.s) = -2 := by
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, hvv, hvs,
      F.symm F.s v, F.isotropic_s, smul_eq_mul]
    ring
  have hw_a : f F.a (v + (-c) • F.s) = 0 := by
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      F.symm F.a v, hva, F.a_orth_s, smul_eq_mul]
    ring
  have hv_w : f v (v + (-c) • F.s) = -2 := by
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, hvv, hvs,
      smul_eq_mul]
    ring
  have hvw : OrthReflConj f v (v + (-c) • F.s) :=
    orthReflConj_of_ne_zero f hp F.symm hvv hw_norm (by rw [hv_w]; exact hn2)
  have hav : OrthReflConj f F.a v := orthReflConj_a_of_mem_U F hp hv hvv hva
  have haw : OrthReflConj f F.a (v + (-c) • F.s) := hav.trans hvw
  have hrv : orthRefl f v ∈ orthConjSup f F.a :=
    orthRefl_mem_orthConjSup f F.symm (by rw [F.symm F.a v]; exact hva) hav
  have hrw : orthRefl f (v + (-c) • F.s) ∈ orthConjSup f F.a :=
    orthRefl_mem_orthConjSup f F.symm hw_a haw
  rw [hT]
  exact Subgroup.mul_mem _ hrv hrw

end OrthFrame

end CFSG.LocalAnalysis.WeakClosure81
