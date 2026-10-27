module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveZSInputs
import CFSG.LocalAnalysis.StandardType.ZS.Basic
import CFSG.LocalAnalysis.StandardType.ZS.ReflQuotient
import CFSG.LocalAnalysis.StandardType.GGWitExcModelTransfer
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Determinant

public section

namespace CFSG.StandardType.ZS

private lemma two_ne_zero_zmod {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) : (2 : ZMod p) ≠ 0 :=
  Ring.two_ne_zero (by rw [ZMod.ringChar_zmod_n]; exact hp)

private lemma neg_one_ne_one_units {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) :
    (-1 : (ZMod p)ˣ) ≠ 1 := by
  have h2p : Fact (2 < p) :=
    ⟨lt_of_le_of_ne (Fact.out : p.Prime).two_le (Ne.symm hp)⟩
  intro h
  exact @ZMod.neg_one_ne_one p h2p (congrArg Units.val h)

private lemma ker_reflection_add_id {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U]
    [Module (ZMod p) U] (hp : p ≠ 2) {a : U} {φ : Module.Dual (ZMod p) U} (hφ : φ a = 2) :
    LinearMap.ker ((Module.reflection hφ : U →ₗ[ZMod p] U) + LinearMap.id) =
      Submodule.span (ZMod p) {a} := by
  have h2 : (2 : ZMod p) ≠ 0 := two_ne_zero_zmod hp
  ext x
  rw [LinearMap.mem_ker, Submodule.mem_span_singleton]
  constructor
  · intro hx
    have hx' : (2 : ZMod p) • x = φ x • a := by
      have h := hx
      rw [LinearMap.add_apply, LinearMap.id_apply] at h
      change (Module.reflection hφ) x + x = 0 at h
      rw [Module.reflection_apply] at h
      have h' : x + x - φ x • a = 0 := by
        have hrearr : x + x - φ x • a = (x - φ x • a) + x := by abel
        rw [hrearr, h]
      rw [two_smul]
      exact sub_eq_zero.mp h'
    refine ⟨(2 : ZMod p)⁻¹ * φ x, ?_⟩
    calc ((2 : ZMod p)⁻¹ * φ x) • a = (2 : ZMod p)⁻¹ • (φ x • a) := by rw [smul_smul]
      _ = (2 : ZMod p)⁻¹ • ((2 : ZMod p) • x) := by rw [← hx']
      _ = x := by rw [smul_smul, inv_mul_cancel₀ h2, one_smul]
  · rintro ⟨c, rfl⟩
    rw [LinearMap.add_apply, LinearMap.id_apply, LinearEquiv.coe_coe, Module.reflection_apply,
      map_smul, hφ, smul_eq_mul, mul_smul, two_smul, smul_add]
    abel

section Refl

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]

theorem not_isRefl_mul [Module.Finite (ZMod p) U] (hp : p ≠ 2) {a b : U ≃ₗ[ZMod p] U}
    (ha : IsRefl p a) (hb : IsRefl p b) : ¬ IsRefl p (a * b) := by
  intro h
  have hprod : LinearEquiv.det (a * b) = 1 := by
    rw [map_mul, det_eq_neg_one_of_isRefl hp ha, det_eq_neg_one_of_isRefl hp hb]
    rw [neg_one_mul, neg_neg]
  exact neg_one_ne_one_units hp ((det_eq_neg_one_of_isRefl hp h).symm.trans hprod)

theorem not_isRefl_neg_mul [Module.Finite (ZMod p) U] (hp : p ≠ 2)
    (hU : 3 ≤ Module.finrank (ZMod p) U) {a : U ≃ₗ[ZMod p] U} (ha : IsRefl p a) :
    ¬ IsRefl p (LinearEquiv.neg (ZMod p) * a) := by
  intro h
  obtain ⟨v, φ, hφ, rfl⟩ := (isRefl_iff hp a).mp ha
  have h2 : (2 : ZMod p) ≠ 0 := two_ne_zero_zmod hp
  have hv0 : v ≠ 0 := by
    rintro rfl
    rw [map_zero] at hφ
    exact h2 hφ.symm
  have hker := ker_reflection_add_id hp hφ
  have hrank := LinearMap.finrank_range_add_finrank_ker
    ((Module.reflection hφ : U →ₗ[ZMod p] U) + LinearMap.id)
  rw [hker, finrank_span_singleton hv0] at hrank
  have hmap : ((LinearEquiv.neg (ZMod p) * Module.reflection hφ : U ≃ₗ[ZMod p] U) :
      U →ₗ[ZMod p] U) - LinearMap.id =
      -((Module.reflection hφ : U →ₗ[ZMod p] U) + LinearMap.id) := by
    ext x
    simp only [LinearMap.sub_apply, LinearMap.neg_apply, LinearMap.add_apply,
      LinearMap.id_apply, LinearEquiv.coe_coe, LinearEquiv.mul_apply, LinearEquiv.neg_apply]
    abel
  have hrange : Module.finrank (ZMod p) (LinearMap.range
      (((LinearEquiv.neg (ZMod p) * Module.reflection hφ : U ≃ₗ[ZMod p] U) :
        U →ₗ[ZMod p] U) - LinearMap.id)) = Module.finrank (ZMod p) U - 1 := by
    rw [hmap, LinearMap.range_neg]
    omega
  have h1 := h.2
  rw [hrange] at h1
  have hfr : Module.finrank (ZMod p) U = 2 := by omega
  exact absurd (hfr ▸ hU) (by norm_num)

theorem not_isRefl_neg_mul_mul [Module.Finite (ZMod p) U] (hp : p ≠ 2)
    (hU : Even (Module.finrank (ZMod p) U)) {a b : U ≃ₗ[ZMod p] U} (ha : IsRefl p a)
    (hb : IsRefl p b) : ¬ IsRefl p (LinearEquiv.neg (ZMod p) * (a * b)) := by
  intro h
  have hneg : LinearEquiv.det (LinearEquiv.neg (ZMod p) : U ≃ₗ[ZMod p] U) = 1 := by
    ext
    rw [LinearEquiv.coe_det]
    have hcoe : ((LinearEquiv.neg (ZMod p) : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) =
        (-1 : ZMod p) • LinearMap.id := by
      ext x
      rw [LinearEquiv.coe_coe, LinearEquiv.neg_apply, LinearMap.smul_apply,
        LinearMap.id_apply]
      exact (neg_one_smul (ZMod p) x).symm
    rw [hcoe, LinearMap.det_smul, LinearMap.det_id, mul_one, Units.val_one]
    exact Even.neg_one_pow hU
  have hprod : LinearEquiv.det (LinearEquiv.neg (ZMod p) * (a * b)) = 1 := by
    rw [map_mul, hneg, map_mul, det_eq_neg_one_of_isRefl hp ha,
      det_eq_neg_one_of_isRefl hp hb]
    rw [one_mul, neg_one_mul, neg_neg]
  exact neg_one_ne_one_units hp ((det_eq_neg_one_of_isRefl hp h).symm.trans hprod)

end Refl

private lemma not_isRefl_one {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U]
    [Module (ZMod p) U] : ¬ IsRefl p (1 : U ≃ₗ[ZMod p] U) := by
  rintro ⟨-, h2⟩
  have h0 : Module.finrank (ZMod p) (LinearMap.range
      (((1 : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) - LinearMap.id)) = 0 := by
    rw [LinearEquiv.coe_toLinearMap_one, sub_self, LinearMap.range_zero, finrank_bot]
  rw [h0] at h2
  exact zero_ne_one h2

private lemma isRefl_e_of_isConj {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U]
    [Module (ZMod p) U] {k : ExcRow} {A : Subgroup (U ≃ₗ[ZMod p] U)}
    {e : ↥(model k) ≃* ↥A} {c : ↥(model k)} (hec : IsRefl p (e c : U ≃ₗ[ZMod p] U))
    {g : ↥(model k)} (hg : IsConj c g) : IsRefl p (e g : U ≃ₗ[ZMod p] U) := by
  obtain ⟨m, hm⟩ := isConj_iff.mp hg
  have hcoe : (e g : U ≃ₗ[ZMod p] U) = (e m : U ≃ₗ[ZMod p] U) *
      (e c : U ≃ₗ[ZMod p] U) * (e m : U ≃ₗ[ZMod p] U)⁻¹ := by
    rw [← hm]
    simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
  rw [hcoe]
  exact IsRefl.conj hec (e m : U ≃ₗ[ZMod p] U)

private lemma isReflMat_of_isConj {k : ExcRow} {c g : ↥(model k)}
    (hc : IsReflMat (c : Matrix.GeneralLinearGroup (Fin (mdeg k)) (ZMod 13)))
    (hg : IsConj c g) :
    IsReflMat (g : Matrix.GeneralLinearGroup (Fin (mdeg k)) (ZMod 13)) := by
  obtain ⟨m, hm⟩ := isConj_iff.mp hg
  have hcoe : (g : Matrix.GeneralLinearGroup (Fin (mdeg k)) (ZMod 13)) =
      (m : Matrix.GeneralLinearGroup (Fin (mdeg k)) (ZMod 13)) *
        (c : Matrix.GeneralLinearGroup (Fin (mdeg k)) (ZMod 13)) *
        (m : Matrix.GeneralLinearGroup (Fin (mdeg k)) (ZMod 13))⁻¹ := by
    rw [← hm]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [hcoe]
  exact owEm_isReflMat_conj (c : Matrix.GeneralLinearGroup (Fin (mdeg k)) (ZMod 13))
    (m : Matrix.GeneralLinearGroup (Fin (mdeg k)) (ZMod 13)) hc

private lemma mul_self_of_map_eq_neg {p : ℕ} {U : Type} [AddCommGroup U]
    [Module (ZMod p) U] {k : ExcRow} {A : Subgroup (U ≃ₗ[ZMod p] U)}
    {e : ↥(model k) ≃* ↥A} {z : ↥(model k)}
    (hez : (e z : U ≃ₗ[ZMod p] U) = LinearEquiv.neg (ZMod p)) : z * z = 1 := by
  apply e.injective
  apply Subtype.ext
  rw [map_mul, map_one, Subgroup.coe_mul, Subgroup.coe_one, hez]
  ext x
  simp [LinearEquiv.mul_apply, LinearEquiv.neg_apply]

private lemma coe_map_mul {p : ℕ} {U : Type} [AddCommGroup U] [Module (ZMod p) U]
    {k : ExcRow} {A : Subgroup (U ≃ₗ[ZMod p] U)} {e : ↥(model k) ≃* ↥A}
    (a b : ↥(model k)) :
    (e (a * b) : U ≃ₗ[ZMod p] U) = (e a : U ≃ₗ[ZMod p] U) * (e b : U ≃ₗ[ZMod p] U) := by
  simp only [map_mul, Subgroup.coe_mul]

private lemma not_isRefl_e_of_isConj_mul_neg {p : ℕ} [Fact p.Prime] {U : Type}
    [AddCommGroup U] [Module (ZMod p) U] [hfin : Module.Finite (ZMod p) U] {k : ExcRow}
    {A : Subgroup (U ≃ₗ[ZMod p] U)} {e : ↥(model k) ≃* ↥A} (hp : p ≠ 2)
    (hdim3 : 3 ≤ Module.finrank (ZMod p) U) {c z g : ↥(model k)}
    (hec : IsRefl p (e c : U ≃ₗ[ZMod p] U))
    (hez : (e z : U ≃ₗ[ZMod p] U) = LinearEquiv.neg (ZMod p))
    (hg3 : IsConj c (z * g)) (hg : IsRefl p (e g : U ≃ₗ[ZMod p] U)) : False := by
  have hzrefl : IsRefl p (e (z * g) : U ≃ₗ[ZMod p] U) :=
    isRefl_e_of_isConj (e := e) (c := c) hec hg3
  have hzz : z * z = 1 := mul_self_of_map_eq_neg (e := e) (z := z) hez
  have hsplit : z * (z * g) = g := by rw [← mul_assoc, hzz, one_mul]
  rw [← hsplit, coe_map_mul, hez] at hg
  exact (not_isRefl_neg_mul hp hdim3 hzrefl) hg

private lemma not_isRefl_e_of_isConj_mul {p : ℕ} [Fact p.Prime] {U : Type}
    [AddCommGroup U] [Module (ZMod p) U] [hfin : Module.Finite (ZMod p) U] {k : ExcRow}
    {A : Subgroup (U ≃ₗ[ZMod p] U)} {e : ↥(model k) ≃* ↥A} (hp : p ≠ 2)
    {c : ↥(model k)} (hec : IsRefl p (e c : U ≃ₗ[ZMod p] U)) {a b g : ↥(model k)}
    (ha : IsConj c a) (hb : IsConj c b) (hgab : g = a * b)
    (hg : IsRefl p (e g : U ≃ₗ[ZMod p] U)) : False := by
  have hra : IsRefl p (e a : U ≃ₗ[ZMod p] U) :=
    isRefl_e_of_isConj (e := e) (c := c) hec ha
  have hrb : IsRefl p (e b : U ≃ₗ[ZMod p] U) :=
    isRefl_e_of_isConj (e := e) (c := c) hec hb
  rw [hgab, coe_map_mul] at hg
  exact (not_isRefl_mul hp hra hrb) hg

private lemma not_isRefl_e_of_isConj_mul_neg_mul {p : ℕ} [Fact p.Prime] {U : Type}
    [AddCommGroup U] [Module (ZMod p) U] [hfin : Module.Finite (ZMod p) U] {k : ExcRow}
    {A : Subgroup (U ≃ₗ[ZMod p] U)} {e : ↥(model k) ≃* ↥A} (hp : p ≠ 2)
    (heven : Even (Module.finrank (ZMod p) U)) {c z : ↥(model k)}
    (hec : IsRefl p (e c : U ≃ₗ[ZMod p] U))
    (hez : (e z : U ≃ₗ[ZMod p] U) = LinearEquiv.neg (ZMod p)) {a b g : ↥(model k)}
    (ha : IsConj c a) (hb : IsConj c b) (hgab : g = z * (a * b))
    (hg : IsRefl p (e g : U ≃ₗ[ZMod p] U)) : False := by
  have hra : IsRefl p (e a : U ≃ₗ[ZMod p] U) :=
    isRefl_e_of_isConj (e := e) (c := c) hec ha
  have hrb : IsRefl p (e b : U ≃ₗ[ZMod p] U) :=
    isRefl_e_of_isConj (e := e) (c := c) hec hb
  rw [hgab, coe_map_mul, coe_map_mul, hez] at hg
  exact (not_isRefl_neg_mul_mul hp heven hra hrb) hg

private lemma isConj_of_isRefl_e {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U]
    [Module (ZMod p) U] [hfin : Module.Finite (ZMod p) U] {k : ExcRow}
    {A : Subgroup (U ≃ₗ[ZMod p] U)} {e : ↥(model k) ≃* ↥A} (hp : p ≠ 2)
    (hdim3 : 3 ≤ Module.finrank (ZMod p) U) (heven : Even (Module.finrank (ZMod p) U))
    {c z : ↥(model k)} (hec : IsRefl p (e c : U ≃ₗ[ZMod p] U))
    (hez : (e z : U ≃ₗ[ZMod p] U) = LinearEquiv.neg (ZMod p))
    (hinv : ∀ g : ↥(model k), g * g = 1 → g = 1 ∨ IsConj c g ∨ IsConj c (z * g) ∨
      (∃ a b, IsConj c a ∧ IsConj c b ∧ g = a * b) ∨
      ∃ a b, IsConj c a ∧ IsConj c b ∧ g = z * (a * b))
    {g : ↥(model k)} (hg : IsRefl p (e g : U ≃ₗ[ZMod p] U)) : IsConj c g := by
  have hgg : g * g = 1 := by
    apply e.injective
    apply Subtype.ext
    rw [map_mul, map_one, Subgroup.coe_mul, Subgroup.coe_one]
    exact hg.1
  rcases hinv g hgg with hg1 | hg2 | hg3 | ⟨a, b, ha, hb, hgab⟩ | ⟨a, b, ha, hb, hgzab⟩
  · exact (not_isRefl_one (by simpa [hg1] using hg)).elim
  · exact hg2
  · exact (not_isRefl_e_of_isConj_mul_neg (e := e) (c := c) (z := z) (g := g) hp hdim3
      hec hez hg3 hg).elim
  · exact (not_isRefl_e_of_isConj_mul (e := e) (c := c) (g := g) hp hec ha hb hgab hg).elim
  · exact (not_isRefl_e_of_isConj_mul_neg_mul (e := e) (c := c) (z := z) (g := g) hp heven
      hec hez ha hb hgzab hg).elim

private lemma orderOf_mul_eq_of_map_eq {p : ℕ} {U : Type} [AddCommGroup U]
    [Module (ZMod p) U] {k : ExcRow} {A : Subgroup (U ≃ₗ[ZMod p] U)}
    {e : ↥(model k) ≃* ↥A} {gx gy : ↥(model k)} {x y : U ≃ₗ[ZMod p] U}
    (hx : (e gx : U ≃ₗ[ZMod p] U) = x) (hy : (e gy : U ≃ₗ[ZMod p] U) = y) :
    orderOf (x * y) = orderOf (gx * gy) := by
  rw [← hx, ← hy]
  calc orderOf ((e gx : U ≃ₗ[ZMod p] U) * (e gy : U ≃ₗ[ZMod p] U))
      = orderOf ((e gx * e gy : ↥A) : U ≃ₗ[ZMod p] U) := by rw [Subgroup.coe_mul]
    _ = orderOf (e gx * e gy) := Subgroup.orderOf_coe _
    _ = orderOf (e (gx * gy)) := by rw [map_mul]
    _ = orderOf (gx * gy) := MulEquiv.orderOf_eq e (gx * gy)

private lemma exists_conj_of_mem_isRefl {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U]
    [Module (ZMod p) U] [hfin : Module.Finite (ZMod p) U] {A : Subgroup (U ≃ₗ[ZMod p] U)}
    {k : ExcRow} {e : ↥(model k) ≃* ↥A} (hp : p ≠ 2)
    (hdim3 : 3 ≤ Module.finrank (ZMod p) U) (heven : Even (Module.finrank (ZMod p) U))
    {c z : ↥(model k)} (hec : IsRefl p (e c : U ≃ₗ[ZMod p] U))
    (hez : (e z : U ≃ₗ[ZMod p] U) = LinearEquiv.neg (ZMod p))
    (hinv : ∀ g : ↥(model k), g * g = 1 → g = 1 ∨ IsConj c g ∨ IsConj c (z * g) ∨
      (∃ a b, IsConj c a ∧ IsConj c b ∧ g = a * b) ∨
      ∃ a b, IsConj c a ∧ IsConj c b ∧ g = z * (a * b))
    {x : U ≃ₗ[ZMod p] U} (hxA : x ∈ A) (hx : IsRefl p x) :
    ∃ g : ↥(model k), IsConj c g ∧ (e g : U ≃ₗ[ZMod p] U) = x := by
  let g : ↥(model k) := e.symm ⟨x, hxA⟩
  have hxe : (e g : U ≃ₗ[ZMod p] U) = x := by
    dsimp only [g]
    simp
  refine ⟨g, ?_, hxe⟩
  exact isConj_of_isRefl_e (e := e) (c := c) (z := z) hp hdim3 heven hec hez hinv
    (by rw [hxe]; exact hx)

private lemma oneClass_of_mulEquiv {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U]
    [Module (ZMod p) U] [hfin : Module.Finite (ZMod p) U] {A : Subgroup (U ≃ₗ[ZMod p] U)}
    {k : ExcRow} {e : ↥(model k) ≃* ↥A} (hp : p ≠ 2)
    (hdim3 : 3 ≤ Module.finrank (ZMod p) U) (heven : Even (Module.finrank (ZMod p) U))
    {c z : ↥(model k)} (hec : IsRefl p (e c : U ≃ₗ[ZMod p] U))
    (hez : (e z : U ≃ₗ[ZMod p] U) = LinearEquiv.neg (ZMod p))
    (hinv : ∀ g : ↥(model k), g * g = 1 → g = 1 ∨ IsConj c g ∨ IsConj c (z * g) ∨
      (∃ a b, IsConj c a ∧ IsConj c b ∧ g = a * b) ∨
      ∃ a b, IsConj c a ∧ IsConj c b ∧ g = z * (a * b)) :
    OneClass p A := by
  intro x hxA y hyA hx hy
  obtain ⟨gx, hcx, hxge⟩ :=
    exists_conj_of_mem_isRefl (e := e) (c := c) (z := z) hp hdim3 heven hec hez hinv hxA hx
  obtain ⟨gy, hcy, hyge⟩ :=
    exists_conj_of_mem_isRefl (e := e) (c := c) (z := z) hp hdim3 heven hec hez hinv hyA hy
  obtain ⟨m, hm⟩ := isConj_iff.mp (hcx.symm.trans hcy)
  refine ⟨(e m : U ≃ₗ[ZMod p] U), (e m).2, ?_⟩
  have hcoe : (e gy : U ≃ₗ[ZMod p] U) = (e m : U ≃ₗ[ZMod p] U) *
      (e gx : U ≃ₗ[ZMod p] U) * (e m : U ≃ₗ[ZMod p] U)⁻¹ := by
    rw [← hm]
    simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
  rw [hyge, hxge] at hcoe
  exact hcoe

private lemma dmax_of_mulEquiv {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U]
    [Module (ZMod p) U] [hfin : Module.Finite (ZMod p) U] {A : Subgroup (U ≃ₗ[ZMod p] U)}
    {k : ExcRow} {e : ↥(model k) ≃* ↥A} (hp : p ≠ 2)
    (hdim3 : 3 ≤ Module.finrank (ZMod p) U) (heven : Even (Module.finrank (ZMod p) U))
    {c z : ↥(model k)} (hec : IsRefl p (e c : U ≃ₗ[ZMod p] U))
    (hez : (e z : U ≃ₗ[ZMod p] U) = LinearEquiv.neg (ZMod p))
    (hinv : ∀ g : ↥(model k), g * g = 1 → g = 1 ∨ IsConj c g ∨ IsConj c (z * g) ∨
      (∃ a b, IsConj c a ∧ IsConj c b ∧ g = a * b) ∨
      ∃ a b, IsConj c a ∧ IsConj c b ∧ g = z * (a * b))
    (hpair : ∀ g h : ↥(model k), IsConj c g → IsConj c h → orderOf (g * h) ≤ k.dmax)
    (hwit : ∃ g h : ↥(model k), IsConj c g ∧ IsConj c h ∧ orderOf (g * h) = k.dmax) :
    DMax p A k.dmax := by
  constructor
  · intro x hxA y hyA hx hy
    obtain ⟨gx, hcx, hxge⟩ :=
      exists_conj_of_mem_isRefl (e := e) (c := c) (z := z) hp hdim3 heven hec hez hinv hxA hx
    obtain ⟨gy, hcy, hyge⟩ :=
      exists_conj_of_mem_isRefl (e := e) (c := c) (z := z) hp hdim3 heven hec hez hinv hyA hy
    rw [orderOf_mul_eq_of_map_eq hxge hyge]
    exact hpair gx gy hcx hcy
  · obtain ⟨g, h, hcg, hch, hord⟩ := hwit
    refine ⟨(e g : U ≃ₗ[ZMod p] U), (e g).2, (e h : U ≃ₗ[ZMod p] U), (e h).2,
      isRefl_e_of_isConj (e := e) (c := c) hec hcg,
      isRefl_e_of_isConj (e := e) (c := c) hec hch, ?_⟩
    rw [orderOf_mul_eq_of_map_eq rfl rfl, hord]

theorem family_exc_of_mulEquiv {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {U : Type} [AddCommGroup U]
    [Module (ZMod p) U] {A : Subgroup (U ≃ₗ[ZMod p] U)} {k : ExcRow} (hk : k.admissible p)
    (hk4 : k.deg = 4) (hU : Module.finrank (ZMod p) U = k.deg) (e : ↥(model k) ≃* ↥A)
    (hcard : Nat.card (model k) = k.ord) (hcen : Nat.card (Subgroup.center ↥(model k)) = k.cen)
    (c z : ↥(model k)) (hc : IsReflMat c.1) (hec : IsRefl p (e c : U ≃ₗ[ZMod p] U))
    (hez : (e z : U ≃ₗ[ZMod p] U) = LinearEquiv.neg (ZMod p))
    (hrefl : ∀ g : ↥(model k), IsReflMat g.1 → IsConj c g)
    (hpair : ∀ g h : ↥(model k), IsConj c g → IsConj c h → orderOf (g * h) ≤ k.dmax)
    (hwit : ∃ g h : ↥(model k), IsConj c g ∧ IsConj c h ∧ orderOf (g * h) = k.dmax)
    (hinv : ∀ g : ↥(model k), g * g = 1 → g = 1 ∨ IsConj c g ∨ IsConj c (z * g) ∨
      (∃ a b, IsConj c a ∧ IsConj c b ∧ g = a * b) ∨
      ∃ a b, IsConj c a ∧ IsConj c b ∧ g = z * (a * b)) :
    Family p A := by
  have hU4 : Module.finrank (ZMod p) U = 4 := hU.trans hk4
  have hfin : Module.Finite (ZMod p) U :=
    Module.finite_of_finrank_pos (by rw [hU4]; norm_num)
  have hdim3 : 3 ≤ Module.finrank (ZMod p) U := by rw [hU4]; norm_num
  have heven : Even (Module.finrank (ZMod p) U) := by
    rw [hU4]
    exact ⟨2, by norm_num⟩
  have hrefl_e : ∀ g : ↥(model k), IsReflMat g.1 → IsRefl p (e g : U ≃ₗ[ZMod p] U) :=
    fun g hgm => isRefl_e_of_isConj (e := e) (c := c) hec (hrefl g hgm)
  have hiso : ModelIso p k A := by
    refine ⟨e, fun g => ⟨hrefl_e g, ?_⟩⟩
    intro hge
    exact isReflMat_of_isConj hc
      (isConj_of_isRefl_e (e := e) (c := c) (z := z) hp hdim3 heven hec hez hinv hge
        (hfin := hfin))
  have hone := oneClass_of_mulEquiv (e := e) (c := c) (z := z) hp hdim3 heven hec hez hinv
    (hfin := hfin)
  have hdmax := dmax_of_mulEquiv (e := e) (c := c) (z := z) hp hdim3 heven hec hez hinv
    hpair hwit (hfin := hfin)
  have hcardA : Nat.card ↥A = k.ord := (Nat.card_congr e.toEquiv).symm.trans hcard
  have hcenA : Nat.card (Subgroup.center ↥A) = k.cen :=
    (Nat.card_congr (Subgroup.centerCongr e).toEquiv).symm.trans hcen
  exact Family.exc k hk hU hcardA hcenA hdmax hone (fun _ => hiso)

end CFSG.StandardType.ZS

end
