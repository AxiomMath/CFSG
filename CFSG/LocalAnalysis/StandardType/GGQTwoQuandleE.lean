module

public import CFSG.LocalAnalysis.StandardType.GGQTwoLin
import Mathlib.LinearAlgebra.Matrix.BilinearForm

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def GGQ2Lin.reflections {p : ℕ} [Fact p.Prime] (D : GGQ2Lin p) :
    Set (D.V ≃ₗ[ZMod p] D.V) := {t | t ∈ D.weyl ∧ IsReflLin t}

section Refl

@[expose] noncomputable def ggQ2xQ_tc {V : Type*} [AddCommGroup V] [Module (ZMod 3) V]
    (B : LinearMap.BilinForm (ZMod 3) V) (c : V) : Module.End (ZMod 3) V :=
  LinearMap.id - (B c).smulRight c

@[simp] lemma ggQ2xQ_tc_apply {V : Type*} [AddCommGroup V] [Module (ZMod 3) V]
    (B : LinearMap.BilinForm (ZMod 3) V) (c v : V) :
    ggQ2xQ_tc B c v = v - B c v • c := rfl

lemma ggQ2xQ_tc_neg {V : Type*} [AddCommGroup V] [Module (ZMod 3) V]
    (B : LinearMap.BilinForm (ZMod 3) V) (c : V) : ggQ2xQ_tc B (-c) = ggQ2xQ_tc B c := by
  ext v
  have e : B (-c) v = (-1 : ZMod 3) * B c v := by
    rw [show -c = (-1 : ZMod 3) • c from (neg_one_smul (ZMod 3) c).symm, LinearMap.map_smul₂,
      smul_eq_mul]
  rw [ggQ2xQ_tc_apply, ggQ2xQ_tc_apply, e, mul_smul]
  erw [neg_one_smul (ZMod 3)]
  rw [smul_neg, neg_neg]

lemma ggQ2xQ_zmod3_sq_eq_one {x : ZMod 3} (hx : x ≠ 0) : x * x = 1 := by
  revert hx; revert x; decide

lemma ggQ2xQ_zmod3_cases_of_sq {x : ZMod 3} (hx : x * x = 1) : x = 1 ∨ x = -1 := by
  revert hx; revert x; decide

lemma ggQ2xQ_eq_smul_of_smul_eq {V : Type*} [AddCommGroup V] [Module (ZMod 3) V]
    {a b : ZMod 3} {c c' : V} (ha : a * a = 1) (h : a • c' = b • c) :
    c' = (a * b) • c := by
  calc c' = (a * a) • c' := by rw [ha, one_smul]
    _ = a • (a • c') := by rw [mul_smul]
    _ = (a * b) • c := by rw [h, smul_smul]

lemma ggQ2xQ_tc_eq_tc_iff {V : Type*} [AddCommGroup V] [Module (ZMod 3) V]
    (B : LinearMap.BilinForm (ZMod 3) V) (hB : B.IsSymm) {c c' : V}
    (hc : B c c = 2) (hc' : B c' c' = 2) :
    ggQ2xQ_tc B c = ggQ2xQ_tc B c' ↔ c' = c ∨ c' = -c := by
  constructor
  · intro h
    have h1 := LinearMap.congr_fun h c
    simp only [ggQ2xQ_tc_apply, hc] at h1
    set a := B c' c with ha_def
    have h2 : a • c' = (2 : ZMod 3) • c := by
      have := congrArg (fun x => c - x) h1
      simpa using this.symm
    have hsym : B c c' = a := by rw [ha_def]; exact (hB.eq c c').trans rfl
    have h3 := congrArg (fun x => B c x) h2
    simp only [map_smul, smul_eq_mul, hc, hsym] at h3
    have haa : a * a = 1 := by
      have : a * a = 2 * 2 := h3
      rw [this]; decide
    have hc'e := ggQ2xQ_eq_smul_of_smul_eq haa h2
    rcases ggQ2xQ_zmod3_cases_of_sq haa with h4 | h4
    · right; rw [hc'e, h4, show (1 : ZMod 3) * 2 = -1 by decide]
      exact neg_one_smul (ZMod 3) c
    · left; rw [hc'e, h4, show (-1 : ZMod 3) * 2 = 1 by decide, one_smul]
  · rintro (rfl | rfl)
    · rfl
    · exact (ggQ2xQ_tc_neg B c).symm

lemma ggQ2xQ_tc_tc_apply {V : Type*} [AddCommGroup V] [Module (ZMod 3) V]
    (B : LinearMap.BilinForm (ZMod 3) V) (c c' v : V) :
    ggQ2xQ_tc B c (ggQ2xQ_tc B c' v) =
      v - B c' v • c' - (B c v - B c' v * B c c') • c := by
  simp only [ggQ2xQ_tc_apply, map_sub, map_smul, smul_eq_mul]
  module

lemma ggQ2xQ_tc_comm_apply {V : Type*} [AddCommGroup V] [Module (ZMod 3) V]
    (B : LinearMap.BilinForm (ZMod 3) V) (hB : B.IsSymm) (c c' v : V) :
    ggQ2xQ_tc B c (ggQ2xQ_tc B c' v) - ggQ2xQ_tc B c' (ggQ2xQ_tc B c v) =
      B c c' • (B c' v • c - B c v • c') := by
  have hs : B c' c = B c c' := hB.eq c' c
  rw [ggQ2xQ_tc_tc_apply, ggQ2xQ_tc_tc_apply, hs]
  module

lemma ggQ2xQ_tc_comm_iff {V : Type*} [AddCommGroup V] [Module (ZMod 3) V]
    (B : LinearMap.BilinForm (ZMod 3) V) (hB : B.IsSymm) {c c' : V}
    (hc : B c c = 2) (hc' : B c' c' = 2) (hne : ggQ2xQ_tc B c ≠ ggQ2xQ_tc B c') :
    ggQ2xQ_tc B c * ggQ2xQ_tc B c' = ggQ2xQ_tc B c' * ggQ2xQ_tc B c ↔ B c c' = 0 := by
  constructor
  · intro h
    by_contra ha
    have h1 := ggQ2xQ_tc_comm_apply B hB c c' c
    have h0 : ggQ2xQ_tc B c (ggQ2xQ_tc B c' c) - ggQ2xQ_tc B c' (ggQ2xQ_tc B c c) = 0 := by
      have := LinearMap.congr_fun h c
      simp only [Module.End.mul_apply] at this
      rw [this, sub_self]
    rw [h0, hc] at h1
    have hs : B c' c = B c c' := hB.eq c' c
    rw [hs] at h1
    have h2 : B c c' • c - (2 : ZMod 3) • c' = 0 := by
      rcases (smul_eq_zero.mp h1.symm) with h | h
      · exact absurd h ha
      · exact h
    have h3 : (2 : ZMod 3) • c' = B c c' • c := (sub_eq_zero.mp h2).symm
    have hc'e := ggQ2xQ_eq_smul_of_smul_eq (by decide : (2 : ZMod 3) * 2 = 1) h3
    apply hne
    rw [ggQ2xQ_tc_eq_tc_iff B hB hc hc']
    rcases ggQ2xQ_zmod3_cases_of_sq (ggQ2xQ_zmod3_sq_eq_one ha) with h4 | h4
    · right; rw [hc'e, h4, show (2 : ZMod 3) * 1 = -1 by decide]
      exact neg_one_smul (ZMod 3) c
    · left; rw [hc'e, h4, show (2 : ZMod 3) * -1 = 1 by decide, one_smul]
  · intro ha
    ext v
    have h1 := ggQ2xQ_tc_comm_apply B hB c c' v
    rw [ha, zero_smul, sub_eq_zero] at h1
    simpa [Module.End.mul_apply] using h1

@[expose] noncomputable def ggQ2xQ_reflE {V : Type*} [AddCommGroup V] [Module (ZMod 3) V]
    (B : LinearMap.BilinForm (ZMod 3) V) (c : V) (h : B c c = 2) : V ≃ₗ[ZMod 3] V :=
  Module.reflection (f := B c) (x := c) h

@[simp] lemma ggQ2xQ_reflE_apply {V : Type*} [AddCommGroup V] [Module (ZMod 3) V]
    (B : LinearMap.BilinForm (ZMod 3) V) (c : V) (h : B c c = 2) (v : V) :
    ggQ2xQ_reflE B c h v = v - B c v • c := by
  rw [ggQ2xQ_reflE, Module.reflection_apply]

lemma ggQ2xQ_reflE_coe {V : Type*} [AddCommGroup V] [Module (ZMod 3) V]
    (B : LinearMap.BilinForm (ZMod 3) V) (c : V) (h : B c c = 2) :
    (ggQ2xQ_reflE B c h : V →ₗ[ZMod 3] V) = ggQ2xQ_tc B c := by
  ext v
  change ggQ2xQ_reflE B c h v = ggQ2xQ_tc B c v
  rw [ggQ2xQ_reflE_apply, ggQ2xQ_tc_apply]

end Refl

section Quandle

lemma ggQ2xQ_comm_iff_of_quandle {G : Type*} [Group G] (T : Set G)
    (hT : ∀ s ∈ T, ∀ t ∈ T, s * t * s⁻¹ ∈ T) (π : G → G) (hinj : Set.InjOn π T)
    (hπ : ∀ s ∈ T, ∀ t ∈ T, π (s * t * s⁻¹) = π s * π t * (π s)⁻¹)
    {s t : G} (hs : s ∈ T) (ht : t ∈ T) :
    s * t = t * s ↔ π s * π t = π t * π s := by
  have e1 : ∀ a b : G, a * b = b * a ↔ a * b * a⁻¹ = b := fun a b => by
    constructor
    · intro h; rw [h, mul_inv_cancel_right]
    · intro h; calc a * b = a * b * a⁻¹ * a := by group
        _ = b * a := by rw [h]
  rw [e1, e1, ← hπ s hs t ht]
  exact ⟨fun h => by rw [h], fun h => hinj (hT s hs t ht) ht h⟩

lemma ggQ2xQ_quandle_eq_conj_of_gen {G : Type*} [Group G] (S T : Set G)
    (hinv : ∀ s ∈ S, s⁻¹ = s) (hST : S ⊆ T)
    (hTc : ∀ w ∈ Subgroup.closure S, ∀ s ∈ S, w * s * w⁻¹ ∈ T) (π : G → G)
    (hπ : ∀ s ∈ T, ∀ t ∈ T, π (s * t * s⁻¹) = π s * π t * (π s)⁻¹) (g : G)
    (hg : ∀ s ∈ S, π s = g * s * g⁻¹) :
    ∀ w ∈ Subgroup.closure S, ∀ s ∈ S, π (w * s * w⁻¹) = g * (w * s * w⁻¹) * g⁻¹ := by
  intro w hw
  induction hw using Subgroup.closure_induction_left with
  | one => intro s hs; simpa using hg s hs
  | mul_left x hx y hy ih =>
    intro s hs
    have hyT : y * s * y⁻¹ ∈ T := hTc y hy s hs
    have e : x * y * s * (x * y)⁻¹ = x * (y * s * y⁻¹) * x⁻¹ := by group
    rw [e, hπ x (hST hx) _ hyT, ih s hs, hg x hx]
    group
  | inv_mul_cancel x hx y hy ih =>
    intro s hs
    rw [hinv x hx]
    have hyT : y * s * y⁻¹ ∈ T := hTc y hy s hs
    have e : x * y * s * (x * y)⁻¹ = x * (y * s * y⁻¹) * x⁻¹ := by group
    rw [e, hπ x (hST hx) _ hyT, ih s hs, hg x hx]
    group

end Quandle

section Integral

lemma ggQ2xQ_nonempty {p : ℕ} [Fact p.Prime] (D : GGQ2Lin p) : Nonempty D.ι := by
  obtain ⟨c, _⟩ := D.a_leaf
  exact ⟨c⟩

noncomputable def ggQ2xQ_basis {p : ℕ} [Fact p.Prime] (D : GGQ2Lin p) (hbas : D.Basis) :
    Module.Basis D.ι (ZMod p) D.V :=
  letI := ggQ2xQ_nonempty D
  Module.Basis.mk hbas.1
    (le_of_eq (LinearIndependent.span_eq_top_of_card_eq_finrank hbas.1 hbas.2).symm)

lemma ggQ2xQ_basis_apply {p : ℕ} [Fact p.Prime] (D : GGQ2Lin p) (hbas : D.Basis) (i : D.ι) :
    ggQ2xQ_basis D hbas i = D.coroot i := by
  rw [ggQ2xQ_basis, Module.Basis.mk_apply]

noncomputable def ggQ2xQ_form {p : ℕ} [Fact p.Prime] (D : GGQ2Lin p) (hbas : D.Basis) :
    LinearMap.BilinForm (ZMod p) D.V :=
  Matrix.toBilin (ggQ2xQ_basis D hbas) (D.cartan.map (Int.cast : ℤ → ZMod p))

lemma ggQ2xQ_form_coroot {p : ℕ} [Fact p.Prime] (D : GGQ2Lin p) (hbas : D.Basis)
    (i j : D.ι) :
    ggQ2xQ_form D hbas (D.coroot i) (D.coroot j) = (D.cartan i j : ZMod p) := by
  have hbij : (ggQ2xQ_basis D hbas).repr (D.coroot j) = Finsupp.single j 1 := by
    rw [← ggQ2xQ_basis_apply D hbas j, Module.Basis.repr_self]
  have hbii : (ggQ2xQ_basis D hbas).repr (D.coroot i) = Finsupp.single i 1 := by
    rw [← ggQ2xQ_basis_apply D hbas i, Module.Basis.repr_self]
  rw [ggQ2xQ_form, Matrix.toBilin_apply, hbii, hbij]
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single j]
    · simp [Matrix.map_apply]
    · intro j' _ hj'
      simp [Finsupp.single_eq_of_ne hj']
    · intro hj; exact absurd (Finset.mem_univ j) hj
  · intro i' _ hi'
    simp [Finsupp.single_eq_of_ne hi']
  · intro hi; exact absurd (Finset.mem_univ i) hi

lemma ggQ2xQ_form_root {p : ℕ} [Fact p.Prime] (D : GGQ2Lin p) (hbas : D.Basis) (i : D.ι) :
    ggQ2xQ_form D hbas (D.coroot i) = D.root i := by
  ext v
  conv_lhs => rw [← (ggQ2xQ_basis D hbas).sum_repr v]
  rw [map_sum]
  simp only [map_smul, smul_eq_mul, ggQ2xQ_basis_apply, ggQ2xQ_form_coroot]
  conv_rhs => rw [← (ggQ2xQ_basis D hbas).sum_repr v]
  rw [map_sum]
  simp only [map_smul, smul_eq_mul, ggQ2xQ_basis_apply, D.pairing]

lemma ggQ2xQ_form_isSymm {p : ℕ} [Fact p.Prime] (D : GGQ2Lin p) (hbas : D.Basis)
    (hCsym : ∀ i j, D.cartan i j = D.cartan j i) :
    (ggQ2xQ_form D hbas).IsSymm := by
  rw [LinearMap.BilinForm.isSymm_iff_basis (ggQ2xQ_basis D hbas)]
  intro i j
  rw [ggQ2xQ_basis_apply, ggQ2xQ_basis_apply, ggQ2xQ_form_coroot, ggQ2xQ_form_coroot, hCsym]

lemma ggQ2xQ_form_refl_preserve {V : Type*} [AddCommGroup V] [Module (ZMod 3) V]
    (B : LinearMap.BilinForm (ZMod 3) V) (hB : B.IsSymm) {c : V} (hc : B c c = 2) (x y : V) :
    B (ggQ2xQ_reflE B c hc x) (ggQ2xQ_reflE B c hc y) = B x y := by
  rw [ggQ2xQ_reflE_apply, ggQ2xQ_reflE_apply]
  simp only [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
  rw [hB.eq x c, hc]
  ring

lemma ggQ2xQ_form_simpleRefl (D : GGQ2Lin 3) (hbas : D.Basis)
    (hCsym : ∀ i j, D.cartan i j = D.cartan j i) (k : D.ι) (x y : D.V) :
    ggQ2xQ_form D hbas (D.simpleRefl k x) (D.simpleRefl k y) = ggQ2xQ_form D hbas x y := by
  have hk : (ggQ2xQ_form D hbas) (D.coroot k) (D.coroot k) = 2 := by
    rw [ggQ2xQ_form_coroot, D.isCartan.1]; norm_num
  have he : D.simpleRefl k = ggQ2xQ_reflE (ggQ2xQ_form D hbas) (D.coroot k) hk := by
    ext v
    rw [GGQ2Lin.simpleRefl, Module.reflection_apply, ggQ2xQ_reflE_apply, ggQ2xQ_form_root]
  rw [he]
  exact ggQ2xQ_form_refl_preserve _ (ggQ2xQ_form_isSymm D hbas hCsym) hk x y

lemma ggQ2xQ_form_preserve (D : GGQ2Lin 3) (hbas : D.Basis)
    (hCsym : ∀ i j, D.cartan i j = D.cartan j i) {w : D.V ≃ₗ[ZMod 3] D.V} (hw : w ∈ D.weyl) :
    ∀ x y, ggQ2xQ_form D hbas (w x) (w y) = ggQ2xQ_form D hbas x y := by
  have hgen : ∀ u ∈ D.simpleRefl '' Set.univ, ∀ x y,
      ggQ2xQ_form D hbas (u x) (u y) = ggQ2xQ_form D hbas x y := by
    rintro u ⟨k, -, rfl⟩
    exact ggQ2xQ_form_simpleRefl D hbas hCsym k
  have hw' : w ∈ Subgroup.closure (D.simpleRefl '' Set.univ) := by
    simpa [GGQ2Lin.weyl, GGQ2Lin.parab] using hw
  exact Subgroup.closure_induction (k := D.simpleRefl '' Set.univ)
    (p := fun u _ => ∀ x y, ggQ2xQ_form D hbas (u x) (u y) = ggQ2xQ_form D hbas x y)
    (fun u hu => hgen u hu) (fun x y => rfl)
    (fun a b _ _ iha ihb => by
      intro x y
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, iha, ihb])
    (fun a _ iha => by
      intro x y
      have h := iha (a⁻¹ x) (a⁻¹ y)
      rw [show a (a⁻¹ x) = x from by simp [LinearEquiv.coe_inv],
        show a (a⁻¹ y) = y from by simp [LinearEquiv.coe_inv]] at h
      exact h.symm) hw'

lemma ggQ2xQ_conj_simpleRefl (D : GGQ2Lin 3) (hbas : D.Basis)
    (hCsym : ∀ i j, D.cartan i j = D.cartan j i) (k : D.ι)
    {w : D.V ≃ₗ[ZMod 3] D.V} (hw : w ∈ D.weyl) :
    ∃ h : (ggQ2xQ_form D hbas) (w (D.coroot k)) (w (D.coroot k)) = 2,
      w * D.simpleRefl k * w⁻¹ = Module.reflection (f := ggQ2xQ_form D hbas (w (D.coroot k)))
        (x := w (D.coroot k)) h := by
  have h2 : (ggQ2xQ_form D hbas) (w (D.coroot k)) (w (D.coroot k)) = 2 := by
    rw [ggQ2xQ_form_preserve D hbas hCsym hw, ggQ2xQ_form_coroot, D.isCartan.1]; norm_num
  refine ⟨h2, ?_⟩
  ext v
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, GGQ2Lin.simpleRefl, Module.reflection_apply,
    Module.reflection_apply]
  have hb : (ggQ2xQ_form D hbas) (w (D.coroot k)) v = D.root k (w⁻¹ v) := by
    have h := ggQ2xQ_form_preserve D hbas hCsym hw (D.coroot k) (w⁻¹ v)
    rw [show w (w⁻¹ v) = v from by simp [LinearEquiv.coe_inv], ggQ2xQ_form_root] at h
    exact h
  rw [hb]
  simp only [map_sub, map_smul, LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply]

noncomputable def ggQ2xQ_intForm {p : ℕ} [Fact p.Prime] (D : GGQ2Lin p) :
    LinearMap.BilinForm ℤ (D.ι → ℤ) :=
  Matrix.toBilin' D.cartan

lemma ggQ2xQ_intForm_apply {p : ℕ} [Fact p.Prime] (D : GGQ2Lin p) (x y : D.ι → ℤ) :
    ggQ2xQ_intForm D x y = ∑ i, ∑ j, x i * D.cartan i j * y j := by
  rw [ggQ2xQ_intForm, Matrix.toBilin'_apply]

lemma ggQ2xQ_intForm_single_self {p : ℕ} [Fact p.Prime] (D : GGQ2Lin p) (k : D.ι) :
    ggQ2xQ_intForm D (Pi.single k 1) (Pi.single k 1) = 2 := by
  rw [ggQ2xQ_intForm_apply, Finset.sum_eq_single k]
  · rw [Finset.sum_eq_single k]
    · simp [D.isCartan.1]
    · intro j _ hj; simp [Pi.single_eq_of_ne hj]
    · intro hk; exact absurd (Finset.mem_univ k) hk
  · intro i _ hi; simp [Pi.single_eq_of_ne hi]
  · intro hk; exact absurd (Finset.mem_univ k) hk

noncomputable def ggQ2xQ_intRefl {p : ℕ} [Fact p.Prime] (D : GGQ2Lin p) (k : D.ι) :
    (D.ι → ℤ) ≃ₗ[ℤ] (D.ι → ℤ) :=
  Module.reflection (f := ggQ2xQ_intForm D (Pi.single k 1)) (x := Pi.single k (1 : ℤ))
    (ggQ2xQ_intForm_single_self D k)

lemma ggQ2xQ_intRefl_apply {p : ℕ} [Fact p.Prime] (D : GGQ2Lin p) (k : D.ι) (x : D.ι → ℤ) :
    ggQ2xQ_intRefl D k x =
      x - (ggQ2xQ_intForm D (Pi.single k 1) x) • Pi.single k (1 : ℤ) := by
  rw [ggQ2xQ_intRefl, Module.reflection_apply]

lemma ggQ2xQ_intRefl_self {p : ℕ} [Fact p.Prime] (D : GGQ2Lin p) (k : D.ι) :
    ggQ2xQ_intRefl D k (Pi.single k 1) = - Pi.single k 1 := by
  rw [ggQ2xQ_intRefl_apply, ggQ2xQ_intForm_single_self, two_smul]
  abel

noncomputable def ggQ2xQ_intWeyl {p : ℕ} [Fact p.Prime] (D : GGQ2Lin p) :
    Subgroup ((D.ι → ℤ) ≃ₗ[ℤ] (D.ι → ℤ)) :=
  Subgroup.closure (Set.range (ggQ2xQ_intRefl D))

def ggQ2xQ_IsRoot {p : ℕ} [Fact p.Prime] (D : GGQ2Lin p) (v : D.ι → ℤ) : Prop :=
  ∃ w ∈ ggQ2xQ_intWeyl D, ∃ k : D.ι, w (Pi.single k 1) = v

noncomputable def ggQ2xQ_rhoBar {p : ℕ} [Fact p.Prime] (D : GGQ2Lin p) :
    (D.ι → ℤ) →ₗ[ℤ] D.V where
  toFun x := ∑ k, (x k : ZMod p) • D.coroot k
  map_add' x y := by
    simp only [Pi.add_apply, Int.cast_add, add_smul, Finset.sum_add_distrib]
  map_smul' m x := by
    simp only [Pi.smul_apply, smul_eq_mul, Int.cast_mul, RingHom.id_apply, mul_smul,
      Finset.smul_sum, Int.cast_smul_eq_zsmul (ZMod p)]

lemma ggQ2xQ_rhoBar_single {p : ℕ} [Fact p.Prime] (D : GGQ2Lin p) (k : D.ι) :
    ggQ2xQ_rhoBar D (Pi.single k 1) = D.coroot k := by
  rw [ggQ2xQ_rhoBar]
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  rw [Finset.sum_eq_single k]
  · simp
  · intro i _ hi; simp [Pi.single_eq_of_ne hi]
  · intro hk; exact absurd (Finset.mem_univ k) hk

lemma ggQ2xQ_intRefl_mem_intWeyl {p : ℕ} [Fact p.Prime] (D : GGQ2Lin p) (k : D.ι) :
    ggQ2xQ_intRefl D k ∈ ggQ2xQ_intWeyl D :=
  Subgroup.subset_closure ⟨k, rfl⟩

lemma ggQ2xQ_single_isRoot {p : ℕ} [Fact p.Prime] (D : GGQ2Lin p) (k : D.ι) :
    ggQ2xQ_IsRoot D (Pi.single k 1) :=
  ⟨1, (ggQ2xQ_intWeyl D).one_mem, k, by simp⟩

lemma ggQ2xQ_IsRoot_neg {p : ℕ} [Fact p.Prime] (D : GGQ2Lin p) {v : D.ι → ℤ}
    (hv : ggQ2xQ_IsRoot D v) : ggQ2xQ_IsRoot D (-v) := by
  obtain ⟨w, hw, k, hk⟩ := hv
  refine ⟨w * ggQ2xQ_intRefl D k, Subgroup.mul_mem _ hw (ggQ2xQ_intRefl_mem_intWeyl D k), k, ?_⟩
  rw [LinearEquiv.mul_apply, ggQ2xQ_intRefl_self, map_neg, hk]

end Integral

section QuandleAssembly

def ggQ2xQ_IsE {p : ℕ} [Fact p.Prime] (D : GGQ2Lin p) : Prop :=
  (∃ e : Fin 6 ≃ D.ι, D.coxeter = CoxeterMatrix.E₆.reindex e) ∨
  (∃ e : Fin 7 ≃ D.ι, D.coxeter = CoxeterMatrix.E₇.reindex e) ∨
  (∃ e : Fin 8 ≃ D.ι, D.coxeter = CoxeterMatrix.E₈.reindex e)

theorem ggQ2xQ_cartan_symm_of_reindex {n : ℕ} (M : CoxeterMatrix (Fin n))
    (hM : ∀ a b, M a b ≤ 3) (D : GGQ2Lin 3) (e : Fin n ≃ D.ι)
    (he : D.coxeter = M.reindex e) : ∀ i j, D.cartan i j = D.cartan j i := by
  intro i j
  by_cases hij : i = j
  · subst hij; rw [D.isCartan.1]
  · have hcox : D.coxeter i j = M (e.symm i) (e.symm j) := by
      rw [he, CoxeterMatrix.reindex_apply]
    rcases D.isCartan.2 i j hij with ⟨hm, h1, h2⟩ | ⟨hm, h1, h2⟩ | ⟨hm, h1, -⟩ | ⟨hm, h1, -⟩
    · rw [h1, h2]
    · rw [h1, h2]
    · exfalso; rw [hcox] at hm; have := hM (e.symm i) (e.symm j); omega
    · exfalso; rw [hcox] at hm; have := hM (e.symm i) (e.symm j); omega

theorem ggQ2xQ_cartan_symm_of_E (D : GGQ2Lin 3) (hE : ggQ2xQ_IsE D) :
    ∀ i j, D.cartan i j = D.cartan j i := by
  rcases hE with ⟨e, he⟩ | ⟨e, he⟩ | ⟨e, he⟩
  · exact ggQ2xQ_cartan_symm_of_reindex CoxeterMatrix.E₆
      (by intro a b; fin_cases a <;> fin_cases b <;> decide) D e he
  · exact ggQ2xQ_cartan_symm_of_reindex CoxeterMatrix.E₇
      (by intro a b; fin_cases a <;> fin_cases b <;> decide) D e he
  · exact ggQ2xQ_cartan_symm_of_reindex CoxeterMatrix.E₈
      (by intro a b; fin_cases a <;> fin_cases b <;> decide) D e he

theorem ggQ2xQ_cartan_of_reindex {n : ℕ} (M : CoxeterMatrix (Fin n))
    (hM : ∀ a b, M a b ≤ 3) (D : GGQ2Lin 3) (e : Fin n ≃ D.ι)
    (he : D.coxeter = M.reindex e) (C : Matrix (Fin n) (Fin n) ℤ) (hCdiag : ∀ a, C a a = 2)
    (hM0 : ∀ a b, M a b = 2 ↔ C a b = 0) (hM1 : ∀ a b, M a b = 3 ↔ C a b = -1) :
    ∀ a b, D.cartan (e a) (e b) = C a b := by
  intro a b
  by_cases hab : a = b
  · subst hab; rw [D.isCartan.1, hCdiag]
  · have hab' : e a ≠ e b := fun h => hab (e.injective h)
    have hcox : D.coxeter (e a) (e b) = M a b := by
      rw [he, CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    rcases D.isCartan.2 (e a) (e b) hab' with ⟨hm, h1, -⟩ | ⟨hm, h1, -⟩ | ⟨hm, -, -⟩ | ⟨hm, -, -⟩
    · rw [hcox] at hm
      rw [h1, (hM0 a b).1 hm]
    · rw [hcox] at hm
      rw [h1, (hM1 a b).1 hm]
    · exfalso; rw [hcox] at hm; have := hM a b; omega
    · exfalso; rw [hcox] at hm; have := hM a b; omega

theorem ggQ2xQ_cartan_E6 (D : GGQ2Lin 3) (e : Fin 6 ≃ D.ι)
    (he : D.coxeter = CoxeterMatrix.E₆.reindex e) :
    ∀ a b, D.cartan (e a) (e b) = CartanMatrix.E 6 a b :=
  ggQ2xQ_cartan_of_reindex CoxeterMatrix.E₆
    (by intro a b; fin_cases a <;> fin_cases b <;> decide) D e he (CartanMatrix.E 6)
    (by intro a; fin_cases a <;> decide)
    (by intro a b; fin_cases a <;> fin_cases b <;> decide)
    (by intro a b; fin_cases a <;> fin_cases b <;> decide)

theorem ggQ2xQ_cartan_E7 (D : GGQ2Lin 3) (e : Fin 7 ≃ D.ι)
    (he : D.coxeter = CoxeterMatrix.E₇.reindex e) :
    ∀ a b, D.cartan (e a) (e b) = CartanMatrix.E 7 a b :=
  ggQ2xQ_cartan_of_reindex CoxeterMatrix.E₇
    (by intro a b; fin_cases a <;> fin_cases b <;> decide) D e he (CartanMatrix.E 7)
    (by intro a; fin_cases a <;> decide)
    (by intro a b; fin_cases a <;> fin_cases b <;> decide)
    (by intro a b; fin_cases a <;> fin_cases b <;> decide)

theorem ggQ2xQ_cartan_E8 (D : GGQ2Lin 3) (e : Fin 8 ≃ D.ι)
    (he : D.coxeter = CoxeterMatrix.E₈.reindex e) :
    ∀ a b, D.cartan (e a) (e b) = CartanMatrix.E 8 a b :=
  ggQ2xQ_cartan_of_reindex CoxeterMatrix.E₈
    (by intro a b; fin_cases a <;> fin_cases b <;> decide) D e he (CartanMatrix.E 8)
    (by intro a; fin_cases a <;> decide)
    (by intro a b; fin_cases a <;> fin_cases b <;> decide)
    (by intro a b; fin_cases a <;> fin_cases b <;> decide)

lemma ggQ2xQ_simpleRefl_mem_weyl (D : GGQ2Lin 3) (k : D.ι) : D.simpleRefl k ∈ D.weyl := by
  rw [GGQ2Lin.weyl, GGQ2Lin.parab]
  exact Subgroup.subset_closure ⟨k, Set.mem_univ k, rfl⟩

lemma ggQ2xQ_simpleRefl_isReflLin (D : GGQ2Lin 3) (k : D.ι) :
    IsReflLin (D.simpleRefl k) :=
  ⟨D.coroot k, D.root k, D.root_coroot_self k, rfl⟩

lemma ggQ2xQ_inv_simpleRefl (D : GGQ2Lin 3) (k : D.ι) :
    (D.simpleRefl k)⁻¹ = D.simpleRefl k := by
  refine inv_eq_of_mul_eq_one_right ?_
  ext v
  exact Module.involutive_reflection (D.root_coroot_self k) v

lemma ggQ2xQ_mem_weyl_iff (D : GGQ2Lin 3) {w : D.V ≃ₗ[ZMod 3] D.V} :
    w ∈ D.weyl ↔ w ∈ Subgroup.closure (Set.range D.simpleRefl) := by
  simp [GGQ2Lin.weyl, GGQ2Lin.parab]

@[expose] def ggQ2xQ_isConjRefl (D : GGQ2Lin 3) : Set (D.V ≃ₗ[ZMod 3] D.V) :=
  {t | ∃ (k : D.ι) (w : D.V ≃ₗ[ZMod 3] D.V), w ∈ D.weyl ∧ t = w * D.simpleRefl k * w⁻¹}

lemma ggQ2xQ_simpleRefl_mem_isConjRefl (D : GGQ2Lin 3) (k : D.ι) :
    D.simpleRefl k ∈ ggQ2xQ_isConjRefl D :=
  ⟨k, 1, Subgroup.one_mem _, by simp⟩

private lemma ggQ2xQ_Q23_intForm_single_left {p : ℕ} [Fact p.Prime] (D : GGQ2Lin p) (k : D.ι)
    (x : D.ι → ℤ) :
    ggQ2xQ_intForm D (Pi.single k 1) x = ∑ j, D.cartan k j * x j := by
  rw [ggQ2xQ_intForm_apply, Finset.sum_eq_single k]
  · simp
  · intro i _ hi
    simp [Pi.single_eq_of_ne hi]
  · intro hk; exact absurd (Finset.mem_univ k) hk

private lemma ggQ2xQ_Q23_root_rhoBar {p : ℕ} [Fact p.Prime] (D : GGQ2Lin p) (k : D.ι)
    (x : D.ι → ℤ) :
    D.root k (ggQ2xQ_rhoBar D x) = ((ggQ2xQ_intForm D (Pi.single k 1) x : ℤ) : ZMod p) := by
  rw [ggQ2xQ_Q23_intForm_single_left, ggQ2xQ_rhoBar]
  simp only [LinearMap.coe_mk, AddHom.coe_mk, map_sum, map_smul, smul_eq_mul, D.pairing,
    Int.cast_sum, Int.cast_mul]
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

private lemma ggQ2xQ_Q23_red_gen {p : ℕ} [Fact p.Prime] (D : GGQ2Lin p) (k : D.ι)
    (x : D.ι → ℤ) :
    ggQ2xQ_rhoBar D (ggQ2xQ_intRefl D k x) = D.simpleRefl k (ggQ2xQ_rhoBar D x) := by
  rw [ggQ2xQ_intRefl_apply, map_sub, map_smul, ggQ2xQ_rhoBar_single, GGQ2Lin.simpleRefl,
    Module.reflection_apply, ggQ2xQ_Q23_root_rhoBar]
  congr 1
  exact (Int.cast_smul_eq_zsmul (ZMod p) (ggQ2xQ_intForm D (Pi.single k 1) x)
    (D.coroot k)).symm

private lemma ggQ2xQ_Q23_intForm_isSymm (D : GGQ2Lin 3) (hE : ggQ2xQ_IsE D) :
    (ggQ2xQ_intForm D).IsSymm := by
  rw [ggQ2xQ_intForm, Matrix.isSymm_toBilin'_iff_isSymm]
  exact Matrix.IsSymm.ext (fun i j => ggQ2xQ_cartan_symm_of_E D hE j i)

private lemma ggQ2xQ_Q23_intForm_refl_preserve {p : ℕ} [Fact p.Prime] (D : GGQ2Lin p)
    (hB : (ggQ2xQ_intForm D).IsSymm) {c : D.ι → ℤ} (hc : ggQ2xQ_intForm D c c = 2)
    (x y : D.ι → ℤ) :
    ggQ2xQ_intForm D (Module.reflection (f := ggQ2xQ_intForm D c) (x := c) hc x)
      (Module.reflection (f := ggQ2xQ_intForm D c) (x := c) hc y) = ggQ2xQ_intForm D x y := by
  rw [Module.reflection_apply, Module.reflection_apply]
  simp only [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
  rw [hB.eq x c, hc]
  ring

private lemma ggQ2xQ_Q23_intRefl_preserve (D : GGQ2Lin 3) (hE : ggQ2xQ_IsE D) (k : D.ι)
    (x y : D.ι → ℤ) :
    ggQ2xQ_intForm D (ggQ2xQ_intRefl D k x) (ggQ2xQ_intRefl D k y) = ggQ2xQ_intForm D x y :=
  ggQ2xQ_Q23_intForm_refl_preserve D (ggQ2xQ_Q23_intForm_isSymm D hE)
    (ggQ2xQ_intForm_single_self D k) x y

private lemma ggQ2xQ_Q23_intWeyl_preserve (D : GGQ2Lin 3) (hE : ggQ2xQ_IsE D)
    {u : (D.ι → ℤ) ≃ₗ[ℤ] (D.ι → ℤ)} (hu : u ∈ ggQ2xQ_intWeyl D) (x y : D.ι → ℤ) :
    ggQ2xQ_intForm D (u x) (u y) = ggQ2xQ_intForm D x y := by
  have hgen : ∀ r ∈ Set.range (ggQ2xQ_intRefl D), ∀ x y,
      ggQ2xQ_intForm D (r x) (r y) = ggQ2xQ_intForm D x y := by
    rintro r ⟨k, rfl⟩
    exact ggQ2xQ_Q23_intRefl_preserve D hE k
  have hu' : u ∈ Subgroup.closure (Set.range (ggQ2xQ_intRefl D)) := by
    simpa [ggQ2xQ_intWeyl] using hu
  exact Subgroup.closure_induction (k := Set.range (ggQ2xQ_intRefl D))
    (p := fun u _ => ∀ x y, ggQ2xQ_intForm D (u x) (u y) = ggQ2xQ_intForm D x y)
    (fun u hu => hgen u hu) (fun x y => rfl)
    (fun a b _ _ iha ihb => by
      intro x y
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, iha, ihb])
    (fun a _ iha => by
      intro x y
      have h := iha (a⁻¹ x) (a⁻¹ y)
      rw [show a (a⁻¹ x) = x from by simp [LinearEquiv.coe_inv],
        show a (a⁻¹ y) = y from by simp [LinearEquiv.coe_inv]] at h
      exact h.symm) hu' x y

private lemma ggQ2xQ_Q23_intForm_self_root (D : GGQ2Lin 3) (hE : ggQ2xQ_IsE D)
    {γ : D.ι → ℤ} (hγ : ggQ2xQ_IsRoot D γ) : ggQ2xQ_intForm D γ γ = 2 := by
  obtain ⟨w, hw, k, hk⟩ := hγ
  rw [← hk, ggQ2xQ_Q23_intWeyl_preserve D hE hw, ggQ2xQ_intForm_single_self]

private lemma ggQ2xQ_Q23_posDef_of_reindex {n : ℕ} (D : GGQ2Lin 3) (e : Fin n ≃ D.ι)
    (M : Matrix (Fin n) (Fin n) ℤ) (hcart : ∀ a b, D.cartan (e a) (e b) = M a b)
    (hpos : (M.map (Int.cast : ℤ → ℚ)).PosDef) :
    ∀ x : D.ι → ℚ, x ≠ 0 → 0 < ∑ i, ∑ j, x i * (D.cartan i j : ℚ) * x j := by
  intro x hx
  set y : Fin n → ℚ := fun a => x (e a) with hy
  have hyne : y ≠ 0 := by
    intro h
    apply hx
    funext i
    have h' := congr_fun h (e.symm i)
    simpa [hy] using h'
  have hdot := Matrix.PosDef.dotProduct_mulVec_pos hpos hyne
  rw [star_trivial] at hdot
  have hsum1 : y ⬝ᵥ (M.map (Int.cast : ℤ → ℚ)).mulVec y
      = ∑ a, ∑ b, y a * (M a b : ℚ) * y b := by
    rw [Matrix.dot_mulVec_eq_sum_sum, Finset.sum_comm]
    simp [Matrix.map_apply]
  have hsum2 : (∑ i, ∑ j, x i * (D.cartan i j : ℚ) * x j)
      = ∑ a, ∑ b, y a * (M a b : ℚ) * y b := by
    rw [← Equiv.sum_comp e (fun i => ∑ j, x i * (D.cartan i j : ℚ) * x j)]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [← Equiv.sum_comp e (fun j => x (e a) * (D.cartan (e a) j : ℚ) * x j)]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [hcart a b]
  rw [hsum2, ← hsum1]
  exact hdot

private lemma ggQ2xQ_Q23_intForm_pos (D : GGQ2Lin 3)
    (hpd : ∀ x : D.ι → ℚ, x ≠ 0 → 0 < ∑ i, ∑ j, x i * (D.cartan i j : ℚ) * x j)
    {v : D.ι → ℤ} (hv : v ≠ 0) : 0 < ggQ2xQ_intForm D v v := by
  have hvq : (fun i => (v i : ℚ)) ≠ 0 := by
    intro h
    apply hv
    funext i
    have h' : (v i : ℚ) = 0 := by simpa using congr_fun h i
    exact_mod_cast h'
  have h := hpd (fun i => (v i : ℚ)) hvq
  have hcast : ((∑ i, ∑ j, v i * D.cartan i j * v j : ℤ) : ℚ)
      = ∑ i, ∑ j, (v i : ℚ) * (D.cartan i j : ℚ) * (v j : ℚ) := by
    push_cast
    ring
  rw [← hcast] at h
  rw [ggQ2xQ_intForm_apply]
  exact_mod_cast h

private lemma ggQ2xQ_Q23_red_surj (D : GGQ2Lin 3) (hbas : D.Basis) (hE : ggQ2xQ_IsE D) :
    ∀ w ∈ D.weyl, ∃ u : ggQ2xQ_intWeyl D,
      ∀ x : D.ι → ℤ, ggQ2xQ_rhoBar D ((u : (D.ι → ℤ) ≃ₗ[ℤ] (D.ι → ℤ)) x) =
        w (ggQ2xQ_rhoBar D x) := by
  intro w hw
  have hw' : w ∈ Subgroup.closure (Set.range D.simpleRefl) := by
    simpa [GGQ2Lin.weyl, GGQ2Lin.parab] using hw
  refine Subgroup.closure_induction (k := Set.range D.simpleRefl)
    (p := fun v _ => ∃ u : ggQ2xQ_intWeyl D,
      ∀ x : D.ι → ℤ, ggQ2xQ_rhoBar D ((u : (D.ι → ℤ) ≃ₗ[ℤ] (D.ι → ℤ)) x) =
        v (ggQ2xQ_rhoBar D x)) ?_ ?_ ?_ ?_ hw'
  · rintro v ⟨k, rfl⟩
    exact ⟨⟨ggQ2xQ_intRefl D k, ggQ2xQ_intRefl_mem_intWeyl D k⟩,
      fun x => ggQ2xQ_Q23_red_gen D k x⟩
  · exact ⟨1, fun x => by simp⟩
  · intro a b ha hb iha ihb
    obtain ⟨ua, hua⟩ := iha
    obtain ⟨ub, hub⟩ := ihb
    refine ⟨ua * ub, fun x => ?_⟩
    change ggQ2xQ_rhoBar D ((↑ua * ↑ub : (D.ι → ℤ) ≃ₗ[ℤ] (D.ι → ℤ)) x) =
      a (b (ggQ2xQ_rhoBar D x))
    rw [LinearEquiv.mul_apply, hua, hub]
  · intro a ha iha
    obtain ⟨u, hu⟩ := iha
    refine ⟨u⁻¹, fun x => ?_⟩
    have h := hu ((↑(u⁻¹) : (D.ι → ℤ) ≃ₗ[ℤ] (D.ι → ℤ)) x)
    have h' : (↑u : (D.ι → ℤ) ≃ₗ[ℤ] (D.ι → ℤ))
        ((↑(u⁻¹) : (D.ι → ℤ) ≃ₗ[ℤ] (D.ι → ℤ)) x) = x := by
      rw [show (↑(u⁻¹) : (D.ι → ℤ) ≃ₗ[ℤ] (D.ι → ℤ)) = (↑u)⁻¹ from rfl]
      exact LinearEquiv.apply_symm_apply (↑u : (D.ι → ℤ) ≃ₗ[ℤ] (D.ι → ℤ)) x
    rw [h'] at h
    rw [h]
    simp

private theorem ggQ2xQ_Q2_lift (D : GGQ2Lin 3) (hbas : D.Basis) (hE : ggQ2xQ_IsE D) :
    ∀ t ∈ ggQ2xQ_isConjRefl D, ∃ γ : D.ι → ℤ, ggQ2xQ_IsRoot D γ ∧
      ∃ h : (ggQ2xQ_form D hbas) (ggQ2xQ_rhoBar D γ) (ggQ2xQ_rhoBar D γ) = 2,
        t = Module.reflection (f := ggQ2xQ_form D hbas (ggQ2xQ_rhoBar D γ))
          (x := ggQ2xQ_rhoBar D γ) h := by
  intro t ht
  obtain ⟨k, w, hw, htw⟩ := ht
  have hCsym := ggQ2xQ_cartan_symm_of_E D hE
  obtain ⟨h2, heq⟩ := ggQ2xQ_conj_simpleRefl D hbas hCsym k hw
  obtain ⟨u, hu⟩ := ggQ2xQ_Q23_red_surj D hbas hE w hw
  refine ⟨(u : (D.ι → ℤ) ≃ₗ[ℤ] (D.ι → ℤ)) (Pi.single k 1),
    ⟨u, u.2, k, rfl⟩, ?_⟩
  have hργ : ggQ2xQ_rhoBar D ((u : (D.ι → ℤ) ≃ₗ[ℤ] (D.ι → ℤ)) (Pi.single k 1)) =
      w (D.coroot k) := (hu (Pi.single k 1)).trans (by rw [ggQ2xQ_rhoBar_single])
  refine ⟨hργ.symm ▸ h2, ?_⟩
  rw [htw, heq]
  ext v
  rw [Module.reflection_apply, Module.reflection_apply, hργ]

private theorem ggQ2xQ_Q2_red (D : GGQ2Lin 3) (hbas : D.Basis) (hE : ggQ2xQ_IsE D) :
    ∀ u : ggQ2xQ_intWeyl D, ∃ g ∈ D.weyl,
      ∀ x : D.ι → ℤ,
        ggQ2xQ_rhoBar D ((u : (D.ι → ℤ) ≃ₗ[ℤ] (D.ι → ℤ)) x) = g (ggQ2xQ_rhoBar D x) := by
  intro u
  refine Subgroup.closure_induction (k := Set.range (ggQ2xQ_intRefl D))
    (p := fun v _ => ∃ g ∈ D.weyl,
      ∀ x : D.ι → ℤ, ggQ2xQ_rhoBar D (v x) = g (ggQ2xQ_rhoBar D x)) ?_ ?_ ?_ ?_ u.2
  · rintro v ⟨k, rfl⟩
    exact ⟨D.simpleRefl k, ggQ2xQ_simpleRefl_mem_weyl D k,
      fun x => ggQ2xQ_Q23_red_gen D k x⟩
  · exact ⟨1, D.weyl.one_mem, fun x => by simp⟩
  · intro a b ha hb iha ihb
    obtain ⟨ga, hga, hia⟩ := iha
    obtain ⟨gb, hgb, hib⟩ := ihb
    refine ⟨ga * gb, Subgroup.mul_mem _ hga hgb, fun x => ?_⟩
    rw [LinearEquiv.mul_apply, hia, hib, LinearEquiv.mul_apply]
  · intro a ha iha
    obtain ⟨g, hg, hi⟩ := iha
    refine ⟨g⁻¹, Subgroup.inv_mem _ hg, fun x => ?_⟩
    have h := hi (a⁻¹ x)
    rw [show a (a⁻¹ x) = x from by simp [LinearEquiv.coe_inv]] at h
    rw [h]
    simp

private theorem ggQ2xQ_Q3 (D : GGQ2Lin 3) (hbas : D.Basis) (hE : ggQ2xQ_IsE D) :
    (∀ x : D.ι → ℚ, x ≠ 0 → 0 < ∑ i, ∑ j, x i * (D.cartan i j : ℚ) * x j) ∧
    (∀ γ δ : D.ι → ℤ, ggQ2xQ_IsRoot D γ → ggQ2xQ_IsRoot D δ → γ ≠ δ → γ ≠ -δ →
      (∑ i, ∑ j, γ i * D.cartan i j * δ j) ∈ ({-1, 0, 1} : Set ℤ)) := by
  have hpd : ∀ x : D.ι → ℚ, x ≠ 0 → 0 < ∑ i, ∑ j, x i * (D.cartan i j : ℚ) * x j := by
    rcases hE with ⟨e, he⟩ | ⟨e, he⟩ | ⟨e, he⟩
    · exact ggQ2xQ_Q23_posDef_of_reindex D e (CartanMatrix.E 6) (ggQ2xQ_cartan_E6 D e he)
        TauCeti.posDef_map_intCast_cartanMatrix_E6
    · exact ggQ2xQ_Q23_posDef_of_reindex D e (CartanMatrix.E 7) (ggQ2xQ_cartan_E7 D e he)
        TauCeti.posDef_map_intCast_cartanMatrix_E7
    · exact ggQ2xQ_Q23_posDef_of_reindex D e (CartanMatrix.E 8) (ggQ2xQ_cartan_E8 D e he)
        TauCeti.posDef_map_intCast_cartanMatrix_E8
  refine ⟨hpd, ?_⟩
  intro γ δ hγ hδ hne hne'
  have hB := ggQ2xQ_Q23_intForm_isSymm D hE
  have hγγ := ggQ2xQ_Q23_intForm_self_root D hE hγ
  have hδδ := ggQ2xQ_Q23_intForm_self_root D hE hδ
  have hγδ : γ + δ ≠ 0 := fun h => hne' (eq_neg_of_add_eq_zero_left h)
  have hγmδ : γ - δ ≠ 0 := fun h => hne (sub_eq_zero.mp h)
  have hp1 : 0 < ggQ2xQ_intForm D (γ + δ) (γ + δ) := ggQ2xQ_Q23_intForm_pos D hpd hγδ
  have hp2 : 0 < ggQ2xQ_intForm D (γ - δ) (γ - δ) := ggQ2xQ_Q23_intForm_pos D hpd hγmδ
  have e1 : ggQ2xQ_intForm D (γ + δ) (γ + δ) = 4 + 2 * ggQ2xQ_intForm D γ δ := by
    simp only [map_add, LinearMap.add_apply]
    rw [hγγ, hδδ, hB.eq δ γ]
    ring
  have e2 : ggQ2xQ_intForm D (γ - δ) (γ - δ) = 4 - 2 * ggQ2xQ_intForm D γ δ := by
    simp only [map_sub, LinearMap.sub_apply]
    rw [hγγ, hδδ, hB.eq δ γ]
    ring
  rw [e1] at hp1
  rw [e2] at hp2
  have hmem : ggQ2xQ_intForm D γ δ ∈ ({-1, 0, 1} : Set ℤ) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    omega
  rwa [ggQ2xQ_intForm_apply] at hmem

lemma ggQ2xQ4_intForm_isSymm (D : GGQ2Lin 3)
    (hCsym : ∀ i j, D.cartan i j = D.cartan j i) :
    (ggQ2xQ_intForm D).IsSymm := by
  refine ⟨fun x y => ?_⟩
  rw [ggQ2xQ_intForm_apply, ggQ2xQ_intForm_apply, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  rw [hCsym i j]
  ring

noncomputable def ggQ2xQ4_intFormQ (D : GGQ2Lin 3) :
    LinearMap.BilinForm ℚ (D.ι → ℚ) :=
  Matrix.toBilin' (D.cartan.map (Int.cast : ℤ → ℚ))

lemma ggQ2xQ4_intFormQ_apply (D : GGQ2Lin 3) (x y : D.ι → ℚ) :
    ggQ2xQ4_intFormQ D x y = ∑ i, ∑ j, x i * (D.cartan i j : ℚ) * y j := by
  rw [ggQ2xQ4_intFormQ, Matrix.toBilin'_apply]
  simp only [Matrix.map_apply]

lemma ggQ2xQ4_intFormQ_intCast (D : GGQ2Lin 3) (x y : D.ι → ℤ) :
    ggQ2xQ4_intFormQ D (fun i => (x i : ℚ)) (fun i => (y i : ℚ)) =
      ((ggQ2xQ_intForm D x y : ℤ) : ℚ) := by
  rw [ggQ2xQ4_intFormQ_apply, ggQ2xQ_intForm_apply]
  push_cast
  ring

lemma ggQ2xQ4_intFormQ_posDef (D : GGQ2Lin 3) (hbas : D.Basis) (hE : ggQ2xQ_IsE D)
    {x : D.ι → ℚ} (hx : x ≠ 0) : 0 < ggQ2xQ4_intFormQ D x x := by
  rw [ggQ2xQ4_intFormQ_apply]
  exact (ggQ2xQ_Q3 D hbas hE).1 x hx

noncomputable def ggQ2xQ4_reflOf (D : GGQ2Lin 3) (v : D.ι → ℤ)
    (h : ggQ2xQ_intForm D v v = 2) : (D.ι → ℤ) ≃ₗ[ℤ] (D.ι → ℤ) :=
  Module.reflection (f := ggQ2xQ_intForm D v) (x := v) h

@[simp] lemma ggQ2xQ4_reflOf_apply (D : GGQ2Lin 3) (v : D.ι → ℤ)
    (h : ggQ2xQ_intForm D v v = 2) (x : D.ι → ℤ) :
    ggQ2xQ4_reflOf D v h x = x - (ggQ2xQ_intForm D v x) • v := by
  rw [ggQ2xQ4_reflOf, Module.reflection_apply]

lemma ggQ2xQ4_intRefl_eq_reflOf (D : GGQ2Lin 3) (k : D.ι) :
    ggQ2xQ_intRefl D k =
      ggQ2xQ4_reflOf D (Pi.single k 1) (ggQ2xQ_intForm_single_self D k) := by
  ext x
  rw [ggQ2xQ4_reflOf_apply, ggQ2xQ_intRefl_apply]

lemma ggQ2xQ4_intForm_refl_preserve (D : GGQ2Lin 3)
    (hB : (ggQ2xQ_intForm D).IsSymm) {v : D.ι → ℤ}
    (hv : ggQ2xQ_intForm D v v = 2) (x y : D.ι → ℤ) :
    ggQ2xQ_intForm D (ggQ2xQ4_reflOf D v hv x) (ggQ2xQ4_reflOf D v hv y) =
      ggQ2xQ_intForm D x y := by
  rw [ggQ2xQ4_reflOf_apply, ggQ2xQ4_reflOf_apply]
  simp only [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
  rw [hB.eq x v, hv]
  ring

lemma ggQ2xQ4_intForm_preserve (D : GGQ2Lin 3)
    (hCsym : ∀ i j, D.cartan i j = D.cartan j i) {w : (D.ι → ℤ) ≃ₗ[ℤ] (D.ι → ℤ)}
    (hw : w ∈ ggQ2xQ_intWeyl D) (x y : D.ι → ℤ) :
    ggQ2xQ_intForm D (w x) (w y) = ggQ2xQ_intForm D x y := by
  have hB := ggQ2xQ4_intForm_isSymm D hCsym
  have hgen : ∀ u ∈ Set.range (ggQ2xQ_intRefl D), ∀ x y,
      ggQ2xQ_intForm D (u x) (u y) = ggQ2xQ_intForm D x y := by
    rintro u ⟨k, rfl⟩ x y
    rw [ggQ2xQ4_intRefl_eq_reflOf]
    exact ggQ2xQ4_intForm_refl_preserve D hB (ggQ2xQ_intForm_single_self D k) x y
  have hw' : w ∈ Subgroup.closure (Set.range (ggQ2xQ_intRefl D)) := hw
  exact Subgroup.closure_induction (k := Set.range (ggQ2xQ_intRefl D))
    (p := fun u _ => ∀ x y, ggQ2xQ_intForm D (u x) (u y) = ggQ2xQ_intForm D x y)
    (fun u hu => hgen u hu) (fun x y => rfl)
    (fun a b _ _ iha ihb => by
      intro x y
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, iha, ihb])
    (fun a _ iha => by
      intro x y
      have h := iha (a⁻¹ x) (a⁻¹ y)
      rw [show a (a⁻¹ x) = x from by simp [LinearEquiv.coe_inv],
        show a (a⁻¹ y) = y from by simp [LinearEquiv.coe_inv]] at h
      exact h.symm) hw' x y

lemma ggQ2xQ4_intForm_self_isRoot (D : GGQ2Lin 3)
    (hCsym : ∀ i j, D.cartan i j = D.cartan j i) {v : D.ι → ℤ}
    (hv : ggQ2xQ_IsRoot D v) : ggQ2xQ_intForm D v v = 2 := by
  obtain ⟨w, hw, k, rfl⟩ := hv
  rw [ggQ2xQ4_intForm_preserve D hCsym hw]
  exact ggQ2xQ_intForm_single_self D k

lemma ggQ2xQ4_intForm_single (D : GGQ2Lin 3) (i j : D.ι) :
    ggQ2xQ_intForm D (Pi.single i 1) (Pi.single j 1) = D.cartan i j := by
  rw [ggQ2xQ_intForm_apply, Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb
      rw [Pi.single_eq_of_ne hb, mul_zero]
    · intro hj; exact absurd (Finset.mem_univ j) hj
  · intro a _ ha
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [Pi.single_eq_of_ne ha, zero_mul, zero_mul]
  · intro hi; exact absurd (Finset.mem_univ i) hi

lemma ggQ2xQ4_single_nonneg (D : GGQ2Lin 3) (k : D.ι) :
    ∀ j, 0 ≤ (Pi.single k (1:ℤ) : D.ι → ℤ) j := by
  intro j
  by_cases hjk : j = k
  · rw [hjk, Pi.single_eq_same]
    exact Int.one_nonneg
  · rw [Pi.single_eq_of_ne hjk]

lemma ggQ2xQ4_reflOf_mem_intWeyl (D : GGQ2Lin 3)
    (hCsym : ∀ i j, D.cartan i j = D.cartan j i) {v : D.ι → ℤ}
    (hv : ggQ2xQ_IsRoot D v) (h : ggQ2xQ_intForm D v v = 2) :
    ggQ2xQ4_reflOf D v h ∈ ggQ2xQ_intWeyl D := by
  obtain ⟨w, hw, k, rfl⟩ := hv
  have heq : ggQ2xQ4_reflOf D (w (Pi.single k 1)) h =
      w * ggQ2xQ_intRefl D k * w⁻¹ := by
    ext x
    rw [ggQ2xQ4_reflOf_apply, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
      ggQ2xQ_intRefl_apply, map_sub, map_smul]
    rw [show w (w⁻¹ x) = x from by simp]
    have hiso : ggQ2xQ_intForm D (w (Pi.single k 1)) x =
        ggQ2xQ_intForm D (Pi.single k 1) (w⁻¹ x) := by
      have h' := ggQ2xQ4_intForm_preserve D hCsym hw (Pi.single k 1) (w⁻¹ x)
      rwa [show w (w⁻¹ x) = x from by simp] at h'
    rw [hiso]
  rw [heq]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hw (ggQ2xQ_intRefl_mem_intWeyl D k))
    (Subgroup.inv_mem _ hw)

lemma ggQ2xQ4_cartan_offdiag_nonpos (D : GGQ2Lin 3) {i j : D.ι} (hij : i ≠ j) :
    D.cartan i j ≤ 0 := by
  rcases D.isCartan.2 i j hij with ⟨-, h, -⟩ | ⟨-, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩
  · rw [h]
  · rw [h]; norm_num
  · exact le_of_lt h
  · exact le_of_lt h

lemma ggQ2xQ4_pairing_le_one (D : GGQ2Lin 3) (hbas : D.Basis) (hE : ggQ2xQ_IsE D)
    {v : D.ι → ℤ} (hv : ggQ2xQ_IsRoot D v) (hpos : ∀ j, 0 ≤ v j) (i : D.ι)
    (hne : v ≠ Pi.single i 1) : ggQ2xQ_intForm D v (Pi.single i 1) ≤ 1 := by
  have hmem := (ggQ2xQ_Q3 D hbas hE).2 v (Pi.single i 1) hv (ggQ2xQ_single_isRoot D i) hne
    (by
      intro hcon
      have := hpos i
      rw [hcon] at this
      simp at this)
  rw [ggQ2xQ_intForm_apply]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  omega

lemma ggQ2xQ4_refl_pos (D : GGQ2Lin 3) (hbas : D.Basis) (hE : ggQ2xQ_IsE D)
    {v : D.ι → ℤ} (hv : ggQ2xQ_IsRoot D v) (hpos : ∀ j, 0 ≤ v j) (i : D.ι)
    (hne : v ≠ Pi.single i 1) : ∀ j, 0 ≤ ggQ2xQ_intRefl D i v j := by
  have hCsym := ggQ2xQ_cartan_symm_of_E D hE
  have hsym : ggQ2xQ_intForm D (Pi.single i 1) v = ggQ2xQ_intForm D v (Pi.single i 1) :=
    (ggQ2xQ4_intForm_isSymm D hCsym).eq _ _
  have hsum : ggQ2xQ_intForm D v (Pi.single i 1) = ∑ j, v j * D.cartan j i := by
    rw [ggQ2xQ_intForm_apply]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_eq_single i]
    · rw [Pi.single_eq_same, mul_one]
    · intro b _ hb
      rw [Pi.single_eq_of_ne hb, mul_zero]
    · intro hi; exact absurd (Finset.mem_univ i) hi
  intro j
  rw [ggQ2xQ_intRefl_apply]
  by_cases hji : j = i
  · rw [hji]
    have hcoe : (v - (ggQ2xQ_intForm D (Pi.single i 1) v) • (Pi.single i (1:ℤ) : D.ι → ℤ)) i =
        v i - ggQ2xQ_intForm D v (Pi.single i 1) := by
      rw [Pi.sub_apply, Pi.smul_apply, Pi.single_eq_same, hsym]
      simp
    rw [hcoe, hsum]
    have hvi : 0 ≤ v i := hpos i
    by_cases h0 : v i = 0
    · have hle : (∑ j, v j * D.cartan j i) ≤ 0 :=
        Finset.sum_nonpos fun j _ => by
          by_cases hji' : j = i
          · rw [hji', h0, zero_mul]
          · exact mul_nonpos_of_nonneg_of_nonpos (hpos j) (ggQ2xQ4_cartan_offdiag_nonpos D hji')
      omega
    · have h1 : 1 ≤ v i := by omega
      have hm := ggQ2xQ4_pairing_le_one D hbas hE hv hpos i hne
      omega
  · rw [Pi.sub_apply, Pi.smul_apply, Pi.single_eq_of_ne hji, smul_zero, sub_zero]
    exact hpos j

lemma ggQ2xQ4_intWeyl_smul_isRoot (D : GGQ2Lin 3)
    {w : (D.ι → ℤ) ≃ₗ[ℤ] (D.ι → ℤ)} (hw : w ∈ ggQ2xQ_intWeyl D)
    {v : D.ι → ℤ} (hv : ggQ2xQ_IsRoot D v) : ggQ2xQ_IsRoot D (w v) := by
  obtain ⟨w', hw', k, rfl⟩ := hv
  exact ⟨w * w', Subgroup.mul_mem _ hw hw', k, by rw [LinearEquiv.mul_apply]⟩

lemma ggQ2xQ4_isRoot_nonneg_or_nonpos (D : GGQ2Lin 3) (hbas : D.Basis) (hE : ggQ2xQ_IsE D)
    {v : D.ι → ℤ} (hv : ggQ2xQ_IsRoot D v) :
    (∀ j, 0 ≤ v j) ∨ (∀ j, v j ≤ 0) := by
  classical
  obtain ⟨w, hw, k, hk⟩ := hv
  subst hk
  set P : ((D.ι → ℤ) ≃ₗ[ℤ] (D.ι → ℤ)) → Prop := fun u => ∀ k : D.ι,
    (∀ j, 0 ≤ u (Pi.single k 1) j) ∨ (∀ j, u (Pi.single k 1) j ≤ 0) with hP
  have hstep : ∀ (i : D.ι) (y : (D.ι → ℤ) ≃ₗ[ℤ] (D.ι → ℤ)), y ∈ ggQ2xQ_intWeyl D → P y →
      P (ggQ2xQ_intRefl D i * y) := by
    intro i y hy hyP k
    have hroot : ggQ2xQ_IsRoot D (y (Pi.single k 1)) :=
      ggQ2xQ4_intWeyl_smul_isRoot D hy (ggQ2xQ_single_isRoot D k)
    rcases hyP k with h | h
    · by_cases hcase : y (Pi.single k 1) = Pi.single i 1
      · right
        rw [LinearEquiv.mul_apply, hcase, ggQ2xQ_intRefl_self]
        intro j
        exact neg_nonpos.mpr (ggQ2xQ4_single_nonneg D i j)
      · left
        rw [LinearEquiv.mul_apply]
        exact ggQ2xQ4_refl_pos D hbas hE hroot h i hcase
    · by_cases hcase : -(y (Pi.single k 1)) = Pi.single i 1
      · left
        have hy' : y (Pi.single k 1) = -Pi.single i 1 := by rw [← hcase, neg_neg]
        rw [LinearEquiv.mul_apply, hy', map_neg, ggQ2xQ_intRefl_self, neg_neg]
        exact ggQ2xQ4_single_nonneg D i
      · right
        rw [LinearEquiv.mul_apply]
        have hroot' : ggQ2xQ_IsRoot D (-(y (Pi.single k 1))) :=
          ggQ2xQ_IsRoot_neg D hroot
        have hpos' : ∀ j, 0 ≤ (-(y (Pi.single k 1))) j := fun j => neg_nonneg.mpr (h j)
        have hstep' := ggQ2xQ4_refl_pos D hbas hE hroot' hpos' i hcase
        have hyy : y (Pi.single k 1) = -(-(y (Pi.single k 1))) := by simp
        rw [hyy, map_neg]
        intro j
        exact neg_nonpos.mpr (hstep' j)
  have hPw : P w := by
    induction hw using Subgroup.closure_induction_left with
    | one =>
      intro k
      left
      intro j
      exact ggQ2xQ4_single_nonneg D k j
    | mul_left x hx y hy ih =>
      obtain ⟨i, rfl⟩ := hx
      exact hstep i y hy ih
    | inv_mul_cancel x hx y hy ih =>
      obtain ⟨i, rfl⟩ := hx
      have hinv : (ggQ2xQ_intRefl D i)⁻¹ = ggQ2xQ_intRefl D i := by
        refine inv_eq_of_mul_eq_one_right ?_
        refine LinearEquiv.ext fun v => ?_
        change ggQ2xQ_intRefl D i (ggQ2xQ_intRefl D i v) = v
        exact Module.involutive_reflection (ggQ2xQ_intForm_single_self D i) v
      rw [hinv]
      exact hstep i y hy ih
  exact hPw k

lemma ggQ2xQ4_cartan_posDef (D : GGQ2Lin 3) (hbas : D.Basis) (hE : ggQ2xQ_IsE D) :
    D.cartan.PosDef := by
  have hCsym := ggQ2xQ_cartan_symm_of_E D hE
  rw [← TauCeti.Matrix.posDef_map_intCast_iff]
  constructor
  · ext i j
    simp only [Matrix.conjTranspose_apply, Matrix.map_apply, star_trivial]
    exact_mod_cast (hCsym j i)
  · intro x hx
    have hx' : (fun i => x i) ≠ 0 := by
      intro h
      apply hx
      ext i
      exact congrFun h i
    have hpos := (ggQ2xQ_Q3 D hbas hE).1 (fun i => x i) hx'
    have hgoal : x.sum (fun i xi => x.sum fun j xj => star xi * (D.cartan.map Int.cast) i j * xj)
        = ∑ i, ∑ j, x i * (D.cartan i j : ℚ) * x j := by
      rw [Finsupp.sum_fintype _ _ (fun i => by simp)]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finsupp.sum_fintype _ _ (fun j => by simp)]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [Matrix.map_apply, star_trivial]
    rw [hgoal]
    exact hpos

lemma ggQ2xQ4_Phi_finite (D : GGQ2Lin 3) (hbas : D.Basis) (hE : ggQ2xQ_IsE D) :
    {v : D.ι → ℤ | ggQ2xQ_IsRoot D v}.Finite := by
  have hpd := ggQ2xQ4_cartan_posDef D hbas hE
  have hfin := Matrix.PosDef.finite_setOfPred_dotProduct_mulVec_le hpd (2 : ℤ)
  refine hfin.subset fun v hv => ?_
  simp only [Set.mem_setOf_eq] at hv ⊢
  have h2 := ggQ2xQ4_intForm_self_isRoot D (ggQ2xQ_cartan_symm_of_E D hE) hv
  have hdot : v ⬝ᵥ (D.cartan.mulVec v) = ggQ2xQ_intForm D v v := by
    rw [ggQ2xQ_intForm_apply]
    simp only [dotProduct, Matrix.mulVec_apply, Matrix.row, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hdot, h2]

lemma ggQ2xQ4_Wz_finite (D : GGQ2Lin 3) (hbas : D.Basis) (hE : ggQ2xQ_IsE D) :
    Finite (ggQ2xQ_intWeyl D) := by
  classical
  haveI : Finite {v : D.ι → ℤ // ggQ2xQ_IsRoot D v} := ggQ2xQ4_Phi_finite D hbas hE
  haveI : Finite (Equiv.Perm {v : D.ι → ℤ // ggQ2xQ_IsRoot D v}) := inferInstance
  refine Finite.of_injective
    (fun w : ggQ2xQ_intWeyl D =>
      ({ toFun := fun v => ⟨w.1 v.1, ggQ2xQ4_intWeyl_smul_isRoot D w.2 v.2⟩
         invFun := fun v => ⟨w.1.symm v.1, by
           have h := ggQ2xQ4_intWeyl_smul_isRoot D (Subgroup.inv_mem _ w.2) v.2
           simpa using h⟩
         left_inv := fun v => Subtype.ext (by simp)
         right_inv := fun v => Subtype.ext (by simp) } :
        Equiv.Perm {v : D.ι → ℤ // ggQ2xQ_IsRoot D v})) ?_
  intro a b hab
  have h : ∀ v : {v : D.ι → ℤ // ggQ2xQ_IsRoot D v}, a.1 v.1 = b.1 v.1 := by
    intro v
    have := congrArg (fun f : Equiv.Perm {v : D.ι → ℤ // ggQ2xQ_IsRoot D v} =>
      (f v : D.ι → ℤ)) hab
    simpa using this
  refine Subtype.ext (LinearEquiv.toLinearMap_injective (LinearMap.pi_ext fun k x => ?_))
  have hk := h ⟨Pi.single k (1:ℤ), ggQ2xQ_single_isRoot D k⟩
  have hsingle : (Pi.single k x : D.ι → ℤ) = x • (Pi.single k (1:ℤ) : D.ι → ℤ) := by
    ext j
    by_cases hjk : j = k
    · rw [hjk, Pi.single_eq_same, Pi.smul_apply, Pi.single_eq_same]; simp
    · rw [Pi.single_eq_of_ne hjk, Pi.smul_apply, Pi.single_eq_of_ne hjk, smul_zero]
  rw [hsingle, map_smul, map_smul]
  exact congrArg (fun z => x • z) hk

def ggQ2xQ4_adjM (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  fun i j => if CartanMatrix.E n i j = 0 then 0 else 1

def ggQ2xQ4_walk (n : ℕ) (i : Fin n) : Fin n → ℤ :=
  fun k => ∑ j, (ggQ2xQ4_adjM n ^ k.val) i j

lemma ggQ2xQ4_adjM_perm {n : ℕ} (σ : Equiv.Perm (Fin n))
    (hσ : ∀ i j, CartanMatrix.E n (σ i) (σ j) = CartanMatrix.E n i j) :
    ∀ i j, ggQ2xQ4_adjM n (σ i) (σ j) = ggQ2xQ4_adjM n i j := by
  intro i j
  simp only [ggQ2xQ4_adjM, hσ i j]

lemma ggQ2xQ4_adjM_pow_perm {n : ℕ} (σ : Equiv.Perm (Fin n))
    (hM : ∀ i j, ggQ2xQ4_adjM n (σ i) (σ j) = ggQ2xQ4_adjM n i j) :
    ∀ k i j, (ggQ2xQ4_adjM n ^ k) (σ i) (σ j) = (ggQ2xQ4_adjM n ^ k) i j := by
  intro k
  induction k with
  | zero => intro i j; simp [Matrix.one_apply, σ.injective.eq_iff]
  | succ k ih =>
    intro i j
    rw [pow_succ, Matrix.mul_apply, Matrix.mul_apply]
    rw [← Equiv.sum_comp σ (fun l =>
      (ggQ2xQ4_adjM n ^ k) (σ i) l * ggQ2xQ4_adjM n l (σ j))]
    exact Finset.sum_congr rfl fun l _ => by rw [ih i l, hM l j]

lemma ggQ2xQ4_walk_perm {n : ℕ} (σ : Equiv.Perm (Fin n))
    (hσ : ∀ i j, CartanMatrix.E n (σ i) (σ j) = CartanMatrix.E n i j) (i : Fin n) :
    ggQ2xQ4_walk n (σ i) = ggQ2xQ4_walk n i := by
  funext k
  rw [ggQ2xQ4_walk, ggQ2xQ4_walk]
  rw [← Equiv.sum_comp σ (fun j => (ggQ2xQ4_adjM n ^ k.val) (σ i) j)]
  exact Finset.sum_congr rfl fun j _ =>
    ggQ2xQ4_adjM_pow_perm σ (ggQ2xQ4_adjM_perm σ hσ) k.val i j

lemma ggQ2xQ4_walk_inj_E7 : ∀ i j : Fin 7,
    ggQ2xQ4_walk 7 i = ggQ2xQ4_walk 7 j → i = j := by decide

lemma ggQ2xQ4_walk_inj_E8 : ∀ i j : Fin 8,
    ggQ2xQ4_walk 8 i = ggQ2xQ4_walk 8 j → i = j := by decide

lemma ggQ2xQ4_walk_class_E6 : ∀ i j : Fin 6,
    ggQ2xQ4_walk 6 i = ggQ2xQ4_walk 6 j →
      i = j ∨ (i = 0 ∧ j = 5) ∨ (i = 5 ∧ j = 0) ∨ (i = 2 ∧ j = 4) ∨ (i = 4 ∧ j = 2) := by
  decide

lemma ggQ2xQ4_diagram_auto_E7 (σ : Equiv.Perm (Fin 7))
    (hσ : ∀ a b, CartanMatrix.E 7 (σ a) (σ b) = CartanMatrix.E 7 a b) : σ = 1 := by
  refine Equiv.ext fun i => ?_
  simpa using ggQ2xQ4_walk_inj_E7 (σ i) i (ggQ2xQ4_walk_perm σ hσ i)

lemma ggQ2xQ4_diagram_auto_E8 (σ : Equiv.Perm (Fin 8))
    (hσ : ∀ a b, CartanMatrix.E 8 (σ a) (σ b) = CartanMatrix.E 8 a b) : σ = 1 := by
  refine Equiv.ext fun i => ?_
  simpa using ggQ2xQ4_walk_inj_E8 (σ i) i (ggQ2xQ4_walk_perm σ hσ i)

lemma ggQ2xQ4_diagram_auto_E6 (σ : Equiv.Perm (Fin 6))
    (hσ : ∀ a b, CartanMatrix.E 6 (σ a) (σ b) = CartanMatrix.E 6 a b) :
    σ = 1 ∨ σ = Equiv.swap 0 5 * Equiv.swap 2 4 := by
  have hw := ggQ2xQ4_walk_perm σ hσ
  have h1 : σ 1 = 1 := by
    have := ggQ2xQ4_walk_class_E6 (σ 1) 1 (hw 1); tauto
  have h3 : σ 3 = 3 := by
    have := ggQ2xQ4_walk_class_E6 (σ 3) 3 (hw 3); tauto
  have h0 : σ 0 = 0 ∨ σ 0 = 5 := by
    have := ggQ2xQ4_walk_class_E6 (σ 0) 0 (hw 0); tauto
  have h2 : σ 2 = 2 ∨ σ 2 = 4 := by
    have := ggQ2xQ4_walk_class_E6 (σ 2) 2 (hw 2); tauto
  have h5 : σ 5 = 0 ∨ σ 5 = 5 := by
    have := ggQ2xQ4_walk_class_E6 (σ 5) 5 (hw 5); tauto
  have h4 : σ 4 = 2 ∨ σ 4 = 4 := by
    have := ggQ2xQ4_walk_class_E6 (σ 4) 4 (hw 4); tauto
  rcases h0 with h0 | h0
  · left
    have h2' : σ 2 = 2 := by
      rcases h2 with h | h
      · exact h
      · exfalso
        have hc := hσ 0 2
        rw [h0, h] at hc
        exact absurd hc (by decide)
    have h4' : σ 4 = 4 := by
      rcases h4 with h | h
      · exfalso
        exact (by decide : (4 : Fin 6) ≠ 2) (σ.injective (h.trans h2'.symm))
      · exact h
    have h5' : σ 5 = 5 := by
      rcases h5 with h | h
      · exfalso
        exact (by decide : (5 : Fin 6) ≠ 0) (σ.injective (h.trans h0.symm))
      · exact h
    refine Equiv.ext fun a => ?_
    fin_cases a <;> simp [h0, h1, h2', h3, h4', h5']
  · right
    have h5' : σ 5 = 0 := by
      rcases h5 with h | h
      · exact h
      · exfalso
        exact (by decide : (5 : Fin 6) ≠ 0) (σ.injective (h.trans h0.symm))
    have h2' : σ 2 = 4 := by
      rcases h2 with h | h
      · exfalso
        have hc := hσ 0 2
        rw [h0, h] at hc
        exact absurd hc (by decide)
      · exact h
    have h4' : σ 4 = 2 := by
      rcases h4 with h | h
      · exact h
      · exfalso
        exact (by decide : (4 : Fin 6) ≠ 2) (σ.injective (h.trans h2'.symm))
    refine Equiv.ext fun a => ?_
    fin_cases a <;> simp [h0, h1, h2', h3, h4', h5', Equiv.swap_apply_def]

lemma ggQ2xQ4_intForm_eq_zero (D : GGQ2Lin 3) (hbas : D.Basis) (hE : ggQ2xQ_IsE D)
    {z : D.ι → ℤ} (hz : ggQ2xQ_intForm D z z = 0) : z = 0 := by
  by_contra hz0
  have hne : (fun i => (z i : ℚ)) ≠ 0 := by
    intro h
    apply hz0
    funext i
    have hi : (z i : ℚ) = 0 := by simpa using congrFun h i
    exact_mod_cast hi
  have hpos := ggQ2xQ4_intFormQ_posDef D hbas hE hne
  rw [ggQ2xQ4_intFormQ_intCast, hz] at hpos
  norm_num at hpos

noncomputable def ggQ2xQ4_F (D : GGQ2Lin 3) (γ : D.ι → (D.ι → ℤ)) :
    (D.ι → ℤ) →ₗ[ℤ] (D.ι → ℤ) :=
  (Pi.basisFun ℤ D.ι).constr ℤ γ

lemma ggQ2xQ4_F_single (D : GGQ2Lin 3) (γ : D.ι → (D.ι → ℤ)) (k : D.ι) :
    ggQ2xQ4_F D γ (Pi.single k 1) = γ k := by
  simpa only [ggQ2xQ4_F, Pi.basisFun_apply] using
    (Module.Basis.constr_basis (b := Pi.basisFun ℤ D.ι) ℤ γ k)

lemma ggQ2xQ4_F_isometry (D : GGQ2Lin 3) (γ : D.ι → (D.ι → ℤ))
    (hframe : ∀ i j, ggQ2xQ_intForm D (γ i) (γ j) = D.cartan i j) (x y : D.ι → ℤ) :
    ggQ2xQ_intForm D (ggQ2xQ4_F D γ x) (ggQ2xQ4_F D γ y) = ggQ2xQ_intForm D x y := by
  have hcomp : (ggQ2xQ_intForm D).comp (ggQ2xQ4_F D γ) (ggQ2xQ4_F D γ) =
      ggQ2xQ_intForm D := by
    refine LinearMap.BilinForm.ext_basis (Pi.basisFun ℤ D.ι) fun i j => ?_
    rw [LinearMap.BilinForm.comp_apply, Pi.basisFun_apply, Pi.basisFun_apply,
      ggQ2xQ4_F_single, ggQ2xQ4_F_single, ggQ2xQ4_intForm_single]
    exact hframe i j
  have := LinearMap.BilinForm.congr_fun hcomp x y
  rwa [LinearMap.BilinForm.comp_apply] at this

lemma ggQ2xQ4_F_injective (D : GGQ2Lin 3) (hbas : D.Basis) (hE : ggQ2xQ_IsE D)
    (γ : D.ι → (D.ι → ℤ)) (hframe : ∀ i j, ggQ2xQ_intForm D (γ i) (γ j) = D.cartan i j) :
    Function.Injective (ggQ2xQ4_F D γ) := by
  intro x y hxy
  have h0 : ggQ2xQ_intForm D (x - y) (x - y) = 0 := by
    have hiso := ggQ2xQ4_F_isometry D γ hframe (x - y) (x - y)
    rw [map_sub, hxy, sub_self] at hiso
    simpa using hiso.symm
  exact sub_eq_zero.mp (ggQ2xQ4_intForm_eq_zero D hbas hE h0)

lemma ggQ2xQ4_intRefl_involutive (D : GGQ2Lin 3) (k : D.ι) (z : D.ι → ℤ) :
    ggQ2xQ_intRefl D k (ggQ2xQ_intRefl D k z) = z :=
  Module.involutive_reflection (ggQ2xQ_intForm_single_self D k) z

lemma ggQ2xQ4_F_refl (D : GGQ2Lin 3) (γ : D.ι → (D.ι → ℤ))
    (hframe : ∀ i j, ggQ2xQ_intForm D (γ i) (γ j) = D.cartan i j) (k : D.ι)
    (x : D.ι → ℤ) :
    ggQ2xQ4_F D γ (ggQ2xQ_intRefl D k x) =
      ggQ2xQ4_reflOf D (γ k) (by rw [hframe k k, D.isCartan.1]) (ggQ2xQ4_F D γ x) := by
  rw [ggQ2xQ_intRefl_apply, ggQ2xQ4_reflOf_apply, map_sub, map_smul, ggQ2xQ4_F_single]
  have h : ggQ2xQ_intForm D (γ k) (ggQ2xQ4_F D γ x) = ggQ2xQ_intForm D (Pi.single k 1) x := by
    rw [← ggQ2xQ4_F_single D γ k]
    exact ggQ2xQ4_F_isometry D γ hframe (Pi.single k 1) x
  rw [h]

lemma ggQ2xQ4_F_mem_roots (D : GGQ2Lin 3) (hCsym : ∀ i j, D.cartan i j = D.cartan j i)
    (γ : D.ι → (D.ι → ℤ)) (hframe : ∀ i j, ggQ2xQ_intForm D (γ i) (γ j) = D.cartan i j)
    (hroot : ∀ k, ggQ2xQ_IsRoot D (γ k)) {v : D.ι → ℤ} (hv : ggQ2xQ_IsRoot D v) :
    ggQ2xQ_IsRoot D (ggQ2xQ4_F D γ v) := by
  obtain ⟨w, hw, k, rfl⟩ := hv
  have hconj : ∀ u ∈ ggQ2xQ_intWeyl D, ∃ u' ∈ ggQ2xQ_intWeyl D,
      ∀ x, ggQ2xQ4_F D γ (u x) = u' (ggQ2xQ4_F D γ x) := by
    intro u hu
    refine Subgroup.closure_induction (k := Set.range (ggQ2xQ_intRefl D))
      (p := fun u _ => ∃ u' ∈ ggQ2xQ_intWeyl D,
        ∀ x, ggQ2xQ4_F D γ (u x) = u' (ggQ2xQ4_F D γ x)) ?_ ?_ ?_ ?_ hu
    · rintro u ⟨i, rfl⟩
      exact ⟨ggQ2xQ4_reflOf D (γ i) (by rw [hframe i i, D.isCartan.1]),
        ggQ2xQ4_reflOf_mem_intWeyl D hCsym (hroot i) _, fun x => ggQ2xQ4_F_refl D γ hframe i x⟩
    · exact ⟨1, (ggQ2xQ_intWeyl D).one_mem, fun x => by simp⟩
    · rintro a b _ _ ⟨a', ha', hFa⟩ ⟨b', hb', hFb⟩
      exact ⟨a' * b', Subgroup.mul_mem _ ha' hb', fun x => by
        rw [LinearEquiv.mul_apply, hFa, LinearEquiv.mul_apply, hFb]⟩
    · rintro a _ ⟨a', ha', hFa⟩
      refine ⟨a'⁻¹, Subgroup.inv_mem _ ha', fun x => ?_⟩
      have h := hFa (a⁻¹ x)
      rw [show a (a⁻¹ x) = x from by simp] at h
      rw [h]
      simp
  obtain ⟨w', hw', hFw⟩ := hconj w hw
  rw [hFw, ggQ2xQ4_F_single]
  exact ggQ2xQ4_intWeyl_smul_isRoot D hw' (hroot k)

lemma ggQ2xQ4_intForm_single_left (D : GGQ2Lin 3) (x : D.ι → ℤ) (k : D.ι) :
    ggQ2xQ_intForm D (Pi.single k 1) x = ∑ j, D.cartan k j * x j := by
  rw [ggQ2xQ_intForm_apply, Finset.sum_eq_single k]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [Pi.single_eq_same, one_mul]
  · intro i _ hi
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [Pi.single_eq_of_ne hi, zero_mul, zero_mul]
  · intro h; exact absurd (Finset.mem_univ k) h

lemma ggQ2xQ4_dominant_E6 (D : GGQ2Lin 3) (e : Fin 6 ≃ D.ι)
    (hc : ∀ a b, D.cartan (e a) (e b) = CartanMatrix.E 6 a b) :
    ∃ x₀ : D.ι → ℤ, ∀ k, ggQ2xQ_intForm D (Pi.single k 1) x₀ = 3 := by
  refine ⟨fun i => ![24, 33, 45, 63, 45, 24] (e.symm i), fun k => ?_⟩
  obtain ⟨a, rfl⟩ := e.surjective k
  rw [ggQ2xQ4_intForm_single_left]
  rw [← Equiv.sum_comp e (fun j => D.cartan (e a) j *
    (fun i => ![24, 33, 45, 63, 45, 24] (e.symm i)) j)]
  simp only [Equiv.symm_apply_apply, hc]
  fin_cases a <;> decide

lemma ggQ2xQ4_dominant_E7 (D : GGQ2Lin 3) (e : Fin 7 ≃ D.ι)
    (hc : ∀ a b, D.cartan (e a) (e b) = CartanMatrix.E 7 a b) :
    ∃ x₀ : D.ι → ℤ, ∀ k, ggQ2xQ_intForm D (Pi.single k 1) x₀ = 2 := by
  refine ⟨fun i => ![34, 49, 66, 96, 75, 52, 27] (e.symm i), fun k => ?_⟩
  obtain ⟨a, rfl⟩ := e.surjective k
  rw [ggQ2xQ4_intForm_single_left]
  rw [← Equiv.sum_comp e (fun j => D.cartan (e a) j *
    (fun i => ![34, 49, 66, 96, 75, 52, 27] (e.symm i)) j)]
  simp only [Equiv.symm_apply_apply, hc]
  fin_cases a <;> decide

lemma ggQ2xQ4_dominant_E8 (D : GGQ2Lin 3) (e : Fin 8 ≃ D.ι)
    (hc : ∀ a b, D.cartan (e a) (e b) = CartanMatrix.E 8 a b) :
    ∃ x₀ : D.ι → ℤ, ∀ k, ggQ2xQ_intForm D (Pi.single k 1) x₀ = 1 := by
  refine ⟨fun i => ![46, 68, 91, 135, 110, 84, 57, 29] (e.symm i), fun k => ?_⟩
  obtain ⟨a, rfl⟩ := e.surjective k
  rw [ggQ2xQ4_intForm_single_left]
  rw [← Equiv.sum_comp e (fun j => D.cartan (e a) j *
    (fun i => ![46, 68, 91, 135, 110, 84, 57, 29] (e.symm i)) j)]
  simp only [Equiv.symm_apply_apply, hc]
  fin_cases a <;> decide

private def ggQ2xQ4_tau6p : Equiv.Perm (Fin 6) :=
  Equiv.swap (0 : Fin 6) 5 * Equiv.swap (2 : Fin 6) 4

private lemma ggQ2xQ4_decomp (D : GGQ2Lin 3) (x : D.ι → ℤ) :
    x = ∑ j, x j • (Pi.single j (1:ℤ) : D.ι → ℤ) := by
  ext i
  rw [Finset.sum_apply, Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    rw [Pi.smul_apply, Pi.single_eq_of_ne (Ne.symm hj), smul_zero]
  · intro h; exact absurd (Finset.mem_univ i) h

private noncomputable def ggQ2xQ4_tau6 (D : GGQ2Lin 3) (e : Fin 6 ≃ D.ι) : D.ι ≃ D.ι :=
  e.symm.trans (ggQ2xQ4_tau6p.trans e)

private lemma ggQ2xQ4_tau6_apply (D : GGQ2Lin 3) (e : Fin 6 ≃ D.ι) (a : Fin 6) :
    ggQ2xQ4_tau6 D e (e a) = e (ggQ2xQ4_tau6p a) := by
  simp [ggQ2xQ4_tau6]

private lemma ggQ2xQ4_tau6_ne_one (D : GGQ2Lin 3) (e : Fin 6 ≃ D.ι) :
    ggQ2xQ4_tau6 D e ≠ 1 := by
  intro h
  have := ggQ2xQ4_tau6_apply D e 0
  rw [h] at this
  simp only [Equiv.Perm.coe_one, id_eq] at this
  have h5 : ggQ2xQ4_tau6p (0 : Fin 6) = 5 := by decide
  rw [h5] at this
  exact (by decide : (0 : Fin 6) ≠ 5) (e.injective this)

private lemma ggQ2xQ4_diagram_auto_D_E6 (D : GGQ2Lin 3) (e : Fin 6 ≃ D.ι)
    (hc : ∀ a b, D.cartan (e a) (e b) = CartanMatrix.E 6 a b)
    (σ : D.ι ≃ D.ι) (hσ : ∀ i j, D.cartan (σ i) (σ j) = D.cartan i j) :
    σ = 1 ∨ σ = ggQ2xQ4_tau6 D e := by
  set σ' : Equiv.Perm (Fin 6) := e.trans (σ.trans e.symm) with hσ'def
  have hσ' : ∀ a b, CartanMatrix.E 6 (σ' a) (σ' b) = CartanMatrix.E 6 a b := by
    intro a b
    have h1 := hc (σ' a) (σ' b)
    have h2 := hc a b
    have h3 := hσ (e a) (e b)
    have hea : e (σ' a) = σ (e a) := by simp [hσ'def]
    have heb : e (σ' b) = σ (e b) := by simp [hσ'def]
    rw [← h1, hea, heb, h3, h2]
  rcases ggQ2xQ4_diagram_auto_E6 σ' hσ' with h | h
  · left
    refine Equiv.ext fun i => ?_
    obtain ⟨a, rfl⟩ := e.surjective i
    have hh : σ' a = a := by
      have := DFunLike.congr_fun h a
      simpa using this
    simp only [hσ'def, Equiv.trans_apply] at hh
    have := congrArg e hh
    simpa using this
  · right
    refine Equiv.ext fun i => ?_
    obtain ⟨a, rfl⟩ := e.surjective i
    have hh : σ' a = ggQ2xQ4_tau6p a := by
      have := DFunLike.congr_fun h a
      simpa [ggQ2xQ4_tau6p] using this
    simp only [hσ'def, Equiv.trans_apply] at hh
    have h2 : σ (e a) = e (ggQ2xQ4_tau6p a) := by
      have := congrArg e hh
      simpa using this
    rw [ggQ2xQ4_tau6_apply]
    exact h2

private lemma ggQ2xQ4_frame_perm (D : GGQ2Lin 3) (hbas : D.Basis) (hE : ggQ2xQ_IsE D)
    (γ : D.ι → (D.ι → ℤ)) (hroot : ∀ k, ggQ2xQ_IsRoot D (γ k))
    (hframe : ∀ i j, ggQ2xQ_intForm D (γ i) (γ j) = D.cartan i j) :
    ∃ (u : ggQ2xQ_intWeyl D) (σ : D.ι ≃ D.ι), (∀ i j, D.cartan (σ i) (σ j) = D.cartan i j) ∧
      ∀ k, γ k = (u : (D.ι → ℤ) ≃ₗ[ℤ] (D.ι → ℤ)) (Pi.single (σ k) 1) := by
  classical
  have hCsym := ggQ2xQ_cartan_symm_of_E D hE
  have hFmem : ∀ v, ggQ2xQ_IsRoot D v → ggQ2xQ_IsRoot D (ggQ2xQ4_F D γ v) :=
    fun v hv => ggQ2xQ4_F_mem_roots D hCsym γ hframe hroot hv
  have hFinj := ggQ2xQ4_F_injective D hbas hE γ hframe
  obtain ⟨x₀, d, hd, hx₀⟩ : ∃ x₀ : D.ι → ℤ, ∃ d : ℤ, 0 < d ∧
      ∀ k, ggQ2xQ_intForm D (Pi.single k 1) x₀ = d := by
    rcases hE with ⟨e, he⟩ | ⟨e, he⟩ | ⟨e, he⟩
    · obtain ⟨x₀, hx₀⟩ := ggQ2xQ4_dominant_E6 D e (ggQ2xQ_cartan_E6 D e he)
      exact ⟨x₀, 3, by norm_num, hx₀⟩
    · obtain ⟨x₀, hx₀⟩ := ggQ2xQ4_dominant_E7 D e (ggQ2xQ_cartan_E7 D e he)
      exact ⟨x₀, 2, by norm_num, hx₀⟩
    · obtain ⟨x₀, hx₀⟩ := ggQ2xQ4_dominant_E8 D e (ggQ2xQ_cartan_E8 D e he)
      exact ⟨x₀, 1, by norm_num, hx₀⟩
  haveI : Finite (ggQ2xQ_intWeyl D) := ggQ2xQ4_Wz_finite D hbas hE
  letI := Fintype.ofFinite (ggQ2xQ_intWeyl D)
  obtain ⟨v, -, hv⟩ := Finset.exists_max_image Finset.univ
    (fun v : ggQ2xQ_intWeyl D => ggQ2xQ_intForm D x₀ (v.1 (ggQ2xQ4_F D γ x₀)))
    Finset.univ_nonempty
  set z : D.ι → ℤ := v.1 (ggQ2xQ4_F D γ x₀) with hz
  have hzdom : ∀ k, 0 ≤ ggQ2xQ_intForm D (Pi.single k 1) z := by
    intro k
    by_contra hneg
    rw [not_le] at hneg
    let vk : ggQ2xQ_intWeyl D :=
      ⟨(ggQ2xQ_intRefl D k) * v.1,
        Subgroup.mul_mem _ (ggQ2xQ_intRefl_mem_intWeyl D k) v.2⟩
    have hvk : vk.1 = ggQ2xQ_intRefl D k * v.1 := rfl
    have hsym : ggQ2xQ_intForm D x₀ (ggQ2xQ_intRefl D k z) =
        ggQ2xQ_intForm D (ggQ2xQ_intRefl D k x₀) z := by
      have h := ggQ2xQ4_intForm_preserve D hCsym (ggQ2xQ_intRefl_mem_intWeyl D k) x₀
        (ggQ2xQ_intRefl D k z)
      rw [ggQ2xQ4_intRefl_involutive] at h
      exact h.symm
    have hval : ggQ2xQ_intForm D x₀ (vk.1 (ggQ2xQ4_F D γ x₀)) =
        ggQ2xQ_intForm D x₀ z - d * ggQ2xQ_intForm D (Pi.single k 1) z := by
      rw [hvk, LinearEquiv.mul_apply, ← hz, hsym, ggQ2xQ_intRefl_apply, hx₀ k]
      rw [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, zsmul_eq_mul,
        Int.cast_id]
    have hlt : ggQ2xQ_intForm D x₀ z < ggQ2xQ_intForm D x₀ (vk.1 (ggQ2xQ4_F D γ x₀)) := by
      rw [hval]; nlinarith
    exact not_le_of_gt hlt (hv vk (Finset.mem_univ _))
  set H : (D.ι → ℤ) →ₗ[ℤ] (D.ι → ℤ) := v.1.toLinearMap.comp (ggQ2xQ4_F D γ) with hHdef
  have hHapply : ∀ x, H x = v.1 (ggQ2xQ4_F D γ x) := fun x => rfl
  have hHiso : ∀ a b, ggQ2xQ_intForm D (H a) (H b) = ggQ2xQ_intForm D a b := by
    intro a b
    rw [hHapply, hHapply, ggQ2xQ4_intForm_preserve D hCsym v.2, ggQ2xQ4_F_isometry D γ hframe]
  have hHmem : ∀ x, ggQ2xQ_IsRoot D x → ggQ2xQ_IsRoot D (H x) := fun x hx =>
    ggQ2xQ4_intWeyl_smul_isRoot D v.2 (hFmem x hx)
  have hHnn : ∀ k, ∀ j, 0 ≤ H (Pi.single k 1) j := by
    intro k
    rcases ggQ2xQ4_isRoot_nonneg_or_nonpos D hbas hE (hHmem _ (ggQ2xQ_single_isRoot D k)) with
      h | h
    · exact h
    · exfalso
      have hBpos : ggQ2xQ_intForm D (H (Pi.single k 1)) z = d := by
        rw [show z = H x₀ from rfl, hHiso (Pi.single k 1) x₀, hx₀ k]
      have hBnonpos : ggQ2xQ_intForm D (H (Pi.single k 1)) z ≤ 0 := by
        rw [ggQ2xQ4_decomp D (H (Pi.single k 1)), map_sum, LinearMap.sum_apply]
        refine Finset.sum_nonpos fun j _ => ?_
        rw [map_smul, LinearMap.smul_apply, zsmul_eq_mul]
        exact mul_nonpos_of_nonpos_of_nonneg (h j) (hzdom j)
      rw [hBpos] at hBnonpos
      omega
  have hHcone : ∀ x, ggQ2xQ_IsRoot D x → (∀ i, x i ≤ 0) → ∀ j, H x j ≤ 0 := by
    intro x _ hxneg j
    have hHx : H x = ∑ i, x i • H (Pi.single i 1) := by
      conv_lhs => rw [ggQ2xQ4_decomp D x]
      rw [map_sum]
      simp only [map_smul]
    rw [hHx, Finset.sum_apply]
    refine Finset.sum_nonpos fun i _ => ?_
    rw [Pi.smul_apply, zsmul_eq_mul]
    exact mul_nonpos_of_nonpos_of_nonneg (hxneg i) (hHnn i j)
  have hHconePos : ∀ x, ggQ2xQ_IsRoot D x → (∀ i, 0 ≤ x i) → ∀ j, 0 ≤ H x j := by
    intro x _ hxpos j
    have hHx : H x = ∑ i, x i • H (Pi.single i 1) := by
      conv_lhs => rw [ggQ2xQ4_decomp D x]
      rw [map_sum]
      simp only [map_smul]
    rw [hHx, Finset.sum_apply]
    refine Finset.sum_nonneg fun i _ => ?_
    rw [Pi.smul_apply, zsmul_eq_mul]
    exact mul_nonneg (hxpos i) (hHnn i j)
  have hHinj : Function.Injective H := by
    intro a b hab
    rw [hHapply, hHapply] at hab
    exact hFinj (v.1.injective hab)
  haveI : Finite {v : D.ι → ℤ // ggQ2xQ_IsRoot D v} := ggQ2xQ4_Phi_finite D hbas hE
  have hHΦinj : Function.Injective
      (fun x : {v : D.ι → ℤ // ggQ2xQ_IsRoot D v} =>
        (⟨H x.1, hHmem x.1 x.2⟩ : {v : D.ι → ℤ // ggQ2xQ_IsRoot D v})) := by
    intro a b hab
    exact Subtype.ext (hHinj (Subtype.ext_iff.mp hab))
  have hHΦsurj := Finite.injective_iff_surjective.mp hHΦinj
  have hHsurj : ∀ j, ∃ δ : D.ι → ℤ, ggQ2xQ_IsRoot D δ ∧ (∀ i, 0 ≤ δ i) ∧
      H δ = Pi.single j 1 := by
    intro j
    obtain ⟨δ, hδ⟩ := hHΦsurj ⟨Pi.single j 1, ggQ2xQ_single_isRoot D j⟩
    have hδH : H δ.1 = Pi.single j 1 := Subtype.ext_iff.mp hδ
    rcases ggQ2xQ4_isRoot_nonneg_or_nonpos D hbas hE δ.2 with hpos | hneg
    · exact ⟨δ.1, δ.2, hpos, hδH⟩
    · exfalso
      have := hHcone δ.1 δ.2 hneg j
      rw [hδH] at this
      simp at this
  have ht_pos : ∀ δ : D.ι → ℤ, ggQ2xQ_IsRoot D δ → (∀ i, 0 ≤ δ i) → 1 ≤ ∑ i, δ i := by
    intro δ hδ hδpos
    have hδne : δ ≠ 0 := by
      intro h0
      have hself := ggQ2xQ4_intForm_self_isRoot D hCsym hδ
      rw [h0] at hself
      simp at hself
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hδne
    have hjpos : 0 < δ j := lt_of_le_of_ne (hδpos j) (Ne.symm hj)
    have : 0 < ∑ i, δ i := Finset.sum_pos' (fun i _ => hδpos i) ⟨j, Finset.mem_univ j, hjpos⟩
    omega
  have hHsingle : ∀ k, ∃ j, H (Pi.single k 1) = Pi.single j 1 := by
    intro k
    choose δ hδ using hHsurj
    have hδroot : ∀ j, ggQ2xQ_IsRoot D (δ j) := fun j => (hδ j).1
    have hδpos : ∀ j, ∀ i, 0 ≤ δ j i := fun j => (hδ j).2.1
    have hδH : ∀ j, H (δ j) = Pi.single j 1 := fun j => (hδ j).2.2
    have hdec := ggQ2xQ4_decomp D (H (Pi.single k 1))
    have hlin : H (∑ j, (H (Pi.single k 1)) j • δ j) = H (Pi.single k 1) := by
      rw [map_sum]
      simp only [map_smul]
      rw [Finset.sum_congr rfl (fun j _ => by rw [hδH j])]
      exact hdec.symm
    have heq : Pi.single k 1 = ∑ j, (H (Pi.single k 1)) j • δ j := (hHinj hlin).symm
    have hht : ∑ i, (∑ j, (H (Pi.single k 1)) j • δ j) i =
        ∑ j, (H (Pi.single k 1)) j * ∑ i, δ j i := by
      have h1 : ∀ i, (∑ j, (H (Pi.single k 1)) j • δ j) i =
          ∑ j, (H (Pi.single k 1)) j * δ j i := by
        intro i
        rw [Finset.sum_apply]
        exact Finset.sum_congr rfl fun j _ => by
          rw [Pi.smul_apply, zsmul_eq_mul, Int.cast_id]
      simp only [h1]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ => by rw [Finset.mul_sum]
    have hex : ∃ j, 0 < (H (Pi.single k 1)) j := by
      by_contra hcon
      simp only [not_exists, not_lt] at hcon
      have hzero : H (Pi.single k 1) = 0 := by
        rw [hdec]
        refine Finset.sum_eq_zero fun j _ => ?_
        rw [le_antisymm (hcon j) (hHnn k j), zero_smul]
      have hself := ggQ2xQ4_intForm_self_isRoot D hCsym (hHmem _ (ggQ2xQ_single_isRoot D k))
      rw [hzero] at hself
      simp at hself
    obtain ⟨j, hjpos⟩ := hex
    have h3 : 1 ≤ ∑ j, (H (Pi.single k 1)) j := by
      have := Finset.single_le_sum (fun i _ => hHnn k i) (Finset.mem_univ j)
      omega
    have hsum_one : ∑ j, (H (Pi.single k 1)) j = 1 := by
      have h1 : ∑ j, (H (Pi.single k 1)) j * ∑ i, δ j i = 1 := by
        rw [← hht, ← heq]; simp
      have h2 : ∑ j, (H (Pi.single k 1)) j ≤
          ∑ j, (H (Pi.single k 1)) j * ∑ i, δ j i :=
        Finset.sum_le_sum fun j _ => by
          have := ht_pos (δ j) (hδroot j) (hδpos j)
          nlinarith [hHnn k j]
      omega
    have hjone : (H (Pi.single k 1)) j = 1 := by
      have : (H (Pi.single k 1)) j ≤ ∑ i, (H (Pi.single k 1)) i :=
        Finset.single_le_sum (fun i _ => hHnn k i) (Finset.mem_univ j)
      omega
    refine ⟨j, ?_⟩
    rw [hdec, Finset.sum_eq_single j]
    · rw [hjone, one_smul]
    · intro i _ hi
      have hiz : (H (Pi.single k 1)) i = 0 := by
        have hmem : j ∈ Finset.univ.erase i :=
          Finset.mem_erase.mpr ⟨Ne.symm hi, Finset.mem_univ j⟩
        have h1 : (H (Pi.single k 1)) j ≤
            ∑ l ∈ Finset.univ.erase i, (H (Pi.single k 1)) l :=
          Finset.single_le_sum (fun l _ => hHnn k l) hmem
        have h2 : (H (Pi.single k 1)) i +
            ∑ l ∈ Finset.univ.erase i, (H (Pi.single k 1)) l =
            ∑ l, (H (Pi.single k 1)) l :=
          Finset.add_sum_erase Finset.univ (fun l => (H (Pi.single k 1)) l) (Finset.mem_univ i)
        have h3 : 0 ≤ (H (Pi.single k 1)) i := hHnn k i
        omega
      rw [hiz, zero_smul]
    · intro h; exact absurd (Finset.mem_univ j) h
  choose σ hσ using hHsingle
  have hσinj : Function.Injective σ := by
    intro i j hij
    have hH : H (Pi.single i 1) = H (Pi.single j 1) := by rw [hσ i, hσ j, hij]
    have hsingle : (Pi.single i (1:ℤ) : D.ι → ℤ) = (Pi.single j (1:ℤ) : D.ι → ℤ) := by
      have h1 : ggQ2xQ4_F D γ (Pi.single i 1) = ggQ2xQ4_F D γ (Pi.single j 1) := by
        apply v.1.injective
        rw [← hHapply, ← hHapply]
        exact hH
      exact hFinj h1
    by_contra hne
    have := congrFun hsingle i
    rw [Pi.single_eq_same, Pi.single_eq_of_ne hne] at this
    exact one_ne_zero this
  have hσsurj := Finite.injective_iff_surjective.mp hσinj
  let σe : D.ι ≃ D.ι := Equiv.ofBijective σ ⟨hσinj, hσsurj⟩
  have hσe : ∀ k, H (Pi.single k 1) = Pi.single (σe k) 1 := fun k => hσ k
  have hσdiag : ∀ i j, D.cartan (σe i) (σe j) = D.cartan i j := by
    intro i j
    have h1 := ggQ2xQ4_intForm_single D (σe i) (σe j)
    have h2 := ggQ2xQ4_intForm_single D i j
    have h3 : ggQ2xQ_intForm D (Pi.single (σe i) 1) (Pi.single (σe j) 1) =
        ggQ2xQ_intForm D (Pi.single i 1) (Pi.single j 1) := by
      rw [← hσe i, ← hσe j, hHiso]
    rw [← h1, h3, h2]
  refine ⟨v⁻¹, σe, hσdiag, fun k => ?_⟩
  have h := hσe k
  rw [hHapply, ggQ2xQ4_F_single] at h
  have := congrArg (fun w => (v⁻¹ : (D.ι → ℤ) ≃ₗ[ℤ] (D.ι → ℤ)) w) h
  simpa using this

private noncomputable def ggQ2xQ4_negLE (D : GGQ2Lin 3) :
    (D.ι → ℤ) ≃ₗ[ℤ] (D.ι → ℤ) where
  toFun x := -x
  invFun x := -x
  left_inv x := by simp
  right_inv x := by simp
  map_add' x y := by rw [neg_add]
  map_smul' a x := by simp

private lemma ggQ2xQ4_neg_one_notMem_E6 (D : GGQ2Lin 3) (hbas : D.Basis) (hE : ggQ2xQ_IsE D)
    (e : Fin 6 ≃ D.ι) (he : D.coxeter = CoxeterMatrix.E₆.reindex e) :
    ggQ2xQ4_negLE D ∉ ggQ2xQ_intWeyl D := by
  intro hmem
  let ρ : D.V := D.coroot (e 0) - D.coroot (e 2) + D.coroot (e 4) - D.coroot (e 5)
  have hρne : ρ ≠ 0 := by
    intro hρ
    have h1 : (ggQ2xQ_basis D hbas).repr ρ = 0 := by rw [hρ]; simp
    have h2 : (ggQ2xQ_basis D hbas).repr ρ (e 0) = 1 := by
      have hlin : (ggQ2xQ_basis D hbas).repr ρ =
          (ggQ2xQ_basis D hbas).repr (D.coroot (e 0)) -
          (ggQ2xQ_basis D hbas).repr (D.coroot (e 2)) +
          (ggQ2xQ_basis D hbas).repr (D.coroot (e 4)) -
          (ggQ2xQ_basis D hbas).repr (D.coroot (e 5)) := by
        rw [show ρ = D.coroot (e 0) - D.coroot (e 2) + D.coroot (e 4) - D.coroot (e 5)
          from rfl, map_sub, map_add, map_sub]
      rw [hlin, ← ggQ2xQ_basis_apply D hbas (e 0), ← ggQ2xQ_basis_apply D hbas (e 2),
        ← ggQ2xQ_basis_apply D hbas (e 4), ← ggQ2xQ_basis_apply D hbas (e 5),
        Module.Basis.repr_self, Module.Basis.repr_self, Module.Basis.repr_self,
        Module.Basis.repr_self]
      simp
    rw [h1] at h2
    exact one_ne_zero h2.symm
  have hfix : ∀ g ∈ D.weyl, g ρ = ρ := by
    rw [GGQ2Lin.weyl, GGQ2Lin.parab]
    intro g hg
    refine Subgroup.closure_induction (k := D.simpleRefl '' Set.univ) (p := fun g _ => g ρ = ρ)
      ?_ ?_ ?_ ?_ hg
    · rintro g ⟨k, -, rfl⟩
      rw [GGQ2Lin.simpleRefl, Module.reflection_apply]
      have hzero : D.root k ρ = 0 := by
        obtain ⟨a, rfl⟩ := e.surjective k
        have hlin : D.root (e a) ρ = D.root (e a) (D.coroot (e 0)) -
            D.root (e a) (D.coroot (e 2)) + D.root (e a) (D.coroot (e 4)) -
            D.root (e a) (D.coroot (e 5)) := by
          rw [show ρ = D.coroot (e 0) - D.coroot (e 2) + D.coroot (e 4) - D.coroot (e 5)
            from rfl, map_sub, map_add, map_sub]
        rw [hlin, D.pairing, D.pairing, D.pairing, D.pairing,
          ggQ2xQ_cartan_E6 D e he, ggQ2xQ_cartan_E6 D e he, ggQ2xQ_cartan_E6 D e he,
          ggQ2xQ_cartan_E6 D e he]
        fin_cases a <;> decide
      rw [hzero, zero_smul, sub_zero]
    · rfl
    · intro a b _ _ iha ihb
      rw [LinearEquiv.mul_apply, ihb, iha]
    · intro a _ iha
      calc a⁻¹ ρ = a⁻¹ (a ρ) := by rw [iha]
        _ = ρ := by simp
  obtain ⟨g, hg, hgρ⟩ := ggQ2xQ_Q2_red D hbas hE ⟨ggQ2xQ4_negLE D, hmem⟩
  have hgneg : g ρ = -ρ := by
    let x : D.ι → ℤ := Pi.single (e 0) 1 - Pi.single (e 2) 1 + Pi.single (e 4) 1 -
      Pi.single (e 5) 1
    have hx : ggQ2xQ_rhoBar D x = ρ := by
      rw [show ρ = D.coroot (e 0) - D.coroot (e 2) + D.coroot (e 4) - D.coroot (e 5)
        from rfl]
      rw [show x = Pi.single (e 0) 1 - Pi.single (e 2) 1 + Pi.single (e 4) 1 -
          Pi.single (e 5) 1 from rfl, map_sub, map_add, map_sub, ggQ2xQ_rhoBar_single,
        ggQ2xQ_rhoBar_single, ggQ2xQ_rhoBar_single, ggQ2xQ_rhoBar_single]
    have h := hgρ x
    have hux : ((⟨ggQ2xQ4_negLE D, hmem⟩ : ggQ2xQ_intWeyl D) :
        (D.ι → ℤ) ≃ₗ[ℤ] (D.ι → ℤ)) x = -x := by simp [ggQ2xQ4_negLE]
    rw [hux, map_neg, hx] at h
    exact h.symm
  have hfixg := hfix g hg
  rw [hfixg] at hgneg
  have hzero : ρ = 0 := by
    have h2 : (2 : ZMod 3) • ρ = 0 := by
      rw [two_smul]
      exact add_eq_zero_iff_eq_neg.mpr hgneg
    exact (smul_eq_zero.mp h2).resolve_left (by decide)
  exact hρne hzero

private lemma ggQ2xQ4_E6_negperm (D : GGQ2Lin 3) (hbas : D.Basis) (hE : ggQ2xQ_IsE D)
    (e : Fin 6 ≃ D.ι) (he : D.coxeter = CoxeterMatrix.E₆.reindex e)
    (σ : D.ι ≃ D.ι) (hσ : ∀ i j, D.cartan (σ i) (σ j) = D.cartan i j) (hσne : σ ≠ 1) :
    ∃ w : ggQ2xQ_intWeyl D,
      ∀ k, (w : (D.ι → ℤ) ≃ₗ[ℤ] (D.ι → ℤ)) (Pi.single k 1) = - (Pi.single (σ k) 1) := by
  classical
  have hc := ggQ2xQ_cartan_E6 D e he
  rcases ggQ2xQ4_diagram_auto_D_E6 D e hc σ hσ with h1 | hτ
  · exact absurd h1 hσne
  let γ' : D.ι → (D.ι → ℤ) := fun k => - (Pi.single (σ k) (1:ℤ))
  have hroot' : ∀ k, ggQ2xQ_IsRoot D (γ' k) := fun k =>
    ggQ2xQ_IsRoot_neg D (ggQ2xQ_single_isRoot D (σ k))
  have hframe' : ∀ i j, ggQ2xQ_intForm D (γ' i) (γ' j) = D.cartan i j := by
    intro i j
    have h1 : ggQ2xQ_intForm D (-(Pi.single (σ i) (1:ℤ))) (-(Pi.single (σ j) (1:ℤ))) =
        ggQ2xQ_intForm D (Pi.single (σ i) (1:ℤ)) (Pi.single (σ j) (1:ℤ)) := by
      simp only [map_neg, LinearMap.neg_apply, neg_neg]
    rw [show γ' i = -(Pi.single (σ i) (1:ℤ)) from rfl,
      show γ' j = -(Pi.single (σ j) (1:ℤ)) from rfl, h1, ggQ2xQ4_intForm_single]
    exact hσ i j
  obtain ⟨w, σ'', hσ'', hγ'⟩ := ggQ2xQ4_frame_perm D hbas hE γ' hroot' hframe'
  rcases ggQ2xQ4_diagram_auto_D_E6 D e hc σ'' hσ'' with hσ''1 | hσ''τ
  · refine ⟨w, fun k => ?_⟩
    have h := hγ' k
    rw [hσ''1] at h
    simpa [γ'] using h.symm
  · exfalso
    have hwe : ∀ j, w.1 (Pi.single j (1:ℤ)) = - (Pi.single j (1:ℤ)) := by
      intro j
      obtain ⟨k, rfl⟩ := σ.surjective j
      have h1 := hγ' k
      rw [hσ''τ, show γ' k = -(Pi.single (σ k) (1:ℤ)) from rfl] at h1
      have hτk : ggQ2xQ4_tau6 D e k = σ k := by rw [← hτ]
      rw [hτk] at h1
      exact h1.symm
    have hwneg : w.1 = ggQ2xQ4_negLE D := by
      refine LinearEquiv.ext fun x => ?_
      have hx := ggQ2xQ4_decomp D x
      conv_lhs => rw [hx]
      conv_rhs => rw [hx]
      rw [map_sum, map_sum]
      simp only [map_smul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hwe i]
      rfl
    exact ggQ2xQ4_neg_one_notMem_E6 D hbas hE e he (by rw [← hwneg]; exact w.2)

private lemma ggQ2xQ4_diagram_auto_D_E7 (D : GGQ2Lin 3) (e : Fin 7 ≃ D.ι)
    (hc : ∀ a b, D.cartan (e a) (e b) = CartanMatrix.E 7 a b)
    (σ : D.ι ≃ D.ι) (hσ : ∀ i j, D.cartan (σ i) (σ j) = D.cartan i j) : σ = 1 := by
  set σ' : Equiv.Perm (Fin 7) := e.trans (σ.trans e.symm) with hσ'def
  have hσ' : ∀ a b, CartanMatrix.E 7 (σ' a) (σ' b) = CartanMatrix.E 7 a b := by
    intro a b
    have h1 := hc (σ' a) (σ' b)
    have h2 := hc a b
    have h3 := hσ (e a) (e b)
    have hea : e (σ' a) = σ (e a) := by simp [hσ'def]
    have heb : e (σ' b) = σ (e b) := by simp [hσ'def]
    rw [← h1, hea, heb, h3, h2]
  have h1 : σ' = 1 := ggQ2xQ4_diagram_auto_E7 σ' hσ'
  refine Equiv.ext fun i => ?_
  obtain ⟨a, rfl⟩ := e.surjective i
  have hh : σ' a = a := by
    have := DFunLike.congr_fun h1 a
    simpa using this
  simp only [hσ'def, Equiv.trans_apply] at hh
  have := congrArg e hh
  simpa using this

private lemma ggQ2xQ4_diagram_auto_D_E8 (D : GGQ2Lin 3) (e : Fin 8 ≃ D.ι)
    (hc : ∀ a b, D.cartan (e a) (e b) = CartanMatrix.E 8 a b)
    (σ : D.ι ≃ D.ι) (hσ : ∀ i j, D.cartan (σ i) (σ j) = D.cartan i j) : σ = 1 := by
  set σ' : Equiv.Perm (Fin 8) := e.trans (σ.trans e.symm) with hσ'def
  have hσ' : ∀ a b, CartanMatrix.E 8 (σ' a) (σ' b) = CartanMatrix.E 8 a b := by
    intro a b
    have h1 := hc (σ' a) (σ' b)
    have h2 := hc a b
    have h3 := hσ (e a) (e b)
    have hea : e (σ' a) = σ (e a) := by simp [hσ'def]
    have heb : e (σ' b) = σ (e b) := by simp [hσ'def]
    rw [← h1, hea, heb, h3, h2]
  have h1 : σ' = 1 := ggQ2xQ4_diagram_auto_E8 σ' hσ'
  refine Equiv.ext fun i => ?_
  obtain ⟨a, rfl⟩ := e.surjective i
  have hh : σ' a = a := by
    have := DFunLike.congr_fun h1 a
    simpa using this
  simp only [hσ'def, Equiv.trans_apply] at hh
  have := congrArg e hh
  simpa using this

private theorem ggQ2xQ_Q4 (D : GGQ2Lin 3) (hbas : D.Basis) (hE : ggQ2xQ_IsE D)
    (γ : D.ι → (D.ι → ℤ)) (hroot : ∀ k, ggQ2xQ_IsRoot D (γ k))
    (hframe : ∀ i j, ggQ2xQ_intForm D (γ i) (γ j) = D.cartan i j) :
    ∃ (u : ggQ2xQ_intWeyl D) (ε : ℤ), (ε = 1 ∨ ε = -1) ∧
      ∀ k, γ k = ε • (u : (D.ι → ℤ) ≃ₗ[ℤ] (D.ι → ℤ)) (Pi.single k 1) := by
  obtain ⟨u, σ, hσ, hγ⟩ := ggQ2xQ4_frame_perm D hbas hE γ hroot hframe
  have hEall : ggQ2xQ_IsE D := hE
  rcases hE with ⟨e, he⟩ | ⟨e, he⟩ | ⟨e, he⟩
  · have hc := ggQ2xQ_cartan_E6 D e he
    rcases ggQ2xQ4_diagram_auto_D_E6 D e hc σ hσ with hσ1 | hστ
    · refine ⟨u, 1, Or.inl rfl, fun k => ?_⟩
      rw [hγ k, hσ1]
      simp
    · obtain ⟨w, hwγ⟩ := ggQ2xQ4_E6_negperm D hbas hEall e he σ hσ
        (by rw [hστ]; exact ggQ2xQ4_tau6_ne_one D e)
      refine ⟨u * w, -1, Or.inr rfl, fun k => ?_⟩
      have h2 : Pi.single (σ k) (1:ℤ) =
          - ((w : (D.ι → ℤ) ≃ₗ[ℤ] (D.ι → ℤ)) (Pi.single k (1:ℤ))) := by
        rw [hwγ k, neg_neg]
      calc γ k = (u : (D.ι → ℤ) ≃ₗ[ℤ] (D.ι → ℤ)) (Pi.single (σ k) 1) := hγ k
        _ = (u : (D.ι → ℤ) ≃ₗ[ℤ] (D.ι → ℤ))
              (- ((w : (D.ι → ℤ) ≃ₗ[ℤ] (D.ι → ℤ)) (Pi.single k (1:ℤ)))) := by rw [h2]
        _ = - ((u : (D.ι → ℤ) ≃ₗ[ℤ] (D.ι → ℤ))
              ((w : (D.ι → ℤ) ≃ₗ[ℤ] (D.ι → ℤ)) (Pi.single k (1:ℤ)))) := by rw [map_neg]
        _ = (-1 : ℤ) • ((u * w : ggQ2xQ_intWeyl D) :
              (D.ι → ℤ) ≃ₗ[ℤ] (D.ι → ℤ)) (Pi.single k 1) := by
              rw [show ((u * w : ggQ2xQ_intWeyl D) :
                  (D.ι → ℤ) ≃ₗ[ℤ] (D.ι → ℤ)) =
                (u : (D.ι → ℤ) ≃ₗ[ℤ] (D.ι → ℤ)) *
                (w : (D.ι → ℤ) ≃ₗ[ℤ] (D.ι → ℤ)) from rfl,
                LinearEquiv.mul_apply, neg_one_smul]
  · have hc := ggQ2xQ_cartan_E7 D e he
    have hσ1 : σ = 1 := ggQ2xQ4_diagram_auto_D_E7 D e hc σ hσ
    refine ⟨u, 1, Or.inl rfl, fun k => ?_⟩
    rw [hγ k, hσ1]
    simp
  · have hc := ggQ2xQ_cartan_E8 D e he
    have hσ1 : σ = 1 := ggQ2xQ4_diagram_auto_D_E8 D e hc σ hσ
    refine ⟨u, 1, Or.inl rfl, fun k => ?_⟩
    rw [hγ k, hσ1]
    simp

private theorem ggQ2xQ5_sign_E6 (B : Fin 6 → Fin 6 → ℤ)
    (hBz : ∀ a c, a ≠ c → CartanMatrix.E 6 a c = 0 → B a c = 0)
    (hBu : ∀ a c, a ≠ c → CartanMatrix.E 6 a c ≠ 0 → B a c = 1 ∨ B a c = -1)
    (hBsym : ∀ a c, B a c = B c a) :
    ∃ s : Fin 6 → ℤˣ, ∀ a c, a ≠ c → (s a : ℤ) * (s c : ℤ) * B a c = CartanMatrix.E 6 a c := by
  have h02 := hBu 0 2 (by decide) (by decide)
  have h23 := hBu 2 3 (by decide) (by decide)
  have h31 := hBu 3 1 (by decide) (by decide)
  have h34 := hBu 3 4 (by decide) (by decide)
  have h45 := hBu 4 5 (by decide) (by decide)
  let g : Fin 6 → ℤ := ![
    1, -(B 0 2 * B 2 3 * B 3 1), -B 0 2, B 0 2 * B 2 3, -(B 0 2 * B 2 3 * B 3 4),
    B 0 2 * B 2 3 * B 3 4 * B 4 5]
  have hg0 : g 0 = 1 := by simp [g]
  have hg1 : g 1 = -(B 0 2 * B 2 3 * B 3 1) := by simp [g]
  have hg2 : g 2 = -B 0 2 := by simp [g]
  have hg3 : g 3 = B 0 2 * B 2 3 := by simp [g]
  have hg4 : g 4 = -(B 0 2 * B 2 3 * B 3 4) := by simp [g]
  have hg5 : g 5 = B 0 2 * B 2 3 * B 3 4 * B 4 5 := by simp [g]
  have hu1 : g 1 = 1 ∨ g 1 = -1 := by
    rw [hg1]; rcases h02 with h0|h0 <;> rcases h23 with h1|h1 <;> rcases h31 with h2|h2 <;>
    simp [h0, h1, h2]
  have hu2 : g 2 = 1 ∨ g 2 = -1 := by
    rw [hg2]; rcases h02 with h0|h0 <;> simp [h0]
  have hu3 : g 3 = 1 ∨ g 3 = -1 := by
    rw [hg3]; rcases h02 with h0|h0 <;> rcases h23 with h1|h1 <;> simp [h0, h1]
  have hu4 : g 4 = 1 ∨ g 4 = -1 := by
    rw [hg4]; rcases h02 with h0|h0 <;> rcases h23 with h1|h1 <;> rcases h34 with h2|h2 <;>
    simp [h0, h1, h2]
  have hu5 : g 5 = 1 ∨ g 5 = -1 := by
    rw [hg5]; rcases h02 with h0|h0 <;> rcases h23 with h1|h1 <;> rcases h34 with h2|h2 <;>
    rcases h45 with h3|h3 <;> simp [h0, h1, h2, h3]
  have hunit : ∀ a, g a = 1 ∨ g a = -1 := by
    intro a
    fin_cases a
    · exact Or.inl hg0
    · exact hu1
    · exact hu2
    · exact hu3
    · exact hu4
    · exact hu5
  have hr02 : g 0 = - g 2 * B 0 2 := by
    rw [hg0, hg2]; rcases h02 with h|h <;> simp [h]
  have hr20 : g 2 = - g 0 * B 2 0 := by
    rw [hg2, hg0, hBsym 2 0]; ring
  have hr23 : g 2 = - g 3 * B 2 3 := by
    rw [hg2, hg3]; rcases h23 with h|h <;> simp [h]
  have hr32 : g 3 = - g 2 * B 3 2 := by
    rw [hg3, hg2, hBsym 3 2]; ring
  have hr31 : g 3 = - g 1 * B 3 1 := by
    rw [hg3, hg1]; rcases h31 with h|h <;> simp [h]
  have hr13 : g 1 = - g 3 * B 1 3 := by
    rw [hg1, hg3, hBsym 1 3]; ring
  have hr34 : g 3 = - g 4 * B 3 4 := by
    rw [hg3, hg4]; rcases h34 with h|h <;> simp [h]
  have hr43 : g 4 = - g 3 * B 4 3 := by
    rw [hg4, hg3, hBsym 4 3]; ring
  have hr45 : g 4 = - g 5 * B 4 5 := by
    rw [hg4, hg5]; rcases h45 with h|h <;> simp [h]
  have hr54 : g 5 = - g 4 * B 5 4 := by
    rw [hg5, hg4, hBsym 5 4]; ring
  have hrel : ∀ a c, a ≠ c → CartanMatrix.E 6 a c ≠ 0 → g a = - g c * B a c := by
    intro a c hac hne
    fin_cases a <;> fin_cases c <;>
      first
      | exact (hac rfl).elim
      | exact (hne (by decide)).elim
      | exact hr02
      | exact hr20
      | exact hr23
      | exact hr32
      | exact hr31
      | exact hr13
      | exact hr34
      | exact hr43
      | exact hr45
      | exact hr54
  have hCval : ∀ a c, a ≠ c → CartanMatrix.E 6 a c = 0 ∨ CartanMatrix.E 6 a c = -1 := by
    intro a c hac
    fin_cases a <;> fin_cases c <;> first | exact (hac rfl).elim | decide
  have hedge : ∀ a c, a ≠ c → g a * g c * B a c = CartanMatrix.E 6 a c := by
    intro a c hac
    by_cases h0 : CartanMatrix.E 6 a c = 0
    · rw [hBz a c hac h0, h0]; ring
    · have hCneg : CartanMatrix.E 6 a c = -1 := (hCval a c hac).resolve_left h0
      rw [hrel a c hac h0, hCneg]
      have hc := hunit c
      have hb := hBu a c hac h0
      rcases hc with hc|hc <;> rcases hb with hb|hb <;> rw [hc, hb] <;> ring
  refine ⟨fun i => if g i = 1 then (1 : ℤˣ) else -1, ?_⟩
  intro a c hac
  have ha := hunit a
  have hc := hunit c
  have hca : ((if g a = 1 then (1 : ℤˣ) else -1 : ℤˣ) : ℤ) = g a := by
    rcases ha with h|h <;> simp [h]
  have hcc : ((if g c = 1 then (1 : ℤˣ) else -1 : ℤˣ) : ℤ) = g c := by
    rcases hc with h|h <;> simp [h]
  rw [hca, hcc]
  exact hedge a c hac

private theorem ggQ2xQ5_sign_E7 (B : Fin 7 → Fin 7 → ℤ)
    (hBz : ∀ a c, a ≠ c → CartanMatrix.E 7 a c = 0 → B a c = 0)
    (hBu : ∀ a c, a ≠ c → CartanMatrix.E 7 a c ≠ 0 → B a c = 1 ∨ B a c = -1)
    (hBsym : ∀ a c, B a c = B c a) :
    ∃ s : Fin 7 → ℤˣ, ∀ a c, a ≠ c → (s a : ℤ) * (s c : ℤ) * B a c = CartanMatrix.E 7 a c := by
  have h02 := hBu 0 2 (by decide) (by decide)
  have h23 := hBu 2 3 (by decide) (by decide)
  have h31 := hBu 3 1 (by decide) (by decide)
  have h34 := hBu 3 4 (by decide) (by decide)
  have h45 := hBu 4 5 (by decide) (by decide)
  have h56 := hBu 5 6 (by decide) (by decide)
  let g : Fin 7 → ℤ := ![
    1, -(B 0 2 * B 2 3 * B 3 1), -B 0 2, B 0 2 * B 2 3, -(B 0 2 * B 2 3 * B 3 4),
    B 0 2 * B 2 3 * B 3 4 * B 4 5, -(B 0 2 * B 2 3 * B 3 4 * B 4 5 * B 5 6)]
  have hg0 : g 0 = 1 := by simp [g]
  have hg1 : g 1 = -(B 0 2 * B 2 3 * B 3 1) := by simp [g]
  have hg2 : g 2 = -B 0 2 := by simp [g]
  have hg3 : g 3 = B 0 2 * B 2 3 := by simp [g]
  have hg4 : g 4 = -(B 0 2 * B 2 3 * B 3 4) := by simp [g]
  have hg5 : g 5 = B 0 2 * B 2 3 * B 3 4 * B 4 5 := by simp [g]
  have hg6 : g 6 = -(B 0 2 * B 2 3 * B 3 4 * B 4 5 * B 5 6) := by simp [g]
  have hu1 : g 1 = 1 ∨ g 1 = -1 := by
    rw [hg1]; rcases h02 with h0|h0 <;> rcases h23 with h1|h1 <;> rcases h31 with h2|h2 <;>
    simp [h0, h1, h2]
  have hu2 : g 2 = 1 ∨ g 2 = -1 := by
    rw [hg2]; rcases h02 with h0|h0 <;> simp [h0]
  have hu3 : g 3 = 1 ∨ g 3 = -1 := by
    rw [hg3]; rcases h02 with h0|h0 <;> rcases h23 with h1|h1 <;> simp [h0, h1]
  have hu4 : g 4 = 1 ∨ g 4 = -1 := by
    rw [hg4]; rcases h02 with h0|h0 <;> rcases h23 with h1|h1 <;> rcases h34 with h2|h2 <;>
    simp [h0, h1, h2]
  have hu5 : g 5 = 1 ∨ g 5 = -1 := by
    rw [hg5]; rcases h02 with h0|h0 <;> rcases h23 with h1|h1 <;> rcases h34 with h2|h2 <;>
    rcases h45 with h3|h3 <;> simp [h0, h1, h2, h3]
  have hu6 : g 6 = 1 ∨ g 6 = -1 := by
    rw [hg6]; rcases h02 with h0|h0 <;> rcases h23 with h1|h1 <;> rcases h34 with h2|h2 <;>
    rcases h45 with h3|h3 <;> rcases h56 with h4|h4 <;> simp [h0, h1, h2, h3, h4]
  have hunit : ∀ a, g a = 1 ∨ g a = -1 := by
    intro a
    fin_cases a
    · exact Or.inl hg0
    · exact hu1
    · exact hu2
    · exact hu3
    · exact hu4
    · exact hu5
    · exact hu6
  have hr02 : g 0 = - g 2 * B 0 2 := by
    rw [hg0, hg2]; rcases h02 with h|h <;> simp [h]
  have hr20 : g 2 = - g 0 * B 2 0 := by
    rw [hg2, hg0, hBsym 2 0]; ring
  have hr23 : g 2 = - g 3 * B 2 3 := by
    rw [hg2, hg3]; rcases h23 with h|h <;> simp [h]
  have hr32 : g 3 = - g 2 * B 3 2 := by
    rw [hg3, hg2, hBsym 3 2]; ring
  have hr31 : g 3 = - g 1 * B 3 1 := by
    rw [hg3, hg1]; rcases h31 with h|h <;> simp [h]
  have hr13 : g 1 = - g 3 * B 1 3 := by
    rw [hg1, hg3, hBsym 1 3]; ring
  have hr34 : g 3 = - g 4 * B 3 4 := by
    rw [hg3, hg4]; rcases h34 with h|h <;> simp [h]
  have hr43 : g 4 = - g 3 * B 4 3 := by
    rw [hg4, hg3, hBsym 4 3]; ring
  have hr45 : g 4 = - g 5 * B 4 5 := by
    rw [hg4, hg5]; rcases h45 with h|h <;> simp [h]
  have hr54 : g 5 = - g 4 * B 5 4 := by
    rw [hg5, hg4, hBsym 5 4]; ring
  have hr56 : g 5 = - g 6 * B 5 6 := by
    rw [hg5, hg6]; rcases h56 with h|h <;> simp [h]
  have hr65 : g 6 = - g 5 * B 6 5 := by
    rw [hg6, hg5, hBsym 6 5]; ring
  have hrel : ∀ a c, a ≠ c → CartanMatrix.E 7 a c ≠ 0 → g a = - g c * B a c := by
    intro a c hac hne
    fin_cases a <;> fin_cases c <;>
      first
      | exact (hac rfl).elim
      | exact (hne (by decide)).elim
      | exact hr02
      | exact hr20
      | exact hr23
      | exact hr32
      | exact hr31
      | exact hr13
      | exact hr34
      | exact hr43
      | exact hr45
      | exact hr54
      | exact hr56
      | exact hr65
  have hCval : ∀ a c, a ≠ c → CartanMatrix.E 7 a c = 0 ∨ CartanMatrix.E 7 a c = -1 := by
    intro a c hac
    fin_cases a <;> fin_cases c <;> first | exact (hac rfl).elim | decide
  have hedge : ∀ a c, a ≠ c → g a * g c * B a c = CartanMatrix.E 7 a c := by
    intro a c hac
    by_cases h0 : CartanMatrix.E 7 a c = 0
    · rw [hBz a c hac h0, h0]; ring
    · have hCneg : CartanMatrix.E 7 a c = -1 := (hCval a c hac).resolve_left h0
      rw [hrel a c hac h0, hCneg]
      have hc := hunit c
      have hb := hBu a c hac h0
      rcases hc with hc|hc <;> rcases hb with hb|hb <;> rw [hc, hb] <;> ring
  refine ⟨fun i => if g i = 1 then (1 : ℤˣ) else -1, ?_⟩
  intro a c hac
  have ha := hunit a
  have hc := hunit c
  have hca : ((if g a = 1 then (1 : ℤˣ) else -1 : ℤˣ) : ℤ) = g a := by
    rcases ha with h|h <;> simp [h]
  have hcc : ((if g c = 1 then (1 : ℤˣ) else -1 : ℤˣ) : ℤ) = g c := by
    rcases hc with h|h <;> simp [h]
  rw [hca, hcc]
  exact hedge a c hac

private theorem ggQ2xQ5_sign_E8 (B : Fin 8 → Fin 8 → ℤ)
    (hBz : ∀ a c, a ≠ c → CartanMatrix.E 8 a c = 0 → B a c = 0)
    (hBu : ∀ a c, a ≠ c → CartanMatrix.E 8 a c ≠ 0 → B a c = 1 ∨ B a c = -1)
    (hBsym : ∀ a c, B a c = B c a) :
    ∃ s : Fin 8 → ℤˣ, ∀ a c, a ≠ c → (s a : ℤ) * (s c : ℤ) * B a c = CartanMatrix.E 8 a c := by
  have h02 := hBu 0 2 (by decide) (by decide)
  have h23 := hBu 2 3 (by decide) (by decide)
  have h31 := hBu 3 1 (by decide) (by decide)
  have h34 := hBu 3 4 (by decide) (by decide)
  have h45 := hBu 4 5 (by decide) (by decide)
  have h56 := hBu 5 6 (by decide) (by decide)
  have h67 := hBu 6 7 (by decide) (by decide)
  let g : Fin 8 → ℤ := ![
    1, -(B 0 2 * B 2 3 * B 3 1), -B 0 2, B 0 2 * B 2 3, -(B 0 2 * B 2 3 * B 3 4),
    B 0 2 * B 2 3 * B 3 4 * B 4 5, -(B 0 2 * B 2 3 * B 3 4 * B 4 5 * B 5 6),
    B 0 2 * B 2 3 * B 3 4 * B 4 5 * B 5 6 * B 6 7]
  have hg0 : g 0 = 1 := by simp [g]
  have hg1 : g 1 = -(B 0 2 * B 2 3 * B 3 1) := by simp [g]
  have hg2 : g 2 = -B 0 2 := by simp [g]
  have hg3 : g 3 = B 0 2 * B 2 3 := by simp [g]
  have hg4 : g 4 = -(B 0 2 * B 2 3 * B 3 4) := by simp [g]
  have hg5 : g 5 = B 0 2 * B 2 3 * B 3 4 * B 4 5 := by simp [g]
  have hg6 : g 6 = -(B 0 2 * B 2 3 * B 3 4 * B 4 5 * B 5 6) := by simp [g]
  have hg7 : g 7 = B 0 2 * B 2 3 * B 3 4 * B 4 5 * B 5 6 * B 6 7 := by simp [g]
  have hu1 : g 1 = 1 ∨ g 1 = -1 := by
    rw [hg1]; rcases h02 with h0|h0 <;> rcases h23 with h1|h1 <;> rcases h31 with h2|h2 <;>
    simp [h0, h1, h2]
  have hu2 : g 2 = 1 ∨ g 2 = -1 := by
    rw [hg2]; rcases h02 with h0|h0 <;> simp [h0]
  have hu3 : g 3 = 1 ∨ g 3 = -1 := by
    rw [hg3]; rcases h02 with h0|h0 <;> rcases h23 with h1|h1 <;> simp [h0, h1]
  have hu4 : g 4 = 1 ∨ g 4 = -1 := by
    rw [hg4]; rcases h02 with h0|h0 <;> rcases h23 with h1|h1 <;> rcases h34 with h2|h2 <;>
    simp [h0, h1, h2]
  have hu5 : g 5 = 1 ∨ g 5 = -1 := by
    rw [hg5]; rcases h02 with h0|h0 <;> rcases h23 with h1|h1 <;> rcases h34 with h2|h2 <;>
    rcases h45 with h3|h3 <;> simp [h0, h1, h2, h3]
  have hu6 : g 6 = 1 ∨ g 6 = -1 := by
    rw [hg6]; rcases h02 with h0|h0 <;> rcases h23 with h1|h1 <;> rcases h34 with h2|h2 <;>
    rcases h45 with h3|h3 <;> rcases h56 with h4|h4 <;> simp [h0, h1, h2, h3, h4]
  have hu7 : g 7 = 1 ∨ g 7 = -1 := by
    rw [hg7]; rcases h02 with h0|h0 <;> rcases h23 with h1|h1 <;> rcases h34 with h2|h2 <;>
    rcases h45 with h3|h3 <;> rcases h56 with h4|h4 <;> rcases h67 with h5|h5 <;>
    simp [h0, h1, h2, h3, h4, h5]
  have hunit : ∀ a, g a = 1 ∨ g a = -1 := by
    intro a
    fin_cases a
    · exact Or.inl hg0
    · exact hu1
    · exact hu2
    · exact hu3
    · exact hu4
    · exact hu5
    · exact hu6
    · exact hu7
  have hr02 : g 0 = - g 2 * B 0 2 := by
    rw [hg0, hg2]; rcases h02 with h|h <;> simp [h]
  have hr20 : g 2 = - g 0 * B 2 0 := by
    rw [hg2, hg0, hBsym 2 0]; ring
  have hr23 : g 2 = - g 3 * B 2 3 := by
    rw [hg2, hg3]; rcases h23 with h|h <;> simp [h]
  have hr32 : g 3 = - g 2 * B 3 2 := by
    rw [hg3, hg2, hBsym 3 2]; ring
  have hr31 : g 3 = - g 1 * B 3 1 := by
    rw [hg3, hg1]; rcases h31 with h|h <;> simp [h]
  have hr13 : g 1 = - g 3 * B 1 3 := by
    rw [hg1, hg3, hBsym 1 3]; ring
  have hr34 : g 3 = - g 4 * B 3 4 := by
    rw [hg3, hg4]; rcases h34 with h|h <;> simp [h]
  have hr43 : g 4 = - g 3 * B 4 3 := by
    rw [hg4, hg3, hBsym 4 3]; ring
  have hr45 : g 4 = - g 5 * B 4 5 := by
    rw [hg4, hg5]; rcases h45 with h|h <;> simp [h]
  have hr54 : g 5 = - g 4 * B 5 4 := by
    rw [hg5, hg4, hBsym 5 4]; ring
  have hr56 : g 5 = - g 6 * B 5 6 := by
    rw [hg5, hg6]; rcases h56 with h|h <;> simp [h]
  have hr65 : g 6 = - g 5 * B 6 5 := by
    rw [hg6, hg5, hBsym 6 5]; ring
  have hr67 : g 6 = - g 7 * B 6 7 := by
    rw [hg6, hg7]; rcases h67 with h|h <;> simp [h]
  have hr76 : g 7 = - g 6 * B 7 6 := by
    rw [hg7, hg6, hBsym 7 6]; ring
  have hrel : ∀ a c, a ≠ c → CartanMatrix.E 8 a c ≠ 0 → g a = - g c * B a c := by
    intro a c hac hne
    fin_cases a <;> fin_cases c <;>
      first
      | exact (hac rfl).elim
      | exact (hne (by decide)).elim
      | exact hr02
      | exact hr20
      | exact hr23
      | exact hr32
      | exact hr31
      | exact hr13
      | exact hr34
      | exact hr43
      | exact hr45
      | exact hr54
      | exact hr56
      | exact hr65
      | exact hr67
      | exact hr76
  have hCval : ∀ a c, a ≠ c → CartanMatrix.E 8 a c = 0 ∨ CartanMatrix.E 8 a c = -1 := by
    intro a c hac
    fin_cases a <;> fin_cases c <;> first | exact (hac rfl).elim | decide
  have hedge : ∀ a c, a ≠ c → g a * g c * B a c = CartanMatrix.E 8 a c := by
    intro a c hac
    by_cases h0 : CartanMatrix.E 8 a c = 0
    · rw [hBz a c hac h0, h0]; ring
    · have hCneg : CartanMatrix.E 8 a c = -1 := (hCval a c hac).resolve_left h0
      rw [hrel a c hac h0, hCneg]
      have hc := hunit c
      have hb := hBu a c hac h0
      rcases hc with hc|hc <;> rcases hb with hb|hb <;> rw [hc, hb] <;> ring
  refine ⟨fun i => if g i = 1 then (1 : ℤˣ) else -1, ?_⟩
  intro a c hac
  have ha := hunit a
  have hc := hunit c
  have hca : ((if g a = 1 then (1 : ℤˣ) else -1 : ℤˣ) : ℤ) = g a := by
    rcases ha with h|h <;> simp [h]
  have hcc : ((if g c = 1 then (1 : ℤˣ) else -1 : ℤˣ) : ℤ) = g c := by
    rcases hc with h|h <;> simp [h]
  rw [hca, hcc]
  exact hedge a c hac

private lemma ggQ2xQ5_intForm_symm (D : GGQ2Lin 3) (hE : ggQ2xQ_IsE D) :
    (ggQ2xQ_intForm D).IsSymm := by
  have hC := ggQ2xQ_cartan_symm_of_E D hE
  refine ⟨fun x y => ?_⟩
  rw [ggQ2xQ_intForm_apply, ggQ2xQ_intForm_apply]
  calc ∑ i, ∑ j, x i * D.cartan i j * y j
      = ∑ i, ∑ j, y j * D.cartan j i * x i := by
        refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
        rw [hC i j]; ring
    _ = ∑ j, ∑ i, y j * D.cartan j i * x i := Finset.sum_comm
    _ = ∑ i, ∑ j, y i * D.cartan i j * x j := rfl

private lemma ggQ2xQ5_intForm_refl_preserve (D : GGQ2Lin 3) (hE : ggQ2xQ_IsE D)
    (k : D.ι) (x y : D.ι → ℤ) :
    ggQ2xQ_intForm D (ggQ2xQ_intRefl D k x) (ggQ2xQ_intRefl D k y)
      = ggQ2xQ_intForm D x y := by
  have hsym := ggQ2xQ5_intForm_symm D hE
  have hc : ggQ2xQ_intForm D (Pi.single k 1) (Pi.single k 1) = 2 :=
    ggQ2xQ_intForm_single_self D k
  rw [ggQ2xQ_intRefl_apply, ggQ2xQ_intRefl_apply]
  simp only [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
  rw [hsym.eq x (Pi.single k 1), hc]
  ring

private lemma ggQ2xQ5_intForm_preserve (D : GGQ2Lin 3) (hE : ggQ2xQ_IsE D)
    {w : (D.ι → ℤ) ≃ₗ[ℤ] (D.ι → ℤ)} (hw : w ∈ ggQ2xQ_intWeyl D) :
    ∀ x y, ggQ2xQ_intForm D (w x) (w y) = ggQ2xQ_intForm D x y := by
  have hgen : ∀ u ∈ Set.range (ggQ2xQ_intRefl D), ∀ x y,
      ggQ2xQ_intForm D (u x) (u y) = ggQ2xQ_intForm D x y := by
    rintro u ⟨k, rfl⟩
    exact ggQ2xQ5_intForm_refl_preserve D hE k
  have hw' : w ∈ Subgroup.closure (Set.range (ggQ2xQ_intRefl D)) := hw
  exact Subgroup.closure_induction (k := Set.range (ggQ2xQ_intRefl D))
    (p := fun u _ => ∀ x y, ggQ2xQ_intForm D (u x) (u y) = ggQ2xQ_intForm D x y)
    (fun u hu => hgen u hu) (fun x y => rfl)
    (fun a b _ _ iha ihb => by
      intro x y
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, iha, ihb])
    (fun a _ iha => by
      intro x y
      have h := iha (a⁻¹ x) (a⁻¹ y)
      rw [show a (a⁻¹ x) = x from by simp [LinearEquiv.coe_inv],
        show a (a⁻¹ y) = y from by simp [LinearEquiv.coe_inv]] at h
      exact h.symm) hw'

private lemma ggQ2xQ5_intForm_root_self (D : GGQ2Lin 3) (hE : ggQ2xQ_IsE D)
    {γ : D.ι → ℤ} (hγ : ggQ2xQ_IsRoot D γ) :
    ggQ2xQ_intForm D γ γ = 2 := by
  obtain ⟨w, hw, k, hk⟩ := hγ
  rw [← hk, ggQ2xQ5_intForm_preserve D hE hw, ggQ2xQ_intForm_single_self]

private lemma ggQ2xQ5_intForm_smul (D : GGQ2Lin 3) (a b : ℤ) (x y : D.ι → ℤ) :
    ggQ2xQ_intForm D (a • x) (b • y) = a * b * ggQ2xQ_intForm D x y := by
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  ring

private lemma ggQ2xQ5_tc_smul_unit {V : Type*} [AddCommGroup V] [Module (ZMod 3) V]
    (B : LinearMap.BilinForm (ZMod 3) V) {η : ZMod 3} (hη : η = 1 ∨ η = -1) (c : V) :
    ggQ2xQ_tc B (η • c) = ggQ2xQ_tc B c := by
  rcases hη with rfl | rfl
  · rw [one_smul]
  · rw [neg_one_smul]; exact ggQ2xQ_tc_neg B c

private lemma ggQ2xQ5_linearEquiv_mul_eq_iff {V : Type*} [AddCommGroup V] [Module (ZMod 3) V]
    (e₁ e₂ e₃ e₄ : V ≃ₗ[ZMod 3] V) :
    (e₁ * e₂ = e₃ * e₄) ↔
      ((e₁ : V →ₗ[ZMod 3] V) * (e₂ : V →ₗ[ZMod 3] V) =
        (e₃ : V →ₗ[ZMod 3] V) * (e₄ : V →ₗ[ZMod 3] V)) := by
  constructor
  · intro h
    exact congrArg (fun e : V ≃ₗ[ZMod 3] V => (e : V →ₗ[ZMod 3] V)) h
  · intro h
    exact LinearEquiv.toLinearMap_injective h

private lemma ggQ2xQ5_mod3_eq_zero {m : ℤ} (hm : m ∈ ({-1, 0, 1} : Set ℤ))
    (h : (m : ZMod 3) = 0) : m = 0 := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
  rcases hm with rfl | rfl | rfl <;> revert h <;> decide

private lemma ggQ2xQ5_mod3_ne_zero {m : ℤ} (hm : m ∈ ({-1, 0, 1} : Set ℤ))
    (h : (m : ZMod 3) ≠ 0) : m = 1 ∨ m = -1 := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
  rcases hm with rfl | rfl | rfl <;> revert h <;> decide

private lemma ggQ2xQ5_form_rhoBar (D : GGQ2Lin 3) (hbas : D.Basis) (x y : D.ι → ℤ) :
    ggQ2xQ_form D hbas (ggQ2xQ_rhoBar D x) (ggQ2xQ_rhoBar D y)
      = (ggQ2xQ_intForm D x y : ZMod 3) := by
  have hx : ggQ2xQ_form D hbas (ggQ2xQ_rhoBar D x)
      = ∑ k, (x k : ZMod 3) • D.root k := by
    rw [ggQ2xQ_rhoBar]
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [map_smul, ggQ2xQ_form_root]
  rw [hx, ggQ2xQ_intForm_apply, Int.cast_sum]
  rw [LinearMap.sum_apply]
  simp only [LinearMap.smul_apply, smul_eq_mul]
  have hy : ∀ k, D.root k (ggQ2xQ_rhoBar D y)
      = ∑ j, (y j : ZMod 3) * (D.cartan k j : ZMod 3) := by
    intro k
    rw [ggQ2xQ_rhoBar]
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [map_smul, D.pairing, smul_eq_mul]
  simp only [hy]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

private theorem ggQ2xQ_Q5 (D : GGQ2Lin 3) (hE : ggQ2xQ_IsE D) (b : D.ι → D.ι → ℤ)
    (hbsym : ∀ i j, b i j = b j i)
    (hb : ∀ i j, i ≠ j →
      (D.cartan i j = 0 → b i j = 0) ∧ (D.cartan i j ≠ 0 → (b i j = 1 ∨ b i j = -1))) :
    ∃ ε : D.ι → ℤˣ,
      ∀ i j, i ≠ j → (ε i : ℤ) * (ε j : ℤ) * b i j = D.cartan i j := by
  classical
  rcases hE with ⟨e, he⟩ | ⟨e, he⟩ | ⟨e, he⟩
  · have hC : ∀ a c, D.cartan (e a) (e c) = CartanMatrix.E 6 a c := ggQ2xQ_cartan_E6 D e he
    obtain ⟨s, hs⟩ := ggQ2xQ5_sign_E6 (fun a c => b (e a) (e c))
      (fun a c hac h => (hb (e a) (e c) (fun hh => hac (e.injective hh))).1 (by rw [hC]; exact h))
      (fun a c hac h => (hb (e a) (e c) (fun hh => hac (e.injective hh))).2 (by rw [hC]; exact h))
      (fun a c => hbsym (e a) (e c))
    refine ⟨fun i => s (e.symm i), ?_⟩
    intro i j hij
    obtain ⟨a, rfl⟩ := e.surjective i
    obtain ⟨c, rfl⟩ := e.surjective j
    have hac : a ≠ c := fun h => hij (by rw [h])
    simpa [hC] using hs a c hac
  · have hC : ∀ a c, D.cartan (e a) (e c) = CartanMatrix.E 7 a c := ggQ2xQ_cartan_E7 D e he
    obtain ⟨s, hs⟩ := ggQ2xQ5_sign_E7 (fun a c => b (e a) (e c))
      (fun a c hac h => (hb (e a) (e c) (fun hh => hac (e.injective hh))).1 (by rw [hC]; exact h))
      (fun a c hac h => (hb (e a) (e c) (fun hh => hac (e.injective hh))).2 (by rw [hC]; exact h))
      (fun a c => hbsym (e a) (e c))
    refine ⟨fun i => s (e.symm i), ?_⟩
    intro i j hij
    obtain ⟨a, rfl⟩ := e.surjective i
    obtain ⟨c, rfl⟩ := e.surjective j
    have hac : a ≠ c := fun h => hij (by rw [h])
    simpa [hC] using hs a c hac
  · have hC : ∀ a c, D.cartan (e a) (e c) = CartanMatrix.E 8 a c := ggQ2xQ_cartan_E8 D e he
    obtain ⟨s, hs⟩ := ggQ2xQ5_sign_E8 (fun a c => b (e a) (e c))
      (fun a c hac h => (hb (e a) (e c) (fun hh => hac (e.injective hh))).1 (by rw [hC]; exact h))
      (fun a c hac h => (hb (e a) (e c) (fun hh => hac (e.injective hh))).2 (by rw [hC]; exact h))
      (fun a c => hbsym (e a) (e c))
    refine ⟨fun i => s (e.symm i), ?_⟩
    intro i j hij
    obtain ⟨a, rfl⟩ := e.surjective i
    obtain ⟨c, rfl⟩ := e.surjective j
    have hac : a ≠ c := fun h => hij (by rw [h])
    simpa [hC] using hs a c hac

private theorem ggQ2xQ_frame (D : GGQ2Lin 3) (hbas : D.Basis) (hE : ggQ2xQ_IsE D)
    (π : (D.V ≃ₗ[ZMod 3] D.V) → (D.V ≃ₗ[ZMod 3] D.V))
    (hπT : ∀ t ∈ ggQ2xQ_isConjRefl D, π t ∈ ggQ2xQ_isConjRefl D)
    (hinj : Set.InjOn π (ggQ2xQ_isConjRefl D))
    (hπ : ∀ s ∈ ggQ2xQ_isConjRefl D, ∀ t ∈ ggQ2xQ_isConjRefl D,
      π (s * t * s⁻¹) = π s * π t * (π s)⁻¹) :
    ∃ g ∈ D.weyl, ∀ k : D.ι, π (D.simpleRefl k) = g * D.simpleRefl k * g⁻¹ := by
  classical
  let B : LinearMap.BilinForm (ZMod 3) D.V := ggQ2xQ_form D hbas
  have hCsym : ∀ i j, D.cartan i j = D.cartan j i := ggQ2xQ_cartan_symm_of_E D hE
  have hBsym : B.IsSymm := ggQ2xQ_form_isSymm D hbas hCsym
  have hcor2 : ∀ k, B (D.coroot k) (D.coroot k) = 2 := by
    intro k
    change (ggQ2xQ_form D hbas) (D.coroot k) (D.coroot k) = 2
    rw [ggQ2xQ_form_coroot, D.isCartan.1]
    norm_num
  have hsimple : ∀ k, D.simpleRefl k = ggQ2xQ_reflE B (D.coroot k) (hcor2 k) := by
    intro k
    ext v
    rw [GGQ2Lin.simpleRefl, Module.reflection_apply, ggQ2xQ_reflE_apply]
    change v - D.root k v • D.coroot k = v - (ggQ2xQ_form D hbas) (D.coroot k) v • D.coroot k
    rw [ggQ2xQ_form_root]
  have hsimplecoe : ∀ k, (D.simpleRefl k : D.V →ₗ[ZMod 3] D.V) = ggQ2xQ_tc B (D.coroot k) := by
    intro k
    rw [hsimple k, ggQ2xQ_reflE_coe]
  have hTclosed : ∀ s ∈ ggQ2xQ_isConjRefl D, ∀ t ∈ ggQ2xQ_isConjRefl D,
      s * t * s⁻¹ ∈ ggQ2xQ_isConjRefl D := by
    intro s hs t ht
    obtain ⟨k, w, hw, rfl⟩ := hs
    obtain ⟨j, v, hv, rfl⟩ := ht
    refine ⟨j, (w * D.simpleRefl k * w⁻¹) * v, ?_, ?_⟩
    · exact Subgroup.mul_mem _
        (Subgroup.mul_mem _ (Subgroup.mul_mem _ hw (ggQ2xQ_simpleRefl_mem_weyl D k))
          (Subgroup.inv_mem _ hw)) hv
    · group
  have hcoex_le : ∀ i j, D.coxeter i j ≤ 3 := by
    rcases hE with ⟨e, he⟩ | ⟨e, he⟩ | ⟨e, he⟩
    · intro i j
      obtain ⟨a, rfl⟩ := e.surjective i
      obtain ⟨c, rfl⟩ := e.surjective j
      rw [he, CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
      fin_cases a <;> fin_cases c <;> decide
    · intro i j
      obtain ⟨a, rfl⟩ := e.surjective i
      obtain ⟨c, rfl⟩ := e.surjective j
      rw [he, CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
      fin_cases a <;> fin_cases c <;> decide
    · intro i j
      obtain ⟨a, rfl⟩ := e.surjective i
      obtain ⟨c, rfl⟩ := e.surjective j
      rw [he, CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
      fin_cases a <;> fin_cases c <;> decide
  have hval : ∀ i j, i ≠ j → D.cartan i j = 0 ∨ D.cartan i j = -1 := by
    intro i j hij
    rcases D.isCartan.2 i j hij with ⟨hm, h1, -⟩ | ⟨hm, h1, -⟩ | ⟨hm, -, -⟩ | ⟨hm, -, -⟩
    · exact Or.inl h1
    · exact Or.inr h1
    · exfalso; have := hcoex_le i j; rw [hm] at this; omega
    · exfalso; have := hcoex_le i j; rw [hm] at this; omega
  have htc_ne_cor : ∀ i j, i ≠ j →
      ggQ2xQ_tc B (D.coroot i) ≠ ggQ2xQ_tc B (D.coroot j) := by
    intro i j hij h
    rcases (ggQ2xQ_tc_eq_tc_iff B hBsym (hcor2 i) (hcor2 j)).1 h with hji | hji
    · exact hij (hbas.1.injective hji).symm
    · have h2 : (D.cartan i j : ZMod 3) = -2 := by
        have h' := congrArg (D.root i) hji
        rw [map_neg, D.pairing, D.pairing, D.isCartan.1] at h'
        norm_num at h'
        exact h'
      rcases hval i j hij with h0 | hm1
      · rw [h0] at h2
        exact absurd h2 (by decide)
      · rw [hm1] at h2
        exact absurd h2 (by decide)
  have hs_ne : ∀ i j, i ≠ j → D.simpleRefl i ≠ D.simpleRefl j := by
    intro i j hij h
    apply htc_ne_cor i j hij
    rw [← hsimplecoe i, ← hsimplecoe j, h]
  have hstep1 : ∀ k, ∃ (γ : D.ι → ℤ), ggQ2xQ_IsRoot D γ ∧
      ∃ h : B (ggQ2xQ_rhoBar D γ) (ggQ2xQ_rhoBar D γ) = 2,
        π (D.simpleRefl k) = ggQ2xQ_reflE B (ggQ2xQ_rhoBar D γ) h := by
    intro k
    obtain ⟨γ, hroot, h, heq⟩ := ggQ2xQ_Q2_lift D hbas hE (π (D.simpleRefl k))
      (hπT (D.simpleRefl k) (ggQ2xQ_simpleRefl_mem_isConjRefl D k))
    exact ⟨γ, hroot, h, heq⟩
  choose γ hγ using hstep1
  have hroot : ∀ k, ggQ2xQ_IsRoot D (γ k) := fun k => (hγ k).1
  choose hk hπγ using fun k => (hγ k).2
  have htc_ne : ∀ i j, i ≠ j →
      ggQ2xQ_tc B (ggQ2xQ_rhoBar D (γ i)) ≠ ggQ2xQ_tc B (ggQ2xQ_rhoBar D (γ j)) := by
    intro i j hij h
    have hsij : π (D.simpleRefl i) = π (D.simpleRefl j) := by
      apply LinearEquiv.toLinearMap_injective
      rw [hπγ i, hπγ j, ggQ2xQ_reflE_coe, ggQ2xQ_reflE_coe]
      exact h
    exact hs_ne i j hij (hinj (ggQ2xQ_simpleRefl_mem_isConjRefl D i)
      (ggQ2xQ_simpleRefl_mem_isConjRefl D j) hsij)
  have hroot_ne : ∀ i j, i ≠ j → γ i ≠ γ j ∧ γ i ≠ - γ j := by
    intro i j hij
    have h := (ggQ2xQ_tc_eq_tc_iff B hBsym (hk i) (hk j)).not.mp (htc_ne i j hij)
    constructor
    · intro heq
      exact h (Or.inl (by rw [heq]))
    · intro heq
      exact h (Or.inr (by rw [heq, map_neg, neg_neg]))
  have hzero : ∀ i j, i ≠ j →
      (B (ggQ2xQ_rhoBar D (γ i)) (ggQ2xQ_rhoBar D (γ j)) = 0 ↔ D.cartan i j = 0) := by
    intro i j hij
    have h0 : B (ggQ2xQ_rhoBar D (γ i)) (ggQ2xQ_rhoBar D (γ j)) = 0 ↔
        ggQ2xQ_tc B (ggQ2xQ_rhoBar D (γ i)) * ggQ2xQ_tc B (ggQ2xQ_rhoBar D (γ j)) =
          ggQ2xQ_tc B (ggQ2xQ_rhoBar D (γ j)) * ggQ2xQ_tc B (ggQ2xQ_rhoBar D (γ i)) :=
      (ggQ2xQ_tc_comm_iff B hBsym (hk i) (hk j) (htc_ne i j hij)).symm
    have h1 : (ggQ2xQ_tc B (ggQ2xQ_rhoBar D (γ i)) *
          ggQ2xQ_tc B (ggQ2xQ_rhoBar D (γ j)) =
        ggQ2xQ_tc B (ggQ2xQ_rhoBar D (γ j)) *
          ggQ2xQ_tc B (ggQ2xQ_rhoBar D (γ i))) ↔
        (π (D.simpleRefl i) * π (D.simpleRefl j) =
          π (D.simpleRefl j) * π (D.simpleRefl i)) := by
      rw [ggQ2xQ5_linearEquiv_mul_eq_iff]
      rw [hπγ i, hπγ j, ggQ2xQ_reflE_coe, ggQ2xQ_reflE_coe]
    have h2 : (π (D.simpleRefl i) * π (D.simpleRefl j) =
          π (D.simpleRefl j) * π (D.simpleRefl i)) ↔
        (D.simpleRefl i * D.simpleRefl j = D.simpleRefl j * D.simpleRefl i) :=
      (ggQ2xQ_comm_iff_of_quandle (ggQ2xQ_isConjRefl D) hTclosed π hinj hπ
        (ggQ2xQ_simpleRefl_mem_isConjRefl D i)
        (ggQ2xQ_simpleRefl_mem_isConjRefl D j)).symm
    have h3 : (D.simpleRefl i * D.simpleRefl j = D.simpleRefl j * D.simpleRefl i) ↔
        ((D.simpleRefl i : D.V →ₗ[ZMod 3] D.V) * (D.simpleRefl j : D.V →ₗ[ZMod 3] D.V) =
          (D.simpleRefl j : D.V →ₗ[ZMod 3] D.V) *
            (D.simpleRefl i : D.V →ₗ[ZMod 3] D.V)) :=
      ggQ2xQ5_linearEquiv_mul_eq_iff _ _ _ _
    have h4 : ((D.simpleRefl i : D.V →ₗ[ZMod 3] D.V) *
          (D.simpleRefl j : D.V →ₗ[ZMod 3] D.V) =
          (D.simpleRefl j : D.V →ₗ[ZMod 3] D.V) *
            (D.simpleRefl i : D.V →ₗ[ZMod 3] D.V)) ↔
        B (D.coroot i) (D.coroot j) = 0 := by
      rw [hsimplecoe i, hsimplecoe j]
      exact ggQ2xQ_tc_comm_iff B hBsym (hcor2 i) (hcor2 j) (htc_ne_cor i j hij)
    have h5 : B (D.coroot i) (D.coroot j) = 0 ↔ D.cartan i j = 0 := by
      change (ggQ2xQ_form D hbas) (D.coroot i) (D.coroot j) = 0 ↔ D.cartan i j = 0
      rw [ggQ2xQ_form_coroot]
      constructor
      · intro h
        rcases hval i j hij with h0 | hm1
        · exact h0
        · rw [hm1] at h
          exact absurd h (by decide)
      · intro h
        rw [h]
        norm_num
    exact h0.trans (h1.trans (h2.trans (h3.trans (h4.trans h5))))
  let b : D.ι → D.ι → ℤ := fun i j => ggQ2xQ_intForm D (γ i) (γ j)
  have hbsym : ∀ i j, b i j = b j i := by
    intro i j
    change ggQ2xQ_intForm D (γ i) (γ j) = ggQ2xQ_intForm D (γ j) (γ i)
    exact (ggQ2xQ5_intForm_symm D hE).eq (γ i) (γ j)
  have hQ3 : ∀ i j, i ≠ j → b i j ∈ ({-1, 0, 1} : Set ℤ) := by
    intro i j hij
    have hmem := (ggQ2xQ_Q3 D hbas hE).2 (γ i) (γ j) (hroot i) (hroot j)
      (hroot_ne i j hij).1 (hroot_ne i j hij).2
    change ggQ2xQ_intForm D (γ i) (γ j) ∈ ({-1, 0, 1} : Set ℤ)
    rw [ggQ2xQ_intForm_apply]
    exact hmem
  have hb : ∀ i j, i ≠ j →
      (D.cartan i j = 0 → b i j = 0) ∧
        (D.cartan i j ≠ 0 → (b i j = 1 ∨ b i j = -1)) := by
    intro i j hij
    have hmod : (b i j : ZMod 3) = 0 ↔ D.cartan i j = 0 := by
      change ((ggQ2xQ_intForm D (γ i) (γ j) : ℤ) : ZMod 3) = 0 ↔ D.cartan i j = 0
      rw [← ggQ2xQ5_form_rhoBar D hbas (γ i) (γ j)]
      exact hzero i j hij
    constructor
    · intro h0
      exact ggQ2xQ5_mod3_eq_zero (hQ3 i j hij) (hmod.mpr h0)
    · intro hne
      exact ggQ2xQ5_mod3_ne_zero (hQ3 i j hij) (fun h => hne (hmod.mp h))
  obtain ⟨ε, hε⟩ := ggQ2xQ_Q5 D hE b hbsym hb
  let δ : D.ι → D.ι → ℤ := fun k => (ε k : ℤ) • γ k
  have hδroot : ∀ k, ggQ2xQ_IsRoot D (δ k) := by
    intro k
    change ggQ2xQ_IsRoot D ((ε k : ℤ) • γ k)
    rcases Int.units_eq_one_or (ε k) with h1 | h1
    · rw [h1]; simp only [Units.val_one, one_smul]; exact hroot k
    · rw [h1]; simp only [Units.val_neg, Units.val_one, neg_one_smul]
      exact ggQ2xQ_IsRoot_neg D (hroot k)
  have hδframe : ∀ i j, ggQ2xQ_intForm D (δ i) (δ j) = D.cartan i j := by
    intro i j
    by_cases hij : i = j
    · subst hij
      change ggQ2xQ_intForm D ((ε i : ℤ) • γ i) ((ε i : ℤ) • γ i) = D.cartan i i
      rw [ggQ2xQ5_intForm_smul, ggQ2xQ5_intForm_root_self D hE (hroot i), D.isCartan.1]
      rcases Int.units_eq_one_or (ε i) with h1 | h1 <;> rw [h1] <;> norm_num
    · change ggQ2xQ_intForm D ((ε i : ℤ) • γ i) ((ε j : ℤ) • γ j) = D.cartan i j
      rw [ggQ2xQ5_intForm_smul]
      exact hε i j hij
  obtain ⟨u, e, he1, hδu⟩ := ggQ2xQ_Q4 D hbas hE δ hδroot hδframe
  obtain ⟨g, hgweyl, hg⟩ := ggQ2xQ_Q2_red D hbas hE u
  refine ⟨g, hgweyl, ?_⟩
  intro k
  have hck : ggQ2xQ_rhoBar D (γ k)
      = (((ε k : ℤ) * e : ℤ) : ZMod 3) • g (D.coroot k) := by
    have h2 : ((ε k : ℤ) : ZMod 3) • ggQ2xQ_rhoBar D (γ k)
        = (e : ZMod 3) • g (D.coroot k) := by
      have hδk : δ k = (ε k : ℤ) • γ k := rfl
      have hρ : ggQ2xQ_rhoBar D (δ k) = ggQ2xQ_rhoBar D
          (e • (u : (D.ι → ℤ) ≃ₗ[ℤ] (D.ι → ℤ)) (Pi.single k 1)) := by rw [hδu k]
      rw [hδk] at hρ
      rw [map_smul] at hρ
      rw [map_smul, hg, ggQ2xQ_rhoBar_single] at hρ
      simpa only [Int.cast_smul_eq_zsmul] using hρ
    have hunit : ((ε k : ℤ) : ZMod 3) * ((ε k : ℤ) : ZMod 3) = 1 := by
      have h : (ε k : ℤ) * (ε k : ℤ) = 1 := by
        rcases Int.units_eq_one_or (ε k) with h|h <;> rw [h] <;> norm_num
      rw [← Int.cast_mul, h, Int.cast_one]
    calc ggQ2xQ_rhoBar D (γ k)
        = (((ε k : ℤ) : ZMod 3) * ((ε k : ℤ) : ZMod 3)) •
            ggQ2xQ_rhoBar D (γ k) := by rw [hunit, one_smul]
      _ = ((ε k : ℤ) : ZMod 3) •
            (((ε k : ℤ) : ZMod 3) • ggQ2xQ_rhoBar D (γ k)) := by rw [mul_smul]
      _ = ((ε k : ℤ) : ZMod 3) • ((e : ZMod 3) • g (D.coroot k)) := by rw [h2]
      _ = (((ε k : ℤ) : ZMod 3) * (e : ZMod 3)) • g (D.coroot k) := by rw [smul_smul]
      _ = (((ε k : ℤ) * e : ℤ) : ZMod 3) • g (D.coroot k) := by rw [Int.cast_mul]
  have hη : (((ε k : ℤ) * e : ℤ) : ZMod 3) = 1 ∨
      (((ε k : ℤ) * e : ℤ) : ZMod 3) = -1 := by
    rcases Int.units_eq_one_or (ε k) with h|h <;> rcases he1 with he|he <;>
      rw [h, he] <;> norm_num
  have htc : ggQ2xQ_tc B (ggQ2xQ_rhoBar D (γ k)) = ggQ2xQ_tc B (g (D.coroot k)) := by
    rw [hck]
    exact ggQ2xQ5_tc_smul_unit B hη (g (D.coroot k))
  have hπcoe : ((π (D.simpleRefl k) : D.V ≃ₗ[ZMod 3] D.V) : D.V →ₗ[ZMod 3] D.V)
      = ggQ2xQ_tc B (ggQ2xQ_rhoBar D (γ k)) := by
    rw [hπγ k, ggQ2xQ_reflE_coe]
  have hgconj : ((g * D.simpleRefl k * g⁻¹ : D.V ≃ₗ[ZMod 3] D.V) : D.V →ₗ[ZMod 3] D.V)
      = ggQ2xQ_tc B (g (D.coroot k)) := by
    obtain ⟨h', heq⟩ := ggQ2xQ_conj_simpleRefl D hbas hCsym k hgweyl
    rw [heq]
    exact ggQ2xQ_reflE_coe B (g (D.coroot k)) h'
  apply LinearEquiv.toLinearMap_injective
  rw [hπcoe, hgconj]
  exact htc

end QuandleAssembly

theorem ggQ2_quandle_aut_E (D : GGQ2Lin 3) (hbas : D.Basis)
    (hE : (∃ e : Fin 6 ≃ D.ι, D.coxeter = CoxeterMatrix.E₆.reindex e) ∨
      (∃ e : Fin 7 ≃ D.ι, D.coxeter = CoxeterMatrix.E₇.reindex e) ∨
      (∃ e : Fin 8 ≃ D.ι, D.coxeter = CoxeterMatrix.E₈.reindex e))
    (π : (D.V ≃ₗ[ZMod 3] D.V) → (D.V ≃ₗ[ZMod 3] D.V))
    (hπT : ∀ t ∈ ggQ2xQ_isConjRefl D, π t ∈ ggQ2xQ_isConjRefl D)
    (hinj : Set.InjOn π (ggQ2xQ_isConjRefl D))
    (hsurj : Set.SurjOn π (ggQ2xQ_isConjRefl D) (ggQ2xQ_isConjRefl D))
    (hπ : ∀ s ∈ ggQ2xQ_isConjRefl D, ∀ t ∈ ggQ2xQ_isConjRefl D,
      π (s * t * s⁻¹) = π s * π t * (π s)⁻¹) :
    ∃ g ∈ D.weyl, ∀ t ∈ ggQ2xQ_isConjRefl D, π t = g * t * g⁻¹ := by
  classical
  have hE' : ggQ2xQ_IsE D := hE
  obtain ⟨g, hgweyl, hgk⟩ := ggQ2xQ_frame D hbas hE' π hπT hinj hπ
  refine ⟨g, hgweyl, ?_⟩
  have hS : Set.range D.simpleRefl ⊆ ggQ2xQ_isConjRefl D := fun t ht => by
    obtain ⟨k, rfl⟩ := ht
    exact ⟨k, 1, Subgroup.one_mem _, by simp⟩
  have hTc : ∀ w ∈ Subgroup.closure (Set.range D.simpleRefl),
      ∀ s ∈ Set.range D.simpleRefl, w * s * w⁻¹ ∈ ggQ2xQ_isConjRefl D := by
    intro w hw s hs
    obtain ⟨k, rfl⟩ := hs
    exact ⟨k, w, (ggQ2xQ_mem_weyl_iff D).2 hw, rfl⟩
  have hinv : ∀ s ∈ Set.range D.simpleRefl, s⁻¹ = s := by
    rintro s ⟨k, rfl⟩
    exact ggQ2xQ_inv_simpleRefl D k
  have hgk' : ∀ s ∈ Set.range D.simpleRefl, π s = g * s * g⁻¹ := by
    rintro s ⟨k, rfl⟩
    exact hgk k
  have hfinal := ggQ2xQ_quandle_eq_conj_of_gen (Set.range D.simpleRefl) (ggQ2xQ_isConjRefl D)
    hinv hS hTc π hπ g hgk'
  intro t ht
  obtain ⟨k, w, hw, rfl⟩ := ht
  exact hfinal w ((ggQ2xQ_mem_weyl_iff D).1 hw) (D.simpleRefl k) ⟨k, rfl⟩

end CFSG.StandardType

end
