module

public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.RepresentationTheory.Coinvariants
public import Mathlib.LinearAlgebra.Transvection.Basic
public import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.Quasithin.H13.NQTerm

open Module

section Transvections

variable {I : Type*} [AddCommGroup I] [Module (ZMod 2) I]

theorem zmod_two_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  fin_cases a
  · exact .inl rfl
  · exact .inr rfl

theorem add_self_eq_zero_of_zmod_two (x : I) : x + x = 0 := by
  rw [← two_smul (ZMod 2) x, show (2 : ZMod 2) = 0 from rfl, zero_smul]

theorem transvection_comp_self {u : I} {g : Module.Dual (ZMod 2) I} (hgu : g u = 0) :
    LinearMap.transvection g u ∘ₗ LinearMap.transvection g u = LinearMap.id := by
  rw [LinearMap.transvection.comp_of_left_eq hgu, add_self_eq_zero_of_zmod_two,
    LinearMap.transvection.of_right_eq_zero]

@[expose] def tvGL (u : I) (g : Module.Dual (ZMod 2) I) (hgu : g u = 0) :
    LinearMap.GeneralLinearGroup (ZMod 2) I :=
  ⟨LinearMap.transvection g u, LinearMap.transvection g u, transvection_comp_self hgu,
    transvection_comp_self hgu⟩

theorem tvGL_apply {u : I} {g : Module.Dual (ZMod 2) I} (hgu : g u = 0) (x : I) :
    (tvGL u g hgu : I →ₗ[ZMod 2] I) x = x + g x • u :=
  rfl

theorem tvGL_mul_self {u : I} {g : Module.Dual (ZMod 2) I} (hgu : g u = 0) :
    tvGL u g hgu * tvGL u g hgu = 1 :=
  Units.ext (transvection_comp_self hgu)

theorem tvGL_inv {u : I} {g : Module.Dual (ZMod 2) I} (hgu : g u = 0) :
    (tvGL u g hgu)⁻¹ = tvGL u g hgu :=
  inv_eq_of_mul_eq_one_right (tvGL_mul_self hgu)

theorem tvGL_mul_axis {u w : I} {g : Module.Dual (ZMod 2) I} (hu : g u = 0) (hw : g w = 0) :
    tvGL u g hu * tvGL w g hw = tvGL (u + w) g (by rw [map_add, hu, hw, add_zero]) :=
  Units.ext (LinearMap.transvection.comp_of_left_eq hw)

theorem tvGL_mul_center {u : I} {g h : Module.Dual (ZMod 2) I} (hg : g u = 0) (hh : h u = 0) :
    tvGL u g hg * tvGL u h hh = tvGL u (g + h) (by rw [LinearMap.add_apply, hg, hh, add_zero]) :=
  Units.ext (LinearMap.transvection.comp_of_right_eq hg)

theorem tvGL_zero_left (u : I) : tvGL u 0 (LinearMap.zero_apply u) = 1 :=
  Units.ext (LinearMap.transvection.of_left_eq_zero u)

theorem tvGL_zero_right (g : Module.Dual (ZMod 2) I) : tvGL 0 g (map_zero g) = 1 :=
  Units.ext (LinearMap.transvection.of_right_eq_zero g)

theorem apply_inv_apply (y : LinearMap.GeneralLinearGroup (ZMod 2) I) (x : I) :
    (y : I →ₗ[ZMod 2] I) (((y⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) I) :
      I →ₗ[ZMod 2] I) x) = x := by
  rw [← Module.End.mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    Module.End.one_apply]

theorem conj_tvGL (y : LinearMap.GeneralLinearGroup (ZMod 2) I) {u : I}
    {g g' : Module.Dual (ZMod 2) I} (hgu : g u = 0)
    (hg' : ∀ x, g' ((y : I →ₗ[ZMod 2] I) x) = g x) :
    y * tvGL u g hgu * y⁻¹ = tvGL ((y : I →ₗ[ZMod 2] I) u) g' (by rw [hg', hgu]) := by
  apply Units.ext
  apply LinearMap.ext
  intro x
  change (y : I →ₗ[ZMod 2] I) ((tvGL u g hgu : I →ₗ[ZMod 2] I)
    (((y⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) I) : I →ₗ[ZMod 2] I) x)) =
      x + g' x • (y : I →ₗ[ZMod 2] I) u
  rw [tvGL_apply, map_add, map_smul, apply_inv_apply, ← hg', apply_inv_apply]

@[expose] def axisGroup (f : Module.Dual (ZMod 2) I) :
    Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) I) where
  carrier := {a | ∃ (u : I) (hu : f u = 0), a = tvGL u f hu}
  one_mem' := ⟨0, map_zero f, (tvGL_zero_right f).symm⟩
  mul_mem' := by
    rintro _ _ ⟨u, hu, rfl⟩ ⟨w, hw, rfl⟩
    exact ⟨u + w, _, tvGL_mul_axis hu hw⟩
  inv_mem' := by
    rintro _ ⟨u, hu, rfl⟩
    exact ⟨u, hu, tvGL_inv hu⟩

theorem tvGL_mem_axisGroup {u : I} {f : Module.Dual (ZMod 2) I} (hu : f u = 0) :
    tvGL u f hu ∈ axisGroup f :=
  ⟨u, hu, rfl⟩

theorem exists_eq_one_of_ne_zero {g : Module.Dual (ZMod 2) I} (hg : g ≠ 0) : ∃ x, g x = 1 := by
  obtain ⟨x, hx⟩ : ∃ x, g x ≠ 0 := by
    by_contra h
    push Not at h
    exact hg (LinearMap.ext h)
  exact ⟨x, (zmod_two_cases (g x)).resolve_left hx⟩

theorem finrank_ker_add_one [FiniteDimensional (ZMod 2) I] {g : Module.Dual (ZMod 2) I}
    (hg : g ≠ 0) : finrank (ZMod 2) (LinearMap.ker g) + 1 = finrank (ZMod 2) I := by
  have h := LinearMap.finrank_range_add_finrank_ker g
  have hr : LinearMap.range g = ⊤ := by
    obtain ⟨x, hx⟩ := exists_eq_one_of_ne_zero hg
    exact LinearMap.range_eq_top.mpr fun c => ⟨c • x, by rw [map_smul, hx, smul_eq_mul, mul_one]⟩
  rw [hr, finrank_top, Module.finrank_self] at h
  omega

theorem exists_eq_one_eq_zero {g h : Module.Dual (ZMod 2) I} (hg : g ≠ 0) (hgh : g ≠ h) :
    ∃ x, g x = 1 ∧ h x = 0 := by
  obtain ⟨x, hx⟩ : ∃ x, g x ≠ h x := by
    by_contra hc
    push Not at hc
    exact hgh (LinearMap.ext hc)
  rcases zmod_two_cases (g x) with h1 | h1 <;> rcases zmod_two_cases (h x) with h2 | h2
  · exact absurd (h1.trans h2.symm) hx
  · obtain ⟨z, hz⟩ := exists_eq_one_of_ne_zero hg
    rcases zmod_two_cases (h z) with h3 | h3
    · exact ⟨z, hz, h3⟩
    · refine ⟨z + x, by rw [map_add, hz, h1, add_zero], ?_⟩
      rw [map_add, h3, h2]
      rfl
  · exact ⟨x, h1, h2⟩
  · exact absurd (h1.trans h2.symm) hx

theorem exists_gl_transport [FiniteDimensional (ZMod 2) I] {f f' : Module.Dual (ZMod 2) I}
    (hf : f ≠ 0) (hf' : f' ≠ 0) :
    ∃ y : LinearMap.GeneralLinearGroup (ZMod 2) I, ∀ x, f' ((y : I →ₗ[ZMod 2] I) x) = f x := by
  obtain ⟨x₀, hx₀⟩ := exists_eq_one_of_ne_zero hf
  obtain ⟨x₁, hx₁⟩ := exists_eq_one_of_ne_zero hf'
  have hk : finrank (ZMod 2) (LinearMap.ker f) = finrank (ZMod 2) (LinearMap.ker f') := by
    have h1 := finrank_ker_add_one hf
    have h2 := finrank_ker_add_one hf'
    omega
  let e := LinearEquiv.ofFinrankEq (LinearMap.ker f) (LinearMap.ker f') hk
  let P : I →ₗ[ZMod 2] LinearMap.ker f :=
    LinearMap.codRestrict _ (LinearMap.id - f.smulRight x₀) fun x => by
      rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smulRight_apply,
        map_sub, map_smul, hx₀, smul_eq_mul, mul_one, sub_self]
  let P' : I →ₗ[ZMod 2] LinearMap.ker f' :=
    LinearMap.codRestrict _ (LinearMap.id - f'.smulRight x₁) fun x => by
      rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smulRight_apply,
        map_sub, map_smul, hx₁, smul_eq_mul, mul_one, sub_self]
  let yL : I →ₗ[ZMod 2] I :=
    (LinearMap.ker f').subtype ∘ₗ e.toLinearMap ∘ₗ P + f.smulRight x₁
  let yL' : I →ₗ[ZMod 2] I :=
    (LinearMap.ker f).subtype ∘ₗ e.symm.toLinearMap ∘ₗ P' + f'.smulRight x₀
  have hP : ∀ x, (P x : I) = x - f x • x₀ := fun x => rfl
  have hP' : ∀ x, (P' x : I) = x - f' x • x₁ := fun x => rfl
  have hyL : ∀ x, yL x = (e (P x) : I) + f x • x₁ := fun x => rfl
  have hyL' : ∀ x, yL' x = (e.symm (P' x) : I) + f' x • x₀ := fun x => rfl
  have hf'yL : ∀ x, f' (yL x) = f x := by
    intro x
    rw [hyL, map_add, map_smul, hx₁, smul_eq_mul, mul_one,
      LinearMap.mem_ker.mp (e (P x)).2, zero_add]
  have hfyL' : ∀ x, f (yL' x) = f' x := by
    intro x
    rw [hyL', map_add, map_smul, hx₀, smul_eq_mul, mul_one,
      LinearMap.mem_ker.mp (e.symm (P' x)).2, zero_add]
  have hPyL' : ∀ x, P (yL' x) = e.symm (P' x) := by
    intro x
    apply Subtype.ext
    rw [hP, hfyL', hyL', add_sub_cancel_right]
  have hP'yL : ∀ x, P' (yL x) = e (P x) := by
    intro x
    apply Subtype.ext
    rw [hP', hf'yL, hyL, add_sub_cancel_right]
  have h1 : yL * yL' = 1 := by
    apply LinearMap.ext
    intro x
    change yL (yL' x) = x
    rw [hyL, hPyL', LinearEquiv.apply_symm_apply, hfyL', hP', sub_add_cancel]
  have h2 : yL' * yL = 1 := by
    apply LinearMap.ext
    intro x
    change yL' (yL x) = x
    rw [hyL', hP'yL, LinearEquiv.symm_apply_apply, hf'yL, hP, sub_add_cancel]
  exact ⟨⟨yL, yL', h1, h2⟩, hf'yL⟩

theorem mem_closure_transvections [FiniteDimensional (ZMod 2) I]
    (hI : finrank (ZMod 2) I = 3) (y : LinearMap.GeneralLinearGroup (ZMod 2) I) :
    y ∈ Subgroup.closure {t | ∃ (u : I) (g : Module.Dual (ZMod 2) I) (h : g u = 0),
      t = tvGL u g h} := by
  classical
  set S := Subgroup.closure {t : LinearMap.GeneralLinearGroup (ZMod 2) I |
    ∃ (u : I) (g : Module.Dual (ZMod 2) I) (h : g u = 0), t = tvGL u g h} with hSdef
  let b := Module.finBasisOfFinrankEq (ZMod 2) I hI
  let φ := LinearMap.toMatrixAlgEquiv b
  let P : Matrix (Fin 3) (Fin 3) (ZMod 2) → Prop := fun N =>
    ∀ z : LinearMap.GeneralLinearGroup (ZMod 2) I, φ (z : I →ₗ[ZMod 2] I) = N → z ∈ S
  have hdet : (φ (y : I →ₗ[ZMod 2] I)).det ≠ 0 := by
    have h1 : φ (y : I →ₗ[ZMod 2] I) *
        φ ((y⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) I) : I →ₗ[ZMod 2] I) = 1 := by
      rw [← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one]
    intro h0
    have h2 := congrArg Matrix.det h1
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at h2
    exact zero_ne_one h2
  have hmk : ∀ N : Matrix (Fin 3) (Fin 3) (ZMod 2), N.det ≠ 0 →
      ∃ z : LinearMap.GeneralLinearGroup (ZMod 2) I, φ (z : I →ₗ[ZMod 2] I) = N := by
    intro N hN
    have hu : IsUnit N.det := isUnit_iff_ne_zero.mpr hN
    refine ⟨⟨φ.symm N, φ.symm N⁻¹, ?_, ?_⟩, φ.apply_symm_apply N⟩
    · rw [← map_mul, Matrix.mul_nonsing_inv N hu, map_one]
    · rw [← map_mul, Matrix.nonsing_inv_mul N hu, map_one]
  refine Matrix.diagonal_transvection_induction_of_det_ne_zero P (φ (y : I →ₗ[ZMod 2] I)) hdet
    ?_ ?_ ?_ y rfl
  · intro D hD z hz
    have hD1 : ∀ i, D i = 1 := by
      intro i
      refine (zmod_two_cases (D i)).resolve_left fun h0 => hD ?_
      rw [Matrix.det_diagonal]
      exact Finset.prod_eq_zero (Finset.mem_univ i) h0
    have hD1' : Matrix.diagonal D = 1 := by
      ext i j
      by_cases hij : i = j
      · subst hij
        rw [Matrix.diagonal_apply_eq, Matrix.one_apply_eq, hD1]
      · rw [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
    have hz1 : z = 1 := by
      apply Units.ext
      apply φ.injective
      rw [hz, hD1', Units.val_one, map_one]
    rw [hz1]
    exact one_mem S
  · intro t z hz
    have hgu : (t.c • b.coord t.j) (b t.i) = 0 := by
      simp [Basis.coord_apply, Basis.repr_self, t.hij]
    have hzt : z = tvGL (b t.i) (t.c • b.coord t.j) hgu := by
      apply Units.ext
      apply φ.injective
      rw [hz]
      ext k l
      have hij := t.hij
      rw [LinearMap.toMatrixAlgEquiv_apply, tvGL_apply, map_add, map_smul, LinearMap.smul_apply,
        Basis.coord_apply, Basis.repr_self, Basis.repr_self, Finsupp.add_apply,
        Finsupp.smul_apply, Matrix.TransvectionStruct.toMatrix, Matrix.transvection,
        Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
      simp only [Finsupp.single_apply, smul_eq_mul]
      revert hij
      generalize t.i = i
      generalize t.j = j
      generalize t.c = c
      revert i j c k l
      decide
    exact Subgroup.subset_closure ⟨_, _, hgu, hzt⟩
  · intro A B hA hB PA PB z hz
    obtain ⟨zA, hzA⟩ := hmk A hA
    obtain ⟨zB, hzB⟩ := hmk B hB
    have hzAB : z = zA * zB :=
      Units.ext (φ.injective (by rw [hz, Units.val_mul, map_mul, hzA, hzB]))
    rw [hzAB]
    exact mul_mem (PA zA hzA) (PB zB hzB)

end Transvections

structure SatData (I D : Type*) [AddCommGroup I] [Module (ZMod 2) I] [AddCommGroup D]
    [Module (ZMod 2) D] where
  ρ : Representation (ZMod 2) (LinearMap.GeneralLinearGroup (ZMod 2) I) D
  D₀ : Submodule (ZMod 2) D
  D₁ : Submodule (ZMod 2) D
  le : D₀ ≤ D₁
  inv₁ : ∀ y, ∀ d ∈ D₁, ρ y d ∈ D₁
  r : ℕ
  π : D₁ →ₗ[ZMod 2] (Fin r → I)
  surj : Function.Surjective π
  ker : ∀ d : D₁, π d = 0 ↔ (d : D) ∈ D₀
  equiv : ∀ y (d : D₁), π ⟨ρ y d, inv₁ y d d.2⟩ = fun i => (y : I →ₗ[ZMod 2] I) (π d i)

namespace SatData

variable {I D : Type*} [AddCommGroup I] [Module (ZMod 2) I] [AddCommGroup D] [Module (ZMod 2) D]
  (S : SatData I D)

@[expose] noncomputable def codim (A : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) I)) : ℕ :=
  finrank (ZMod 2) D - finrank (ZMod 2) (Representation.invariants (S.ρ.comp A.subtype))

@[expose] def U (t : LinearMap.GeneralLinearGroup (ZMod 2) I) : Submodule (ZMod 2) D :=
  LinearMap.range (S.ρ t - LinearMap.id)

theorem mem_invariants_comp {A : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) I)} {d : D} :
    d ∈ (Representation.invariants (S.ρ.comp A.subtype)) ↔ ∀ a ∈ A, S.ρ a d = d :=
  ⟨fun h a ha => h ⟨a, ha⟩, fun h a => h a a.2⟩

theorem finrank_pi_fin {r : ℕ} [FiniteDimensional (ZMod 2) I] :
    finrank (ZMod 2) (Fin r → I) = r * finrank (ZMod 2) I := by
  rw [Module.finrank_pi_fintype]
  simp

variable [FiniteDimensional (ZMod 2) I] [FiniteDimensional (ZMod 2) D]

omit [FiniteDimensional (ZMod 2) I] in
theorem finrank_invariants_le {f g : Module.Dual (ZMod 2) I}
    (y : LinearMap.GeneralLinearGroup (ZMod 2) I) (hy : ∀ x, g ((y : I →ₗ[ZMod 2] I) x) = f x) :
    finrank (ZMod 2) (Representation.invariants (S.ρ.comp (axisGroup f).subtype)) ≤
      finrank (ZMod 2) (Representation.invariants (S.ρ.comp (axisGroup g).subtype)) := by
  have hy' : ∀ x, f (((y⁻¹ : LinearMap.GeneralLinearGroup (ZMod 2) I) : I →ₗ[ZMod 2] I) x) =
      g x := fun x => by rw [← hy, apply_inv_apply]
  have hmap : (Representation.invariants (S.ρ.comp (axisGroup f).subtype)).map (S.ρ y) ≤
      (Representation.invariants (S.ρ.comp (axisGroup g).subtype)) := by
    rintro _ ⟨d, hd0, rfl⟩
    have hd := S.mem_invariants_comp.mp hd0
    apply S.mem_invariants_comp.mpr
    rintro _ ⟨w, hw, rfl⟩
    have hconj := conj_tvGL y⁻¹ hw hy'
    rw [inv_inv] at hconj
    have h2 : S.ρ (y⁻¹ * tvGL w g hw * y) d = d := hd _ (by rw [hconj]; exact ⟨_, _, rfl⟩)
    calc S.ρ (tvGL w g hw) (S.ρ y d)
        = S.ρ (tvGL w g hw * y) d := by rw [map_mul, Module.End.mul_apply]
      _ = S.ρ (y * (y⁻¹ * tvGL w g hw * y)) d := by congr 2; group
      _ = S.ρ y d := by rw [map_mul, Module.End.mul_apply, h2]
  have hinj : Function.Injective (S.ρ y) := by
    intro a b hab
    have := congrArg (S.ρ y⁻¹) hab
    rwa [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply, Module.End.one_apply] at this
  calc finrank (ZMod 2) (Representation.invariants (S.ρ.comp (axisGroup f).subtype))
      = finrank (ZMod 2)
          ((Representation.invariants (S.ρ.comp (axisGroup f).subtype)).map (S.ρ y)) :=
        (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hinj _))
    _ ≤ _ := Submodule.finrank_mono hmap

theorem codim_eq_of_codim_eq {f g : Module.Dual (ZMod 2) I} (hf : f ≠ 0) (hg : g ≠ 0)
    (hc : S.codim (axisGroup f) = S.r) : S.codim (axisGroup g) = S.r := by
  obtain ⟨y, hy⟩ := exists_gl_transport hf hg
  obtain ⟨y', hy'⟩ := exists_gl_transport hg hf
  have h1 := S.finrank_invariants_le y hy
  have h2 := S.finrank_invariants_le y' hy'
  unfold codim at hc ⊢
  omega

theorem axis_facts (hI : finrank (ZMod 2) I = 3) {f : Module.Dual (ZMod 2) I} (hf : f ≠ 0)
    (hc : S.codim (axisGroup f) = S.r) :
    (∀ a ∈ axisGroup f, ∀ d ∈ S.D₀, S.ρ a d = d) ∧
      (∀ a ∈ axisGroup f, ∀ d, S.ρ a d - d ∈ S.D₁) := by
  classical
  set C := (Representation.invariants (S.ρ.comp (axisGroup f).subtype)) with hCdef
  obtain ⟨u, hu, hu0⟩ : ∃ u ∈ LinearMap.ker f, u ≠ 0 := by
    apply Submodule.exists_mem_ne_zero_of_ne_bot
    intro hbot
    have h := finrank_ker_add_one hf
    rw [hbot, finrank_bot] at h
    omega
  rw [LinearMap.mem_ker] at hu
  obtain ⟨x₀, hx₀⟩ := exists_eq_one_of_ne_zero hf
  let Φ : (Fin S.r → I) →ₗ[ZMod 2] (Fin S.r → ZMod 2) :=
    LinearMap.pi fun i => f ∘ₗ LinearMap.proj i
  have hΦ : ∀ z i, Φ z i = f (z i) := fun _ _ => rfl
  let ψ := Φ ∘ₗ S.π
  have hψs : Function.Surjective ψ := by
    intro c
    obtain ⟨d, hd⟩ := S.surj fun i => c i • x₀
    refine ⟨d, funext fun i => ?_⟩
    change Φ (S.π d) i = c i
    rw [hΦ, hd, map_smul, hx₀, smul_eq_mul, mul_one]
  have hkerψ : finrank (ZMod 2) (LinearMap.ker ψ) + S.r = finrank (ZMod 2) S.D₁ := by
    have h := LinearMap.finrank_range_add_finrank_ker ψ
    rw [LinearMap.range_eq_top.mpr hψs, finrank_top, Module.finrank_fin_fun] at h
    omega
  set C₁ := C.comap S.D₁.subtype with hC₁
  set D₀' := S.D₀.comap S.D₁.subtype with hD₀'
  have hC₁ψ : C₁ ≤ LinearMap.ker ψ := by
    intro d hd
    rw [LinearMap.mem_ker]
    funext i
    change f (S.π d i) = 0
    have hdC : (d : D) ∈ C := hd
    have hd' : S.ρ (tvGL u f hu) d = d :=
      (S.mem_invariants_comp.mp hdC) _ (tvGL_mem_axisGroup hu)
    have h1 := S.equiv (tvGL u f hu) d
    have h2 : (⟨S.ρ (tvGL u f hu) d, S.inv₁ _ d d.2⟩ : S.D₁) = d := Subtype.ext hd'
    rw [h2] at h1
    have h3 := congrFun h1 i
    rw [tvGL_apply] at h3
    have h4 : f (S.π d i) • u = 0 := by
      have h5 := congrArg (fun z => z - S.π d i) h3
      simp only [sub_self, add_sub_cancel_left] at h5
      exact h5.symm
    exact (smul_eq_zero.mp h4).resolve_right hu0
  have hD₀ψ : D₀' ≤ LinearMap.ker ψ := by
    intro d hd
    rw [LinearMap.mem_ker]
    change Φ (S.π d) = 0
    rw [(S.ker d).mpr hd, map_zero]
  have hD₀'f : finrank (ZMod 2) D₀' = finrank (ZMod 2) S.D₀ :=
    (Submodule.comapSubtypeEquivOfLe S.le).finrank_eq
  have hπk : LinearMap.ker S.π = D₀' := by
    ext d
    rw [LinearMap.mem_ker]
    exact S.ker d
  have hD₁f : finrank (ZMod 2) S.D₁ = finrank (ZMod 2) S.D₀ + S.r * finrank (ZMod 2) I := by
    have h := LinearMap.finrank_range_add_finrank_ker S.π
    rw [LinearMap.range_eq_top.mpr S.surj, finrank_top, hπk, hD₀'f, finrank_pi_fin] at h
    omega
  have hC₁f : finrank (ZMod 2) C₁ = finrank (ZMod 2) ↥(C ⊓ S.D₁) := by
    have h1 : C₁ = (C ⊓ S.D₁).comap S.D₁.subtype := by
      rw [Submodule.comap_inf, Submodule.comap_subtype_self, inf_top_eq]
    rw [h1]
    exact (Submodule.comapSubtypeEquivOfLe inf_le_right).finrank_eq
  have hsup1 := Submodule.finrank_sup_add_finrank_inf_eq C₁ D₀'
  have hsup2 := Submodule.finrank_sup_add_finrank_inf_eq C S.D₁
  have hle1 : finrank (ZMod 2) ↥(C₁ ⊔ D₀') ≤ finrank (ZMod 2) (LinearMap.ker ψ) :=
    Submodule.finrank_mono (sup_le hC₁ψ hD₀ψ)
  have hle2 : finrank (ZMod 2) ↥(C ⊔ S.D₁) ≤ finrank (ZMod 2) D := Submodule.finrank_le _
  have hle3 : finrank (ZMod 2) ↥(C₁ ⊓ D₀') ≤ finrank (ZMod 2) D₀' :=
    Submodule.finrank_mono inf_le_right
  have hCle : finrank (ZMod 2) C ≤ finrank (ZMod 2) D := Submodule.finrank_le _
  have hcod : finrank (ZMod 2) D - finrank (ZMod 2) C = S.r := hc
  have heq3 : finrank (ZMod 2) ↥(C₁ ⊓ D₀') = finrank (ZMod 2) D₀' := by omega
  have heq2 : finrank (ZMod 2) ↥(C ⊔ S.D₁) = finrank (ZMod 2) D := by omega
  have hD₀C : D₀' ≤ C₁ := by
    have h := Submodule.eq_of_le_of_finrank_eq inf_le_right heq3
    rw [← h]
    exact inf_le_left
  have htop : C ⊔ S.D₁ = ⊤ := Submodule.eq_top_of_finrank_eq heq2
  refine ⟨fun a ha d hd => ?_, fun a ha d => ?_⟩
  · have h1 : (⟨d, S.le hd⟩ : S.D₁) ∈ C₁ := hD₀C (show (⟨d, S.le hd⟩ : S.D₁) ∈ D₀' from hd)
    exact S.mem_invariants_comp.mp h1 a ha
  · have hd : d ∈ C ⊔ S.D₁ := by
      rw [htop]
      exact Submodule.mem_top
    obtain ⟨c, hc, d₁, hd₁, rfl⟩ := Submodule.mem_sup.mp hd
    rw [map_add, S.mem_invariants_comp.mp hc a ha,
      show c + S.ρ a d₁ - (c + d₁) = S.ρ a d₁ - d₁ by abel]
    exact S.D₁.sub_mem (S.inv₁ a d₁ hd₁) hd₁

theorem tv_facts (hI : finrank (ZMod 2) I = 3) {f : Module.Dual (ZMod 2) I} (hf : f ≠ 0)
    (hc : S.codim (axisGroup f) = S.r) {u : I} (hu : f u = 0) (hu0 : u ≠ 0) :
    ∃ hT1 : ∀ d, S.ρ (tvGL u f hu) d - d ∈ S.D₁,
      finrank (ZMod 2) (S.U (tvGL u f hu)) = S.r ∧
      (∀ e : S.D₁, S.π ⟨S.ρ (tvGL u f hu) e - e, hT1 e⟩ = fun i => f (S.π e i) • u) ∧
      (∀ d d', S.π ⟨_, hT1 d⟩ = S.π ⟨_, hT1 d'⟩ →
        S.ρ (tvGL u f hu) d - d = S.ρ (tvGL u f hu) d' - d') ∧
      (∀ d, ∃ c : Fin S.r → ZMod 2, S.π ⟨_, hT1 d⟩ = fun i => c i • u) := by
  classical
  obtain ⟨-, hii⟩ := S.axis_facts hI hf hc
  set t := tvGL u f hu with ht
  set T := S.ρ t - LinearMap.id with hT
  have hTd : ∀ d, T d = S.ρ t d - d := fun _ => rfl
  have hT1 : ∀ d, S.ρ t d - d ∈ S.D₁ := fun d => hii t (tvGL_mem_axisGroup hu) d
  obtain ⟨x₀, hx₀⟩ := exists_eq_one_of_ne_zero hf
  have hπT : ∀ e : S.D₁, S.π ⟨S.ρ t e - e, hT1 e⟩ = fun i => f (S.π e i) • u := by
    intro e
    have h2 : (⟨S.ρ t e - e, hT1 e⟩ : S.D₁) = ⟨S.ρ t e, S.inv₁ t e e.2⟩ - e := rfl
    rw [h2, map_sub, S.equiv t e]
    funext i
    simp only [Pi.sub_apply, ht, tvGL_apply, add_sub_cancel_left]
  set C := (Representation.invariants (S.ρ.comp (axisGroup f).subtype)) with hCdef
  have hCker : C ≤ LinearMap.ker T := fun d hd => by
    rw [LinearMap.mem_ker, hTd, S.mem_invariants_comp.mp hd t (tvGL_mem_axisGroup hu), sub_self]
  have hcod : finrank (ZMod 2) D - finrank (ZMod 2) C = S.r := hc
  have hCle : finrank (ZMod 2) C ≤ finrank (ZMod 2) D := Submodule.finrank_le _
  let T' : D →ₗ[ZMod 2] S.D₁ := LinearMap.codRestrict S.D₁ T hT1
  have hT'r : finrank (ZMod 2) (LinearMap.range T') ≤ S.r := by
    have h := LinearMap.finrank_range_add_finrank_ker T'
    rw [LinearMap.ker_codRestrict] at h
    have h2 := Submodule.finrank_mono hCker
    omega
  have hTr : finrank (ZMod 2) (S.U t) = finrank (ZMod 2) (LinearMap.range T') := by
    have h := LinearMap.finrank_range_add_finrank_ker T'
    have h' := LinearMap.finrank_range_add_finrank_ker T
    rw [LinearMap.ker_codRestrict] at h
    change finrank (ZMod 2) (LinearMap.range T) = _
    omega
  let κ : (Fin S.r → ZMod 2) →ₗ[ZMod 2] (Fin S.r → I) :=
    LinearMap.pi fun i => (LinearMap.proj i).smulRight u
  have hκ : ∀ c i, κ c i = c i • u := fun _ _ => rfl
  have hκinj : Function.Injective κ := by
    intro c c' h
    funext i
    have h1 := congrFun h i
    rw [hκ, hκ, ← sub_eq_zero, ← sub_smul] at h1
    exact sub_eq_zero.mp ((smul_eq_zero.mp h1).resolve_right hu0)
  have hκr : finrank (ZMod 2) (LinearMap.range κ) = S.r := by
    rw [LinearMap.finrank_range_of_inj hκinj, Module.finrank_fin_fun]
  have hκle : LinearMap.range κ ≤ (LinearMap.range T').map S.π := by
    rintro _ ⟨c, rfl⟩
    obtain ⟨e, he⟩ := S.surj fun i => c i • x₀
    refine ⟨T' e, ⟨e, rfl⟩, ?_⟩
    change S.π ⟨S.ρ t e - e, hT1 e⟩ = κ c
    rw [hπT, he]
    funext i
    simp only [map_smul, hx₀, smul_eq_mul, mul_one, hκ]
  have hmap : finrank (ZMod 2) ((LinearMap.range T').map S.π) ≤
      finrank (ZMod 2) (LinearMap.range T') := Submodule.finrank_map_le _ _
  have hκle' := Submodule.finrank_mono hκle
  have hrank : finrank (ZMod 2) (LinearMap.range T') = S.r := by omega
  have himage : (LinearMap.range T').map S.π = LinearMap.range κ :=
    (Submodule.eq_of_le_of_finrank_eq hκle (by omega)).symm
  have hker : LinearMap.ker (S.π.domRestrict (LinearMap.range T')) = ⊥ := by
    have h := LinearMap.finrank_range_add_finrank_ker (S.π.domRestrict (LinearMap.range T'))
    rw [LinearMap.range_domRestrict] at h
    exact Submodule.finrank_eq_zero.mp (by omega)
  refine ⟨hT1, by rw [hTr, hrank], hπT, fun d d' hdd' => ?_, fun d => ?_⟩
  · have h1 : T' (d - d') ∈ LinearMap.range T' := ⟨_, rfl⟩
    have h2 : S.π.domRestrict (LinearMap.range T') ⟨T' (d - d'), h1⟩ = 0 := by
      change S.π (T' (d - d')) = 0
      rw [map_sub, map_sub]
      exact sub_eq_zero.mpr hdd'
    rw [← LinearMap.mem_ker, hker, Submodule.mem_bot] at h2
    have h3 := congrArg (fun x : LinearMap.range T' => ((x : S.D₁) : D)) h2
    change T (d - d') = 0 at h3
    rw [map_sub, hTd, hTd] at h3
    exact sub_eq_zero.mp h3
  · have h1 : S.π (T' d) ∈ (LinearMap.range T').map S.π := ⟨T' d, ⟨d, rfl⟩, rfl⟩
    rw [himage] at h1
    obtain ⟨c, hc⟩ := h1
    exact ⟨c, hc.symm⟩

theorem U_le_U_add (hI : finrank (ZMod 2) I = 3)
    (hcod : ∀ g : Module.Dual (ZMod 2) I, g ≠ 0 → S.codim (axisGroup g) = S.r)
    {u : I} (hu0 : u ≠ 0) {g h : Module.Dual (ZMod 2) I} (hg : g ≠ 0) (hh : h ≠ 0)
    (hgh : g ≠ h) (hgu : g u = 0) (hhu : h u = 0) :
    S.U (tvGL u g hgu) ≤
      S.U (tvGL u (g + h) (by rw [LinearMap.add_apply, hgu, hhu, add_zero])) := by
  obtain ⟨hTa, -, hπa, hinja, himga⟩ := S.tv_facts hI hg (hcod g hg) hgu hu0
  obtain ⟨hTb, -, hπb, hinjb, -⟩ := S.tv_facts hI hh (hcod h hh) hhu hu0
  rintro _ ⟨d, rfl⟩
  obtain ⟨γ, hγ⟩ := himga d
  obtain ⟨x₁, hx₁g, hx₁h⟩ := exists_eq_one_eq_zero hg hgh
  obtain ⟨w, hw⟩ := S.surj fun i => γ i • x₁
  have h1 : S.ρ (tvGL u g hgu) w - w = S.ρ (tvGL u g hgu) d - d := by
    apply hinja
    rw [hπa w, hγ, hw]
    funext i
    simp [hx₁g]
  have h2 : S.ρ (tvGL u h hhu) w - w = 0 := by
    have h3 : S.π ⟨_, hTb (w : D)⟩ = S.π ⟨_, hTb 0⟩ := by
      have h4 : (⟨S.ρ (tvGL u h hhu) 0 - 0, hTb 0⟩ : S.D₁) = 0 := Subtype.ext (by simp)
      rw [h4, map_zero, hπb w, hw]
      funext i
      simp [hx₁h]
    have h5 := hinjb (w : D) 0 h3
    rwa [map_zero, sub_zero] at h5
  refine ⟨w, ?_⟩
  show S.ρ (tvGL u (g + h) _) w - w = S.ρ (tvGL u g hgu) d - d
  rw [← tvGL_mul_center hgu hhu, map_mul, Module.End.mul_apply, sub_eq_zero.mp h2, h1]

theorem U_eq_of_center (hI : finrank (ZMod 2) I = 3)
    (hcod : ∀ g : Module.Dual (ZMod 2) I, g ≠ 0 → S.codim (axisGroup g) = S.r)
    {u : I} (hu0 : u ≠ 0) {g h : Module.Dual (ZMod 2) I} (hg : g ≠ 0) (hh : h ≠ 0)
    (hgu : g u = 0) (hhu : h u = 0) : S.U (tvGL u g hgu) = S.U (tvGL u h hhu) := by
  by_cases hgh : g = h
  · subst hgh
    rfl
  · have hgh' : g + h ≠ 0 := by
      intro h0
      apply hgh
      calc g = g + (h + h) := by rw [add_self_eq_zero_of_zmod_two, add_zero]
        _ = (g + h) + h := by abel
        _ = h := by rw [h0, zero_add]
    have hghu : (g + h) u = 0 := by rw [LinearMap.add_apply, hgu, hhu, add_zero]
    have h1 := S.U_le_U_add hI hcod hu0 hg hh hgh hgu hhu
    have h2 := S.U_le_U_add hI hcod hu0 hh hg (Ne.symm hgh) hhu hgu
    have hc : tvGL u (h + g) (by rw [LinearMap.add_apply, hhu, hgu, add_zero]) =
        tvGL u (g + h) hghu := by
      congr 1
      exact add_comm h g
    rw [hc] at h2
    obtain ⟨-, hra, -⟩ := S.tv_facts hI hg (hcod g hg) hgu hu0
    obtain ⟨-, hrb, -⟩ := S.tv_facts hI hh (hcod h hh) hhu hu0
    obtain ⟨-, hrc, -⟩ := S.tv_facts hI hgh' (hcod _ hgh') hghu hu0
    rw [Submodule.eq_of_le_of_finrank_eq h1 (by rw [hra, hrc]),
      Submodule.eq_of_le_of_finrank_eq h2 (by rw [hrb, hrc])]

theorem U_le_sup (hI : finrank (ZMod 2) I = 3)
    (hcod : ∀ g : Module.Dual (ZMod 2) I, g ≠ 0 → S.codim (axisGroup g) = S.r)
    {u₁ u₂ : I} (hu₁ : u₁ ≠ 0) (hu₂ : u₂ ≠ 0) {h : Module.Dual (ZMod 2) I} (hh : h ≠ 0)
    (h1 : h u₁ = 0) (h2 : h u₂ = 0) :
    S.U (tvGL (u₁ + u₂) h (by rw [map_add, h1, h2, add_zero])) ≤
      S.U (tvGL u₁ h h1) ⊔ S.U (tvGL u₂ h h2) := by
  obtain ⟨hTa, -, hπa, hinja, -⟩ := S.tv_facts hI hh (hcod h hh) h1 hu₁
  obtain ⟨hTb, -, -, -, himgb⟩ := S.tv_facts hI hh (hcod h hh) h2 hu₂
  rintro _ ⟨d, rfl⟩
  show S.ρ (tvGL (u₁ + u₂) h _) d - d ∈ _
  obtain ⟨γ, hγ⟩ := himgb d
  have hzero : S.ρ (tvGL u₁ h h1) (S.ρ (tvGL u₂ h h2) d - d) -
      (S.ρ (tvGL u₂ h h2) d - d) = 0 := by
    have h3 : S.π ⟨_, hTa (S.ρ (tvGL u₂ h h2) d - d)⟩ = S.π ⟨_, hTa 0⟩ := by
      have h4 : (⟨S.ρ (tvGL u₁ h h1) 0 - 0, hTa 0⟩ : S.D₁) = 0 := Subtype.ext (by simp)
      rw [h4, map_zero]
      have h5 : S.π ⟨_, hTa (S.ρ (tvGL u₂ h h2) d - d)⟩ =
          fun i => h (S.π ⟨S.ρ (tvGL u₂ h h2) d - d, hTb d⟩ i) • u₁ :=
        hπa ⟨S.ρ (tvGL u₂ h h2) d - d, hTb d⟩
      rw [h5, hγ]
      funext i
      simp [h2]
    have h5 := hinja _ 0 h3
    rwa [map_zero, sub_zero] at h5
  have h6 : S.ρ (tvGL u₁ h h1) (S.ρ (tvGL u₂ h h2) d) - S.ρ (tvGL u₁ h h1) d =
      S.ρ (tvGL u₂ h h2) d - d := by
    rw [← map_sub]
    exact sub_eq_zero.mp hzero
  have hc : S.ρ (tvGL (u₁ + u₂) h (by rw [map_add, h1, h2, add_zero])) d - d =
      (S.ρ (tvGL u₁ h h1) d - d) + (S.ρ (tvGL u₂ h h2) d - d) := by
    rw [← tvGL_mul_axis h1 h2, map_mul, Module.End.mul_apply]
    calc S.ρ (tvGL u₁ h h1) (S.ρ (tvGL u₂ h h2) d) - d =
        (S.ρ (tvGL u₁ h h1) (S.ρ (tvGL u₂ h h2) d) - S.ρ (tvGL u₁ h h1) d) +
          (S.ρ (tvGL u₁ h h1) d - d) := by abel
      _ = (S.ρ (tvGL u₂ h h2) d - d) + (S.ρ (tvGL u₁ h h1) d - d) := by rw [h6]
      _ = _ := by abel
  rw [hc]
  exact Submodule.add_mem_sup ⟨d, rfl⟩ ⟨d, rfl⟩

theorem exists_dual_vanishing (hI : finrank (ZMod 2) I = 3) (u₁ u₂ : I) :
    ∃ h : Module.Dual (ZMod 2) I, h ≠ 0 ∧ h u₁ = 0 ∧ h u₂ = 0 := by
  let Λ : Module.Dual (ZMod 2) I →ₗ[ZMod 2] (Fin 2 → ZMod 2) :=
    LinearMap.pi fun k => Module.Dual.eval (ZMod 2) I (![u₁, u₂] k)
  have h1 := LinearMap.finrank_range_add_finrank_ker Λ
  have h2 : finrank (ZMod 2) (LinearMap.range Λ) ≤ 2 := by
    have h := Submodule.finrank_le (LinearMap.range Λ)
    rwa [Module.finrank_fin_fun] at h
  have h3 : finrank (ZMod 2) (Module.Dual (ZMod 2) I) = 3 := by
    rw [Subspace.dual_finrank_eq, hI]
  have h4 : LinearMap.ker Λ ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot] at h1
    omega
  obtain ⟨h, hh, hh0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h4
  rw [LinearMap.mem_ker] at hh
  exact ⟨h, hh0, by simpa [Λ] using congrFun hh 0, by simpa [Λ] using congrFun hh 1⟩

theorem U_le_W (hI : finrank (ZMod 2) I = 3)
    (hcod : ∀ g : Module.Dual (ZMod 2) I, g ≠ 0 → S.codim (axisGroup g) = S.r)
    (b : Basis (Fin 3) (ZMod 2) I) {g₀ g₁ g₂ : Module.Dual (ZMod 2) I} (hg₀ : g₀ ≠ 0)
    (hg₁ : g₁ ≠ 0) (hg₂ : g₂ ≠ 0) (he₀ : g₀ (b 0) = 0) (he₁ : g₁ (b 1) = 0)
    (he₂ : g₂ (b 2) = 0) {u : I} (hu0 : u ≠ 0) {g : Module.Dual (ZMod 2) I} (hg : g ≠ 0)
    (hgu : g u = 0) :
    S.U (tvGL u g hgu) ≤
      S.U (tvGL (b 0) g₀ he₀) ⊔ S.U (tvGL (b 1) g₁ he₁) ⊔ S.U (tvGL (b 2) g₂ he₂) := by
  set W := S.U (tvGL (b 0) g₀ he₀) ⊔ S.U (tvGL (b 1) g₁ he₁) ⊔ S.U (tvGL (b 2) g₂ he₂)
    with hW
  have hP : ∀ v : I, v ≠ 0 → (∃ (g' : Module.Dual (ZMod 2) I) (_ : g' ≠ 0) (hg'v : g' v = 0),
      S.U (tvGL v g' hg'v) ≤ W) →
      ∀ g' : Module.Dual (ZMod 2) I, g' ≠ 0 → ∀ hgv : g' v = 0, S.U (tvGL v g' hgv) ≤ W := by
    rintro v hv ⟨g', hg', hg'v, hle⟩ g'' hg'' hg''v
    rw [S.U_eq_of_center hI hcod hv hg'' hg' hg''v hg'v]
    exact hle
  have hadd : ∀ v₁ v₂ : I, v₁ ≠ 0 → v₂ ≠ 0 → v₁ ≠ v₂ →
      (∀ g' : Module.Dual (ZMod 2) I, g' ≠ 0 → ∀ hgv : g' v₁ = 0, S.U (tvGL v₁ g' hgv) ≤ W) →
      (∀ g' : Module.Dual (ZMod 2) I, g' ≠ 0 → ∀ hgv : g' v₂ = 0, S.U (tvGL v₂ g' hgv) ≤ W) →
      ∀ g' : Module.Dual (ZMod 2) I, g' ≠ 0 → ∀ hgv : g' (v₁ + v₂) = 0,
        S.U (tvGL (v₁ + v₂) g' hgv) ≤ W := by
    intro v₁ v₂ hv₁ hv₂ hv₁₂ hP₁ hP₂
    have hv : v₁ + v₂ ≠ 0 := by
      intro h0
      apply hv₁₂
      calc v₁ = v₁ + (v₂ + v₂) := by rw [add_self_eq_zero_of_zmod_two, add_zero]
        _ = (v₁ + v₂) + v₂ := by abel
        _ = v₂ := by rw [h0, zero_add]
    apply hP _ hv
    obtain ⟨h, hh, hh₁, hh₂⟩ := exists_dual_vanishing hI v₁ v₂
    exact ⟨h, hh, by rw [map_add, hh₁, hh₂, add_zero],
      (S.U_le_sup hI hcod hv₁ hv₂ hh hh₁ hh₂).trans (sup_le (hP₁ h hh hh₁) (hP₂ h hh hh₂))⟩
  have hP0 := hP _ (b.ne_zero 0) ⟨g₀, hg₀, he₀, le_sup_left.trans le_sup_left⟩
  have hP1 := hP _ (b.ne_zero 1) ⟨g₁, hg₁, he₁, le_sup_right.trans le_sup_left⟩
  have hP2 := hP _ (b.ne_zero 2) ⟨g₂, hg₂, he₂, le_sup_right⟩
  have ne01 : b 0 + b 1 ≠ 0 := by
    intro h0
    have h1 := congrArg (fun v => b.repr v 0) h0
    simp at h1
  have ne012 : b 0 + b 1 ≠ b 2 := by
    intro h0
    have h1 := congrArg (fun v => b.repr v 2) h0
    simp at h1
  have hsum := b.sum_repr u
  rw [Fin.sum_univ_three] at hsum
  rcases zmod_two_cases (b.repr u 0) with c0 | c0 <;>
    rcases zmod_two_cases (b.repr u 1) with c1 | c1 <;>
    rcases zmod_two_cases (b.repr u 2) with c2 | c2 <;>
    rw [c0, c1, c2] at hsum <;> simp only [zero_smul, one_smul, zero_add, add_zero] at hsum <;>
    subst hsum
  · exact absurd rfl hu0
  · exact hP2 g hg hgu
  · exact hP1 g hg hgu
  · exact hadd _ _ (b.ne_zero 1) (b.ne_zero 2) (b.injective.ne (by decide)) hP1 hP2 g hg hgu
  · exact hP0 g hg hgu
  · exact hadd _ _ (b.ne_zero 0) (b.ne_zero 2) (b.injective.ne (by decide)) hP0 hP2 g hg hgu
  · exact hadd _ _ (b.ne_zero 0) (b.ne_zero 1) (b.injective.ne (by decide)) hP0 hP1 g hg hgu
  · exact hadd _ _ ne01 (b.ne_zero 2) ne012
      (hadd _ _ (b.ne_zero 0) (b.ne_zero 1) (b.injective.ne (by decide)) hP0 hP1) hP2 g hg hgu

end SatData

section Trivial

variable {G D : Type*} [Group G] [AddCommGroup D] [Module (ZMod 2) D]

@[expose] def trivOn (ρ : Representation (ZMod 2) G D) (W : Submodule (ZMod 2) D) :
    Subgroup G where
  carrier := {y | ∀ d, ρ y d - d ∈ W}
  one_mem' d := by
    rw [map_one, Module.End.one_apply, sub_self]
    exact W.zero_mem
  mul_mem' {a b} ha hb d := by
    rw [map_mul, Module.End.mul_apply,
      show ρ a (ρ b d) - d = (ρ a (ρ b d) - ρ b d) + (ρ b d - d) by abel]
    exact W.add_mem (ha _) (hb d)
  inv_mem' {a} ha d := by
    have h1 := ha (ρ a⁻¹ d)
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at h1
    rw [show ρ a⁻¹ d - d = -(d - ρ a⁻¹ d) by abel]
    exact W.neg_mem h1

@[expose] def fixOn (ρ : Representation (ZMod 2) G D) (W : Submodule (ZMod 2) D) :
    Subgroup G where
  carrier := {y | ∀ d ∈ W, ρ y d = d}
  one_mem' d _ := by rw [map_one, Module.End.one_apply]
  mul_mem' {a b} ha hb d hd := by rw [map_mul, Module.End.mul_apply, hb d hd, ha d hd]
  inv_mem' {a} ha d hd := by
    conv_lhs => rw [← ha d hd]
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

end Trivial

theorem binary_GL3_transvection_rank_saturation_lifts_the_whole_commutator
    {I : Type*} [AddCommGroup I] [Module (ZMod 2) I] [FiniteDimensional (ZMod 2) I]
    (hI : finrank (ZMod 2) I = 3)
    {D : Type*} [AddCommGroup D] [Module (ZMod 2) D] [FiniteDimensional (ZMod 2) D]
    (ρ : Representation (ZMod 2) (LinearMap.GeneralLinearGroup (ZMod 2) I) D)
    {D₀ D₁ : Submodule (ZMod 2) D} (hD01 : D₀ < D₁) (_hD₀ : ∀ y, ∀ d ∈ D₀, ρ y d ∈ D₀)
    (hD₁ : ∀ y, ∀ d ∈ D₁, ρ y d ∈ D₁) {r : ℕ} (_hr : 1 ≤ r) (π : D₁ →ₗ[ZMod 2] (Fin r → I))
    (hπs : Function.Surjective π) (hπk : LinearMap.ker π = D₀.comap D₁.subtype)
    (hπe : ∀ y (d : D₁), π ⟨ρ y d, hD₁ y d d.2⟩ = fun i => (y : I →ₗ[ZMod 2] I) (π d i))
    {H : Submodule (ZMod 2) I} {f : Module.Dual (ZMod 2) I} (hf : f ≠ 0)
    (_hH : LinearMap.ker f = H)
    (hc : finrank (ZMod 2) D -
      finrank (ZMod 2) (Representation.invariants (ρ.comp (axisGroup f).subtype)) = r) :
    (∀ y, ∀ d ∈ D₀, ρ y d = d) ∧ (∀ y d, ρ y d - d ∈ D₁) ∧
    ∃ hle : Representation.Coinvariants.ker ρ ≤ D₁,
      Function.Bijective (π.comp (Submodule.inclusion hle)) ∧
      finrank (ZMod 2) (Representation.Coinvariants.ker ρ) = 3 * r ∧
      (∀ (X : Type*) [Group X] (σ : Representation (ZMod 2) X D)
          (τ : Representation (ZMod 2) X (Fin r → I)),
        (∀ x y, σ x ∘ₗ ρ y = ρ y ∘ₗ σ x) → (∀ x, ∀ d ∈ D₀, σ x d ∈ D₀) →
        ∀ hσ₁ : ∀ x, ∀ d ∈ D₁, σ x d ∈ D₁,
        (∀ x (d : D₁), π ⟨σ x d, hσ₁ x d d.2⟩ = τ x (π d)) →
        ∀ x, ∃ hx : ∀ c ∈ Representation.Coinvariants.ker ρ,
            σ x c ∈ Representation.Coinvariants.ker ρ,
          ∀ c : Representation.Coinvariants.ker ρ,
            π (Submodule.inclusion hle ⟨σ x c, hx c c.2⟩) =
              τ x (π (Submodule.inclusion hle c))) ∧
      ∀ t : D ≃ₗ[ZMod 2] D, (∀ y, ∃ y', t.toLinearMap ∘ₗ ρ y = ρ y' ∘ₗ t.toLinearMap) →
        (Representation.Coinvariants.ker ρ).map t.toLinearMap =
          Representation.Coinvariants.ker ρ := by
  classical
  let S : SatData I D :=
    { ρ := ρ, D₀ := D₀, D₁ := D₁, le := hD01.le, inv₁ := hD₁, r := r, π := π, surj := hπs,
      ker := fun d => by rw [← LinearMap.mem_ker, hπk]; rfl, equiv := hπe }
  have hcod : ∀ g : Module.Dual (ZMod 2) I, g ≠ 0 → S.codim (axisGroup g) = S.r :=
    fun g hg => S.codim_eq_of_codim_eq hf hg hc
  have htv0 : ∀ (u : I) (g : Module.Dual (ZMod 2) I) (hgu : g u = 0),
      tvGL u g hgu ∈ fixOn ρ D₀ := by
    intro u g hgu d hd
    by_cases hg : g = 0
    · subst hg
      rw [tvGL_zero_left, map_one, Module.End.one_apply]
    · exact (S.axis_facts hI hg (hcod g hg)).1 _ (tvGL_mem_axisGroup hgu) d hd
  have htv1 : ∀ (u : I) (g : Module.Dual (ZMod 2) I) (hgu : g u = 0),
      tvGL u g hgu ∈ trivOn ρ D₁ := by
    intro u g hgu d
    by_cases hg : g = 0
    · subst hg
      rw [tvGL_zero_left, map_one, Module.End.one_apply, sub_self]
      exact D₁.zero_mem
    · exact (S.axis_facts hI hg (hcod g hg)).2 _ (tvGL_mem_axisGroup hgu) d
  have hgen : ∀ K : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) I),
      (∀ (u : I) (g : Module.Dual (ZMod 2) I) (hgu : g u = 0), tvGL u g hgu ∈ K) →
      ∀ y, y ∈ K := by
    intro K hK y
    refine (Subgroup.closure_le K).mpr ?_ (mem_closure_transvections hI y)
    rintro _ ⟨u, g, hgu, rfl⟩
    exact hK u g hgu
  have hfix0 : ∀ y, ∀ d ∈ D₀, ρ y d = d := fun y => hgen _ htv0 y
  have hfix1 : ∀ y d, ρ y d - d ∈ D₁ := fun y => hgen _ htv1 y
  let b := Module.finBasisOfFinrankEq (ZMod 2) I hI
  have hco : ∀ i j : Fin 3, i ≠ j → b.coord i (b j) = 0 := fun i j hij => by
    simp [Basis.coord_apply, Basis.repr_self, Ne.symm hij]
  have hcone : ∀ i, b.coord i ≠ 0 := fun i h0 => by
    have h1 := congrArg (fun g : Module.Dual (ZMod 2) I => g (b i)) h0
    simp at h1
  have he₀ : b.coord 1 (b 0) = 0 := hco 1 0 (by decide)
  have he₁ : b.coord 0 (b 1) = 0 := hco 0 1 (by decide)
  have he₂ : b.coord 0 (b 2) = 0 := hco 0 2 (by decide)
  set W := S.U (tvGL (b 0) (b.coord 1) he₀) ⊔ S.U (tvGL (b 1) (b.coord 0) he₁) ⊔
    S.U (tvGL (b 2) (b.coord 0) he₂) with hW
  have hWall : ∀ (u : I) (g : Module.Dual (ZMod 2) I) (hgu : g u = 0),
      S.U (tvGL u g hgu) ≤ W := by
    intro u g hgu
    by_cases hu0 : u = 0
    · subst hu0
      rintro _ ⟨d, rfl⟩
      show ρ (tvGL 0 g hgu) d - d ∈ W
      rw [show tvGL 0 g hgu = 1 from tvGL_zero_right g, map_one, Module.End.one_apply, sub_self]
      exact W.zero_mem
    · by_cases hg : g = 0
      · subst hg
        rintro _ ⟨d, rfl⟩
        show ρ (tvGL u 0 hgu) d - d ∈ W
        rw [tvGL_zero_left, map_one, Module.End.one_apply, sub_self]
        exact W.zero_mem
      · exact S.U_le_W hI hcod b (hcone 1) (hcone 0) (hcone 0) he₀ he₁ he₂ hu0 hg hgu
  have hUker : ∀ t, S.U t ≤ Representation.Coinvariants.ker ρ := by
    rintro t _ ⟨d, rfl⟩
    exact Submodule.subset_span ⟨(t, d), rfl⟩
  have hWle : W ≤ Representation.Coinvariants.ker ρ :=
    sup_le (sup_le (hUker _) (hUker _)) (hUker _)
  have hkerle : Representation.Coinvariants.ker ρ ≤ W := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨y, d⟩, rfl⟩
    have hy : y ∈ trivOn ρ W := hgen (trivOn ρ W) (fun u g hgu d' => hWall u g hgu ⟨d', rfl⟩) y
    exact hy d
  have hWeq : Representation.Coinvariants.ker ρ = W := le_antisymm hkerle hWle
  have hWD₁ : W ≤ D₁ := by
    rw [← hWeq]
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨y, d⟩, rfl⟩
    exact hfix1 y d
  have hn0 : (b.coord 1) ≠ 0 := hcone 1
  have hn1 : (b.coord 0) ≠ 0 := hcone 0
  obtain ⟨hT0, hr0, hπ0, -, -⟩ := S.tv_facts hI hn0 (hcod _ hn0) he₀ (b.ne_zero 0)
  obtain ⟨hT1', hr1, hπ1, -, -⟩ := S.tv_facts hI hn1 (hcod _ hn1) he₁ (b.ne_zero 1)
  obtain ⟨hT2, hr2, hπ2, -, -⟩ := S.tv_facts hI hn1 (hcod _ hn1) he₂ (b.ne_zero 2)
  have hWr : finrank (ZMod 2) W ≤ 3 * r := by
    have h1 : finrank (ZMod 2) W ≤ finrank (ZMod 2)
        ↥(S.U (tvGL (b 0) (b.coord 1) he₀) ⊔ S.U (tvGL (b 1) (b.coord 0) he₁)) +
          finrank (ZMod 2) (S.U (tvGL (b 2) (b.coord 0) he₂)) :=
      Submodule.finrank_add_le_finrank_add_finrank _ _
    have h2 := Submodule.finrank_add_le_finrank_add_finrank
      (S.U (tvGL (b 0) (b.coord 1) he₀)) (S.U (tvGL (b 1) (b.coord 0) he₁))
    change finrank (ZMod 2) (S.U (tvGL (b 0) (b.coord 1) he₀)) = r at hr0
    change finrank (ZMod 2) (S.U (tvGL (b 1) (b.coord 0) he₁)) = r at hr1
    change finrank (ZMod 2) (S.U (tvGL (b 2) (b.coord 0) he₂)) = r at hr2
    omega
  set W' := W.comap D₁.subtype with hW'
  have hW'f : finrank (ZMod 2) W' = finrank (ZMod 2) W :=
    (Submodule.comapSubtypeEquivOfLe hWD₁).finrank_eq
  have hpart : ∀ (j : Fin 3) (g : Module.Dual (ZMod 2) I) (hg : g ≠ 0) (hgj : g (b j) = 0)
      (hT : ∀ d, ρ (tvGL (b j) g hgj) d - d ∈ D₁)
      (hπT : ∀ e : D₁, π ⟨ρ (tvGL (b j) g hgj) e - e, hT e⟩ = fun i => g (π e i) • b j)
      (c : Fin r → ZMod 2), ∃ w : D₁, (w : D) ∈ S.U (tvGL (b j) g hgj) ∧
        π w = fun i => c i • b j := by
    intro j g hg hgj hT hπT c
    obtain ⟨x₀, hx₀⟩ := exists_eq_one_of_ne_zero hg
    obtain ⟨e, he⟩ := hπs fun i => c i • x₀
    refine ⟨⟨_, hT e⟩, ⟨e, rfl⟩, ?_⟩
    rw [hπT e, he]
    funext i
    simp [hx₀]
  have hsurjW : ∀ z : Fin r → I, ∃ w : D₁, (w : D) ∈ W ∧ π w = z := by
    intro z
    obtain ⟨w₀, hw₀, hπw₀⟩ := hpart 0 _ hn0 he₀ hT0 hπ0 fun i => b.repr (z i) 0
    obtain ⟨w₁, hw₁, hπw₁⟩ := hpart 1 _ hn1 he₁ hT1' hπ1 fun i => b.repr (z i) 1
    obtain ⟨w₂, hw₂, hπw₂⟩ := hpart 2 _ hn1 he₂ hT2 hπ2 fun i => b.repr (z i) 2
    refine ⟨w₀ + w₁ + w₂, ?_, ?_⟩
    · exact W.add_mem (W.add_mem (Submodule.mem_sup_left (Submodule.mem_sup_left hw₀))
        (Submodule.mem_sup_left (Submodule.mem_sup_right hw₁))) (Submodule.mem_sup_right hw₂)
    · rw [map_add, map_add, hπw₀, hπw₁, hπw₂]
      funext i
      have h1 := b.sum_repr (z i)
      rw [Fin.sum_univ_three] at h1
      simp only [Pi.add_apply]
      exact h1
  have hπWs : Function.Surjective (π.domRestrict W') := by
    intro z
    obtain ⟨w, hw, hπw⟩ := hsurjW z
    exact ⟨⟨w, hw⟩, hπw⟩
  have hπWker : LinearMap.ker (π.domRestrict W') = ⊥ := by
    have h1 := LinearMap.finrank_range_add_finrank_ker (π.domRestrict W')
    rw [LinearMap.range_eq_top.mpr hπWs, finrank_top, SatData.finrank_pi_fin, hI] at h1
    exact Submodule.finrank_eq_zero.mp (by omega)
  have hW3 : finrank (ZMod 2) W = 3 * r := by
    have h1 := LinearMap.finrank_range_add_finrank_ker (π.domRestrict W')
    rw [LinearMap.range_eq_top.mpr hπWs, finrank_top, SatData.finrank_pi_fin, hI, hπWker,
      finrank_bot] at h1
    omega
  have hle : Representation.Coinvariants.ker ρ ≤ D₁ := hWeq.le.trans hWD₁
  refine ⟨hfix0, hfix1, hle, ⟨?_, ?_⟩, by rw [hWeq, hW3], ?_, ?_⟩
  · intro c₁ c₂ h12
    have hc₁ : Submodule.inclusion hle c₁ ∈ W' := by
      change (c₁ : D) ∈ W
      rw [← hWeq]
      exact c₁.2
    have hc₂ : Submodule.inclusion hle c₂ ∈ W' := by
      change (c₂ : D) ∈ W
      rw [← hWeq]
      exact c₂.2
    have h1 : π.domRestrict W' ⟨_, hc₁⟩ = π.domRestrict W' ⟨_, hc₂⟩ := h12
    have h2 := (LinearMap.ker_eq_bot.mp hπWker) h1
    apply Subtype.ext
    exact congrArg (fun x : W' => ((x : D₁) : D)) h2
  · intro z
    obtain ⟨w, hw, hπw⟩ := hsurjW z
    have hw' : (w : D) ∈ Representation.Coinvariants.ker ρ := by
      rw [hWeq]
      exact hw
    exact ⟨⟨w, hw'⟩, hπw⟩
  · intro X _ σ τ hcomm _ hσ₁ hστ x
    have hx : ∀ c ∈ Representation.Coinvariants.ker ρ,
        σ x c ∈ Representation.Coinvariants.ker ρ := by
      intro c hc
      have h1 : Representation.Coinvariants.ker ρ ≤
          (Representation.Coinvariants.ker ρ).comap (σ x) := by
        apply Submodule.span_le.mpr
        rintro _ ⟨⟨y, d⟩, rfl⟩
        change σ x (ρ y d - d) ∈ Representation.Coinvariants.ker ρ
        have h2 : σ x (ρ y d) = ρ y (σ x d) := LinearMap.congr_fun (hcomm x y) d
        rw [map_sub, h2]
        exact Submodule.subset_span ⟨(y, σ x d), rfl⟩
      exact h1 hc
    refine ⟨hx, fun c => ?_⟩
    have h1 : Submodule.inclusion hle ⟨σ x c, hx c c.2⟩ =
        ⟨σ x (Submodule.inclusion hle c), hσ₁ x _ (Submodule.inclusion hle c).2⟩ := rfl
    rw [h1, hστ]
  · intro t ht
    have hle' : (Representation.Coinvariants.ker ρ).map t.toLinearMap ≤
        Representation.Coinvariants.ker ρ := by
      rw [Submodule.map_le_iff_le_comap]
      apply Submodule.span_le.mpr
      rintro _ ⟨⟨y, d⟩, rfl⟩
      obtain ⟨y', hy'⟩ := ht y
      change t (ρ y d - d) ∈ Representation.Coinvariants.ker ρ
      have h2 : t (ρ y d) = ρ y' (t d) := LinearMap.congr_fun hy' d
      rw [map_sub, h2]
      exact Submodule.subset_span ⟨(y', t d), rfl⟩
    apply Submodule.eq_of_le_of_finrank_eq hle'
    exact (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ t.injective _)).symm

end CFSG.Quasithin.H13.NQTerm
