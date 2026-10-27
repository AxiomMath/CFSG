module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7CReflSteps

public section

namespace CFSG.StandardType.HdRo7C

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem hdRo7CSignRAux_two_smul {V : Type} [AddCommGroup V] [Module (ZMod 3) V] (x : V) :
    (2 : ZMod 3) • x = -x := by
  have h : (2 : ZMod 3) = -1 := by decide
  rw [h, neg_smul, one_smul]

private theorem hdRo7CSignRAux_add_self {V : Type} [AddCommGroup V] [Module (ZMod 3) V] (x : V) :
    x + x = -x := by
  rw [← two_smul (ZMod 3) x]
  exact hdRo7CSignRAux_two_smul x

private theorem hdRo7CSignRAux_neg_sub_self {V : Type} [AddCommGroup V] [Module (ZMod 3) V] (x : V) :
    -x - x = x := by
  rw [sub_eq_add_neg, ← neg_add, hdRo7CSignRAux_add_self x, neg_neg]

private theorem hdRo7CSignRAux_sub_two {V : Type} [AddCommGroup V] [Module (ZMod 3) V] (x : V) :
    x - (2 : ZMod 3) • x = -x := by
  module

private noncomputable def hdRo7CSignRAux_z {n : ℕ} {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] (b : Module.Basis (Fin (n + 1)) (ZMod 3) V) : V ≃ₗ[ZMod 3] V :=
  LinearEquiv.ofInvolutive (b.constr (ZMod 3) fun j => if j = 0 then b j else -b j) (by
    let T : V →ₗ[ZMod 3] V := b.constr (ZMod 3) fun j => if j = 0 then b j else -b j
    change Function.Involutive T
    have hT : ∀ j, T (b j) = if j = 0 then b j else -b j :=
      fun j => Module.Basis.constr_basis b (ZMod 3) _ j
    have hcomp : T.comp T = LinearMap.id := by
      apply b.ext
      intro j
      simp only [LinearMap.comp_apply, LinearMap.id_apply]
      rw [hT j]
      by_cases hj : j = 0
      · rw [if_pos hj, hT j, if_pos hj]
      · rw [if_neg hj, map_neg, hT j, if_neg hj, neg_neg]
    intro x
    have hx := congrArg (fun L : V →ₗ[ZMod 3] V => L x) hcomp
    simpa [LinearMap.comp_apply] using hx)

private theorem hdRo7CSignRAux_z_apply {n : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (b : Module.Basis (Fin (n + 1)) (ZMod 3) V) (j : Fin (n + 1)) :
    hdRo7CSignRAux_z b (b j) = if j = 0 then b j else -b j := by
  simp only [hdRo7CSignRAux_z, LinearEquiv.coe_ofInvolutive]
  rw [Module.Basis.constr_basis]

private theorem hdRo7CSignRAux_z_apply_zero {n : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (b : Module.Basis (Fin (n + 1)) (ZMod 3) V) : hdRo7CSignRAux_z b (b 0) = b 0 := by
  rw [hdRo7CSignRAux_z_apply, if_pos rfl]

private theorem hdRo7CSignRAux_z_apply_ne {n : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (b : Module.Basis (Fin (n + 1)) (ZMod 3) V) {j : Fin (n + 1)} (hj : j ≠ 0) :
    hdRo7CSignRAux_z b (b j) = -b j := by
  rw [hdRo7CSignRAux_z_apply, if_neg hj]

private theorem hdRo7CSignRAux_z_formula {n : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (b : Module.Basis (Fin (n + 1)) (ZMod 3) V) (v : V) :
    hdRo7CSignRAux_z b v = v - (2 : ZMod 3) • (v - (b.coord 0 v) • b 0) := by
  have hmap : (hdRo7CSignRAux_z b : V →ₗ[ZMod 3] V) =
      LinearMap.id - (2 : ZMod 3) • (LinearMap.id - (b.coord 0).smulRight (b 0)) := by
    refine b.ext (fun j => ?_)
    change hdRo7CSignRAux_z b (b j) =
      (LinearMap.id - (2 : ZMod 3) • (LinearMap.id - (b.coord 0).smulRight (b 0)) :
        V →ₗ[ZMod 3] V) (b j)
    rw [hdRo7CSignRAux_z_apply, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smul_apply,
      LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smulRight_apply,
      Module.Basis.coord_apply, Module.Basis.repr_self_apply]
    by_cases hj : j = 0
    · subst hj
      rw [if_pos rfl, if_pos rfl, one_smul, sub_self, smul_zero, sub_zero]
    · rw [if_neg hj, if_neg hj, zero_smul, sub_zero]
      exact (hdRo7CSignRAux_sub_two (b j)).symm
  have h := congrArg (fun L : V →ₗ[ZMod 3] V => L v) hmap
  simpa [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smul_apply, LinearMap.smulRight_apply]
    using h

private theorem hdRo7CSignRAux_z_neg_axis_sub {n : ℕ} {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] (b : Module.Basis (Fin (n + 1)) (ZMod 3) V) {g : V}
    (hg : b.coord 0 g = 0) : hdRo7CSignRAux_z b (-b 0 - g) = -b 0 + g := by
  have hc : b.coord 0 (-b 0 - g) = -1 := by
    rw [map_sub, map_neg, hg, Module.Basis.coord_apply, Module.Basis.repr_self_apply, if_pos rfl]
    ring
  rw [hdRo7CSignRAux_z_formula, hc, neg_smul, one_smul]
  rw [show (-b 0 - g) - (-b 0) = -g by abel]
  rw [hdRo7CSignRAux_two_smul (-g), neg_neg]
  rw [show (-b 0 - g) - g = -b 0 + (-g - g) by abel, hdRo7CSignRAux_neg_sub_self g]

private theorem hdRo7CSignRAux_z_sp {n : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (b : Module.Basis (Fin (n + 1)) (ZMod 3) V) : C2SP 3 b (hdRo7CSignRAux_z b) := by
  refine ⟨Equiv.refl _, fun j => if j = 0 then 1 else -1, rfl, by simp, ?_, ?_⟩
  · intro j
    dsimp only
    by_cases hj : j = 0
    · left; rw [if_pos hj]
    · right; rw [if_neg hj]
  · intro j
    dsimp only
    rw [hdRo7CSignRAux_z_apply, Equiv.refl_apply]
    by_cases hj : j = 0
    · subst hj; rw [if_pos rfl, if_pos rfl, one_smul]
    · rw [if_neg hj, if_neg hj, neg_smul, one_smul]

private theorem hdRo7CSignRAux_range_smulRight {n : ℕ} {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] (b : Module.Basis (Fin (n + 1)) (ZMod 3) V) (g : V) :
    LinearMap.range ((b.coord 0).smulRight g) = Submodule.span (ZMod 3) {g} := by
  apply le_antisymm
  · rintro y ⟨v, rfl⟩
    rw [LinearMap.smulRight_apply]
    exact Submodule.mem_span_singleton.mpr ⟨b.coord 0 v, rfl⟩
  · rw [Submodule.span_le]
    rintro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact ⟨b 0, by rw [LinearMap.smulRight_apply, Module.Basis.coord_apply,
      Module.Basis.repr_self_apply, if_pos rfl, one_smul]⟩

private theorem hdRo7CSignRAux_supp_zero {n : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (b : Module.Basis (Fin (n + 1)) (ZMod 3) V) {r : V ≃ₗ[ZMod 3] V} {u : V}
    {φ : V →ₗ[ZMod 3] ZMod 3} {c : ZMod 3}
    (hform : ∀ v, r v = v - φ v • u) (hφ0 : φ (b 0) = 1) (hφu : φ u = 2)
    (hc : ∀ i, i ≠ 0 → φ (b i) = c * b.coord i u)
    (hI : ∀ i, i ≠ 0 → b.coord i u = 0) : C2SignX 3 b r := by
  have hφi : ∀ i, i ≠ 0 → φ (b i) = 0 := by
    intro i hi
    rw [hc i hi, hI i hi, mul_zero]
  have hrepr : u = ∑ i, b.coord i u • b i := by
    simpa only [Module.Basis.coord_apply] using (b.sum_repr u).symm
  have hcu : b.coord 0 u = 2 := by
    have hsum : u = b.coord 0 u • b 0 := by
      conv_lhs => rw [hrepr]
      rw [Fintype.sum_eq_single 0 (fun i hi => by rw [hI i hi, zero_smul])]
    have h2 : φ (b.coord 0 u • b 0) = 2 := by
      rw [← hsum]
      exact hφu
    rw [map_smul, hφ0, smul_eq_mul, mul_one] at h2
    exact h2
  have hu : u = (2 : ZMod 3) • b 0 := by
    rw [hrepr, Fintype.sum_eq_single 0 (fun i hi => by rw [hI i hi, zero_smul]), hcu]
  constructor
  · rw [hform (b 0), hφ0, one_smul, hu]
    exact hdRo7CSignRAux_sub_two (b 0)
  · intro i hi
    rw [hform (b i), hφi i hi, zero_smul, sub_zero]

theorem c2_reflSign_holds : C2ReflSignLeaf := by
  intro p hp_prime hp n hn V instAdd instMod b A hP hNoT r u φ hNF c hc hc0
  subst hp
  rcases hc0 with hc0 | hsupp
  · by_cases hI : ∀ i, i ≠ 0 → b.coord i u = 0
    · exact hdRo7CSignRAux_supp_zero b hNF.hform hNF.hφ0 hNF.hφu hc hI
    · exfalso
      obtain ⟨j, hj0, hjne⟩ : ∃ j, j ≠ 0 ∧ b.coord j u ≠ 0 := by
        by_contra hcon
        exact hI (fun i hi => by
          by_contra hne
          exact hcon ⟨i, hi, hne⟩)
      have hφi : ∀ i, i ≠ 0 → φ (b i) = 0 := by
        intro i hi
        rw [hc i hi, hc0, zero_mul]
      have hφcoord : φ = b.coord 0 := by
        refine b.ext (fun i => ?_)
        by_cases hi : i = 0
        · subst hi
          rw [hNF.hφ0, Module.Basis.coord_apply, Module.Basis.repr_self_apply, if_pos rfl]
        · rw [hφi i hi, Module.Basis.coord_apply, Module.Basis.repr_self_apply, if_neg hi]
      have hcu : b.coord 0 u = 2 := by
        have h := hNF.hφu
        rw [hφcoord] at h
        exact h
      set a : V := u - (2 : ZMod 3) • b 0 with ha_def
      have hca : b.coord 0 a = 0 := by
        rw [ha_def, map_sub, map_smul, hcu, Module.Basis.coord_apply,
          Module.Basis.repr_self_apply, if_pos rfl]
        ring
      have hb0j : b.coord j (b 0) = 0 := by
        rw [Module.Basis.coord_apply, Module.Basis.repr_self_apply, if_neg (Ne.symm hj0)]
      have hca_j : b.coord j a = b.coord j u := by
        rw [ha_def, map_sub, map_smul, hb0j, smul_zero, sub_zero]
      have ha_ne : a ≠ 0 := by
        intro ha0
        have hz : b.coord j a = 0 := by rw [ha0, map_zero]
        rw [hca_j] at hz
        exact hjne hz
      have hu_a : u = (2 : ZMod 3) • b 0 + a := by
        rw [ha_def]
        abel
      have hr0 : r (b 0) = -b 0 - a := by
        rw [hNF.hform (b 0), hNF.hφ0, one_smul, hu_a, hdRo7CSignRAux_two_smul (b 0)]
        rw [show b 0 - (-b 0 + a) = (b 0 + b 0) - a by abel, hdRo7CSignRAux_add_self (b 0)]
      have hri : ∀ i, i ≠ 0 → r (b i) = b i := by
        intro i hi
        rw [hNF.hform (b i), hφi i hi, zero_smul, sub_zero]
      have hra : r a = a := by
        rw [hNF.hform a, hφcoord, hca, zero_smul, sub_zero]
      let z : V ≃ₗ[ZMod 3] V := hdRo7CSignRAux_z b
      have hz0 : z (b 0) = b 0 := hdRo7CSignRAux_z_apply_zero b
      have hzi : ∀ i, i ≠ 0 → z (b i) = -b i := fun i hi => hdRo7CSignRAux_z_apply_ne b hi
      have hzA : z ∈ A := hP z (hdRo7CSignRAux_z_sp b)
      have hz_neg_axis_sub : z (-b 0 - a) = -b 0 + a :=
        hdRo7CSignRAux_z_neg_axis_sub b hca
      set r' : V ≃ₗ[ZMod 3] V := z * r * z with hr'_def
      have hr'_0 : r' (b 0) = -b 0 + a := by
        rw [hr'_def, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hz0, hr0, hz_neg_axis_sub]
      have hr'_i : ∀ i, i ≠ 0 → r' (b i) = b i := by
        intro i hi
        rw [hr'_def, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hzi i hi, map_neg, hri i hi,
          map_neg, hzi i hi, neg_neg]
      have hr'A : r' ∈ A := by
        rw [hr'_def]
        exact A.mul_mem (A.mul_mem hzA hNF.hr) hzA
      set t : V ≃ₗ[ZMod 3] V := r * r' with ht_def
      have ht_0 : t (b 0) = b 0 - a := by
        rw [ht_def, LinearEquiv.mul_apply, hr'_0, map_add, map_neg, hr0, hra, neg_sub,
          sub_neg_eq_add]
        rw [show (a + b 0) + a = b 0 + (a + a) by abel, hdRo7CSignRAux_add_self a, sub_eq_add_neg]
      have ht_i : ∀ i, i ≠ 0 → t (b i) = b i := by
        intro i hi
        rw [ht_def, LinearEquiv.mul_apply, hr'_i i hi, hri i hi]
      have hmap_t : (t : V →ₗ[ZMod 3] V) = LinearMap.id - (b.coord 0).smulRight a := by
        refine b.ext (fun i => ?_)
        change t (b i) = (LinearMap.id - (b.coord 0).smulRight a : V →ₗ[ZMod 3] V) (b i)
        by_cases hi : i = 0
        · subst hi
          rw [ht_0, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smulRight_apply,
            Module.Basis.coord_apply, Module.Basis.repr_self_apply, if_pos rfl, one_smul]
        · rw [ht_i i hi, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smulRight_apply,
            Module.Basis.coord_apply, Module.Basis.repr_self_apply, if_neg hi, zero_smul,
            sub_zero]
      have ht_formula : ∀ v, t v = v - (b.coord 0 v) • a := by
        intro v
        have h := congrArg (fun L : V →ₗ[ZMod 3] V => L v) hmap_t
        simpa [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smulRight_apply] using h
      have hmove : ggLinMove t = Submodule.span (ZMod 3) {a} := by
        have hsub : (t : V →ₗ[ZMod 3] V) - LinearMap.id = -((b.coord 0).smulRight a) := by
          rw [hmap_t]
          abel
        rw [ggLinMove, hsub, LinearMap.range_neg]
        exact hdRo7CSignRAux_range_smulRight b a
      have htransv : C2Transv 3 t := by
        refine ⟨?_, ?_⟩
        · rw [hmove]
          exact finrank_span_singleton ha_ne
        · intro w
          have hcw : b.coord 0 (t w - w) = 0 := by
            have hw : t w - w = -((b.coord 0 w) • a) := by
              rw [ht_formula]
              abel
            rw [hw, map_neg, map_smul, hca, smul_zero, neg_zero]
          rw [ht_formula (t w - w), hcw, zero_smul, sub_zero]
      have htA : t ∈ A := by
        rw [ht_def]
        exact A.mul_mem hNF.hr hr'A
      exact hNoT t htA htransv
  · exact hdRo7CSignRAux_supp_zero b hNF.hform hNF.hφ0 hNF.hφu hc hsupp

end CFSG.StandardType.HdRo7C
