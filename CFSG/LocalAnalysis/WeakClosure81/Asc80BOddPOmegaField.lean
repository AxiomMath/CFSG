module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataBasic
import CFSG.Mathlib.FieldTheory.Finite.QuadraticZeroMulti
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentFixedSpace
import CFSG.Quasithin.Vol2.Ch10Reselect.GaloisDescent
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentNormalization

public section

namespace CFSG.LocalAnalysis.WeakClosure81.POmegaOuter

open Subgroup Matrix QuadraticMap
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBLinearTwoDescent
open CFSG.ComponentClassification.CatalogueBOrthogonalDescent
open CFSG.Quasithin.Vol2.Ch10Reselect

variable {K : Type} [Field K] [Finite K] {d : ℕ}
  {Q : QuadraticForm K (Fin d → K)}

private theorem polar_coordinateSemilinearMap' {K : Type} [Field K] {d : ℕ}
    {Q : QuadraticForm K (Fin d → K)} {g : similarityPairs Q} (u v : Fin d → K) :
    polar Q (coordinateSemilinearMap g.val u) (coordinateSemilinearMap g.val v) =
      (multiplier Q g : K) * g.val.right (polar Q u v) := by
  have hu := multiplier_spec Q g u
  have hv := multiplier_spec Q g v
  have h := multiplier_spec Q g (u + v)
  rw [map_add] at h
  rw [QuadraticMap.map_add Q (coordinateSemilinearMap g.val u)
    (coordinateSemilinearMap g.val v)] at h
  rw [QuadraticMap.map_add Q u v] at h
  rw [map_add] at h
  rw [map_add] at h
  rw [hu, hv, mul_add, mul_add] at h
  linear_combination h

theorem exists_stable_singular_field {K : Type} [Field K] [Finite K] {d : ℕ}
    {Q : QuadraticForm K (Fin d → K)} (h2 : (2 : K) ≠ 0) (hnd : Q.polarBilin.Nondegenerate)
    (hd : 5 ≤ d) (ga gb : similarityPairs Q) (hφ : ga.val.right ≠ 1) (hb : gb.val.right = 1)
    (ha2 : (ga * ga).val.right = 1 ∧
      ∃ c : Kˣ, (ga * ga).val.left = GeneralLinearGroup.scalar (Fin d) c)
    (hb2 : ∃ c : Kˣ, (gb * gb).val.left = GeneralLinearGroup.scalar (Fin d) c)
    (hab : ∃ c : Kˣ,
      (ga * gb * ga⁻¹ * gb⁻¹).val.left = GeneralLinearGroup.scalar (Fin d) c) :
    ∃ W : Submodule K (Fin d → K), W ≠ ⊥ ∧ (∀ x ∈ W, Q x = 0) ∧
      (∀ x ∈ W, coordinateSemilinearMap ga.val x ∈ W) ∧
      ∀ x ∈ W, coordinateSemilinearMap gb.val x ∈ W := by
  classical
  obtain ⟨hφ2, c, hc⟩ := ha2
  obtain ⟨β, hβ⟩ := hb2
  obtain ⟨cl, hcl⟩ := hab
  set φ : K ≃+* K := ga.val.right with hφdef
  have hφne : φ ≠ 1 := hφ
  have hφsq : φ * φ = 1 := by
    have h : (ga.val * ga.val).right = 1 := hφ2
    rw [coordinateSemilinearGroup_mul_field] at h
    exact h
  have horder : orderOf φ = 2 := orderOf_eq_prime (by rw [pow_two]; exact hφsq) hφne
  have hσ2 : ∀ v : Fin d → K,
      coordinateSemilinearMap ga.val (coordinateSemilinearMap ga.val v) = (c : K) • v := by
    intro v
    have hpair : ga.val * ga.val =
        SemidirectProduct.mk (GeneralLinearGroup.scalar (Fin d) c) 1 := by
      apply SemidirectProduct.ext
      · exact hc
      · rw [coordinateSemilinearGroup_mul_field]; exact hφ2
    have hfun : (fun i => (1 : K ≃+* K) (v i)) = v := rfl
    rw [← coordinateSemilinearMap_mul, hpair, coordinateSemilinearMap_apply, hfun,
      Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_const_mulVec]
  have hφc : φ (c : K) = (c : K) := by
    have key : ∀ v : Fin d → K, (c : K) • coordinateSemilinearMap ga.val v =
        φ (c : K) • coordinateSemilinearMap ga.val v := by
      intro v
      have h1 : coordinateSemilinearMap ga.val (coordinateSemilinearMap ga.val
          (coordinateSemilinearMap ga.val v)) = (c : K) • coordinateSemilinearMap ga.val v :=
        hσ2 _
      have h2 : coordinateSemilinearMap ga.val (coordinateSemilinearMap ga.val
          (coordinateSemilinearMap ga.val v)) =
          φ (c : K) • coordinateSemilinearMap ga.val v := by
        conv_lhs => rw [hσ2 v]
        rw [coordinateSemilinearMap_smul]
      rw [← h1, h2]
    have key2 : ∀ w : Fin d → K, (c : K) • w = φ (c : K) • w := by
      intro w
      obtain ⟨v, rfl⟩ := (coordinateSemilinearMap ga.val).surjective w
      exact key v
    have : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
    obtain ⟨w, hw⟩ := exists_ne (0 : Fin d → K)
    exact smul_left_injective K hw (key2 w).symm
  have hcinv : φ (((c⁻¹ : Kˣ) : K)) = ((c⁻¹ : Kˣ) : K) := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, hφc]
  obtain ⟨t, ht⟩ := exists_norm_unit K φ hφsq hφne c⁻¹ hcinv
  have ht' : (t : K) * φ (t : K) = (c : K)⁻¹ := by
    rw [← Units.val_inv_eq_inv_val]
    exact ht
  let S : (Fin d → K) ≃+ (Fin d → K) :=
    (coordinateSemilinearMap ga.val).trans (LinearEquiv.smulOfUnit t).toAddEquiv
  have hS_apply : ∀ v : Fin d → K, S v = (t : K) • coordinateSemilinearMap ga.val v :=
    fun v => rfl
  have hS2 : Function.Involutive S := by
    intro v
    rw [hS_apply, hS_apply, coordinateSemilinearMap_smul, hσ2, smul_smul, smul_smul, ht',
      inv_mul_cancel₀ (Units.ne_zero c), one_smul]
  have hSsemi : ∀ (a : K) (x : Fin d → K), S (a • x) = φ a • S x := by
    intro a x
    rw [hS_apply, hS_apply, coordinateSemilinearMap_smul, smul_smul, smul_smul, mul_comm]
  let k := fixedSubfield K φ
  let V₀ : Submodule k (Fin d → K) := fixedSubspace φ S hSsemi
  have hdim : Module.finrank k V₀ = d := by
    rw [fixedSubspace_finrank φ hφsq hφne h2 S hS2 hSsemi, Module.finrank_fin_fun]
  have h5 : 2 * 2 < Module.finrank k V₀ := by rw [hdim]; omega
  let Bm : (Fin d → K) ≃ₗ[K] (Fin d → K) := matrixLinearEquiv gb.val.left
  have hBm_apply : ∀ v : Fin d → K, Bm v = gb.val.left.val *ᵥ v :=
    fun v => matrixLinearEquiv_apply _ _
  have hgb_map : ∀ v : Fin d → K, coordinateSemilinearMap gb.val v = Bm v := by
    intro v
    rw [coordinateSemilinearMap_apply, hBm_apply]
    have hfun : (fun i => gb.val.right (v i)) = v := by
      rw [hb]; rfl
    rw [hfun]
  have hBm_sim : ∀ v : Fin d → K, Q (Bm v) = (multiplier Q gb : K) * Q v := by
    intro v
    have h := multiplier_spec Q gb v
    have h1 : (1 : K ≃+* K) (Q v) = Q v := rfl
    rw [hgb_map, hb, h1] at h
    exact h
  have hBm2 : ∀ v : Fin d → K, Bm (Bm v) = (β : K) • v := by
    intro v
    have hmul : gb.val.left * gb.val.left = GeneralLinearGroup.scalar (Fin d) β := by
      have h := coordinateSemilinearGroup_mul_matrix gb.val gb.val
      rw [hb] at h
      have hone : (1 : MulAut (GL (Fin d) K)) gb.val.left = gb.val.left := rfl
      rw [map_one, hone] at h
      exact h.symm.trans hβ
    have h1 : Bm (Bm v) = matrixLinearEquiv (gb.val.left * gb.val.left) v := by
      show matrixLinearEquiv gb.val.left (matrixLinearEquiv gb.val.left v) = _
      rw [matrixLinearEquiv_mul, LinearEquiv.mul_apply]
    rw [h1, hmul, matrixLinearEquiv_apply, Matrix.GeneralLinearGroup.coe_scalar,
      Matrix.scalar_apply, Matrix.diagonal_const_mulVec]
  have hstep : ∀ w : Fin d → K,
      coordinateSemilinearMap (ga.val * gb.val * ga.val⁻¹ * gb.val⁻¹)
        (coordinateSemilinearMap gb.val (coordinateSemilinearMap ga.val w))
      = coordinateSemilinearMap ga.val (coordinateSemilinearMap gb.val w) := by
    intro w
    rw [coordinateSemilinearMap_mul, coordinateSemilinearMap_mul,
      coordinateSemilinearMap_mul, coordinateSemilinearMap_inv, coordinateSemilinearMap_inv]
    simp only [AddEquiv.symm_apply_apply]
  have hmap : ∀ w : Fin d → K,
      coordinateSemilinearMap (ga.val * gb.val * ga.val⁻¹ * gb.val⁻¹) w = (cl : K) • w := by
    have hright : (ga.val * gb.val * ga.val⁻¹ * gb.val⁻¹).right = 1 := by
      simp [hb]
    have hpair : ga.val * gb.val * ga.val⁻¹ * gb.val⁻¹ =
        SemidirectProduct.mk (GeneralLinearGroup.scalar (Fin d) cl) 1 := by
      apply SemidirectProduct.ext
      · exact hcl
      · exact hright
    intro w
    rw [hpair, coordinateSemilinearMap_apply]
    have hfun : (fun i => (1 : K ≃+* K) (w i)) = w := rfl
    rw [hfun, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.diagonal_const_mulVec]
  have hcomm : ∀ w : Fin d → K,
      coordinateSemilinearMap ga.val (coordinateSemilinearMap gb.val w) =
        (cl : K) • coordinateSemilinearMap gb.val (coordinateSemilinearMap ga.val w) := by
    intro w
    have h2 := hmap (coordinateSemilinearMap gb.val (coordinateSemilinearMap ga.val w))
    rw [hstep w] at h2
    exact h2
  have hSBmS : ∀ v : Fin d → K, S (Bm (S v)) = (cl : K) • Bm v := by
    intro v
    have step1 : S (Bm (S v)) = S ((t : K) • Bm (coordinateSemilinearMap ga.val v)) := by
      rw [hS_apply v, Bm.map_smul]
    have step2 : S ((t : K) • Bm (coordinateSemilinearMap ga.val v)) =
        (t : K) • coordinateSemilinearMap ga.val
          ((t : K) • Bm (coordinateSemilinearMap ga.val v)) := hS_apply _
    rw [step1, step2, coordinateSemilinearMap_smul, smul_smul, ht']
    rw [← hgb_map, hcomm, hσ2, coordinateSemilinearMap_smul, hb]
    rw [smul_smul]
    have hone : (1 : K ≃+* K) (c : K) = (c : K) := rfl
    rw [hone, ← hgb_map]
    have hscalar : (c : K)⁻¹ * (cl : K) * (c : K) = (cl : K) := by
      have hc0 : (c : K) ≠ 0 := Units.ne_zero c
      field_simp
    rw [smul_smul, hscalar]
  have hclφcl : (cl : K) * φ (cl : K) = 1 := by
    have hA : ∀ u : Fin d → K, S (Bm u) = (cl : K) • Bm (S u) := by
      intro u
      have h := hSBmS (S u)
      rwa [hS2 u] at h
    have hB : ∀ u : Fin d → K, Bm (S u) = φ (cl : K) • S (Bm u) := by
      intro u
      have h := congrArg S (hSBmS u)
      rw [hS2, hSsemi] at h
      exact h
    have key : ∀ u : Fin d → K, Bm (S u) = (φ (cl : K) * (cl : K)) • Bm (S u) := by
      intro u
      calc Bm (S u) = φ (cl : K) • S (Bm u) := hB u
        _ = φ (cl : K) • ((cl : K) • Bm (S u)) := by rw [hA u]
        _ = (φ (cl : K) * (cl : K)) • Bm (S u) := by rw [smul_smul]
    have : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
    obtain ⟨u, hu⟩ := exists_ne (0 : Fin d → K)
    have hxne : Bm (S u) ≠ 0 := by
      intro h0
      have h1 : S u = 0 := by
        have h := congrArg Bm.symm h0
        simpa using h
      have h2 : u = 0 := by
        have h3 := congrArg S h1
        rw [hS2, map_zero] at h3
        exact h3
      exact hu h2
    have h1 : (φ (cl : K) * (cl : K)) • Bm (S u) = (1 : K) • Bm (S u) := by
      rw [one_smul, ← key u]
    have h2 : φ (cl : K) * (cl : K) = 1 := smul_left_injective K hxne h1
    rw [mul_comm]
    exact h2
  have hQne : ∃ v : Fin d → K, Q v ≠ 0 := by
    by_contra h
    push Not at h
    have hpolar : ∀ x y : Fin d → K, polar Q x y = 0 := by
      intro x y
      have h2 := QuadraticMap.map_add Q x y
      rw [h (x + y), h x, h y, zero_add, zero_add] at h2
      exact h2.symm
    have : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
    obtain ⟨w, hw⟩ := exists_ne (0 : Fin d → K)
    refine hw (hnd.1 w fun y => ?_)
    rw [polarBilin_apply_apply]
    exact hpolar w y
  set ν : K := (t : K) * (t : K) * (multiplier Q ga : K) with hνdef
  have hνne : ν ≠ 0 := by
    have h1 : (t : K) ≠ 0 := Units.ne_zero t
    have h2 : (multiplier Q ga : K) ≠ 0 := Units.ne_zero (multiplier Q ga)
    simp [hνdef, mul_ne_zero (mul_ne_zero h1 h1) h2]
  have hS_sim : ∀ v : Fin d → K, Q (S v) = ν * φ (Q v) := by
    intro v
    rw [hS_apply, QuadraticMap.map_smul, multiplier_spec, hνdef]
    rw [smul_eq_mul]
    ring
  have hφ2' : ∀ x : K, φ (φ x) = x := by
    intro x
    have h := congrArg (fun e : K ≃+* K => e x) hφsq
    simpa using h
  have hνφν : ν * φ ν = 1 := by
    have hσμ : ∀ v : Fin d → K,
        Q (coordinateSemilinearMap ga.val (coordinateSemilinearMap ga.val v))
          = (multiplier Q ga : K) * φ (multiplier Q ga : K) * Q v := by
      intro v
      rw [multiplier_spec Q ga (coordinateSemilinearMap ga.val v), multiplier_spec Q ga v,
        map_mul, hφ2']
      ring
    have hc2 : ∀ v : Fin d → K,
        Q (coordinateSemilinearMap ga.val (coordinateSemilinearMap ga.val v))
          = (c : K) * (c : K) * Q v := by
      intro v
      rw [hσ2, QuadraticMap.map_smul]
      simp [smul_eq_mul, mul_assoc]
    have hμc : (multiplier Q ga : K) * φ (multiplier Q ga : K) = (c : K) * (c : K) := by
      obtain ⟨v, hv⟩ := hQne
      have h1 := hσμ v
      rw [hc2 v] at h1
      exact mul_right_cancel₀ hv h1.symm
    have ht2 : (t : K) * φ (t : K) = (c : K)⁻¹ := ht'
    calc ν * φ ν = ((t : K) * (t : K) * (multiplier Q ga : K)) *
          (φ (t : K) * φ (t : K) * φ (multiplier Q ga : K)) := by
          rw [hνdef]; simp only [map_mul]
        _ = ((t : K) * φ (t : K)) * ((t : K) * φ (t : K)) *
            ((multiplier Q ga : K) * φ (multiplier Q ga : K)) := by ring
        _ = ((c : K)⁻¹ * (c : K)⁻¹) * ((c : K) * (c : K)) := by rw [ht2, hμc]
        _ = 1 := by
          have hc0 : (c : K) ≠ 0 := Units.ne_zero c
          field_simp
  have hprodν : ∏ i ∈ Finset.range 2, (φ ^ i) ((ν)⁻¹) = 1 := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, Finset.prod_range_succ, Finset.prod_range_one]
    have h0 : (φ ^ 0) ((ν)⁻¹) = (ν)⁻¹ := rfl
    have h1 : (φ ^ 1) ((ν)⁻¹) = φ ((ν)⁻¹) := rfl
    rw [h0, h1, map_inv₀, ← _root_.mul_inv_rev, mul_comm (φ ν) ν, hνφν, inv_one]
  obtain ⟨s, hsne, hs⟩ := gd_hilbert90 φ horder.symm (by norm_num) ((ν)⁻¹)
    (inv_ne_zero hνne) hprodν
  have hφs : φ s = ν * s := by
    conv_rhs => rw [← hs]
    rw [← mul_assoc, mul_inv_cancel₀ hνne, one_mul]
  have hskill : ∀ x : K, x = ν * φ x → φ (s * x) = s * x := by
    intro x hx
    have hφx : φ x = (ν)⁻¹ * x := by
      conv_rhs => rw [hx]
      rw [← mul_assoc, inv_mul_cancel₀ hνne, one_mul]
    rw [map_mul, hφs, hφx]
    field_simp
  let tr : K →ₗ[k] k :=
    { toFun := fun x => ⟨x + φ x, (mem_fixedSubfield K φ _).mpr (by
        rw [map_add, hφ2']
        exact add_comm _ _)⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        push_cast
        rw [map_add]
        ring
      map_smul' := by
        intro a x
        apply Subtype.ext
        have ha : φ (a : K) = (a : K) := (mem_fixedSubfield K φ _).mp a.property
        simp only [Subfield.smul_def, smul_eq_mul, Subfield.coe_mul, map_mul, ha, RingHom.id_apply]
        ring }
  have htr : ∀ x : K, ((tr x : k) : K) = x + φ x := fun x => rfl
  let ms : K →ₗ[k] K := LinearMap.restrictScalars k (LinearMap.lsmul K K s)
  have hms : ∀ x : K, ms x = s * x := by
    intro x
    rw [LinearMap.restrictScalars_apply, LinearMap.lsmul_apply, smul_eq_mul]
  let L : K →ₗ[k] k := tr.comp ms
  have hL : ∀ x : K, ((L x : k) : K) = s * x + φ (s * x) := by
    intro x
    show ((tr (s * x) : k) : K) = _
    rw [htr]
  have hfixV : ∀ v : ↥V₀, Q (v : Fin d → K) = ν * φ (Q (v : Fin d → K)) := by
    intro v
    have hvfix : S (v : Fin d → K) = (v : Fin d → K) :=
      (mem_fixedSubspace φ S hSsemi _).mp v.property
    have h := hS_sim (v : Fin d → K)
    rwa [hvfix] at h
  let q1 : QuadraticForm k ↥V₀ := (L.compQuadraticMap' Q).comp V₀.subtype
  have hq1val : ∀ v : ↥V₀, ((q1 v : k) : K) = 2 * (s * Q (v : Fin d → K)) := by
    intro v
    have h1 : q1 v = L (Q (v : Fin d → K)) := rfl
    rw [h1, hL, hskill (Q (v : Fin d → K)) (hfixV v)]
    ring
  have hprodcl : ∏ i ∈ Finset.range 2, (φ ^ i) ((cl : K)) = 1 := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, Finset.prod_range_succ, Finset.prod_range_one]
    have h0 : (φ ^ 0) ((cl : K)) = (cl : K) := rfl
    have h1 : (φ ^ 1) ((cl : K)) = φ (cl : K) := rfl
    rw [h0, h1, hclφcl]
  obtain ⟨z, hzne, hz⟩ := gd_hilbert90 φ horder.symm (by norm_num) (cl : K)
    (Units.ne_zero cl) hprodcl
  let BmL : (Fin d → K) →ₗ[K] (Fin d → K) := (z : K) • Bm.toLinearMap
  have hBmL_apply : ∀ v : Fin d → K, BmL v = (z : K) • Bm v := by
    intro v
    simp only [BmL, LinearMap.smul_apply, LinearEquiv.coe_toLinearMap]
  have hSBmL : ∀ u : Fin d → K, S (BmL (S u)) = BmL u := by
    intro u
    rw [hBmL_apply, hBmL_apply, hSsemi, hSBmS, smul_smul]
    congr 1
    rw [mul_comm (φ z) (cl : K), hz]
  have hBmL_fix : ∀ v : ↥V₀, S (BmL (v : Fin d → K)) = BmL (v : Fin d → K) := by
    intro v
    have hvfix : S (v : Fin d → K) = (v : Fin d → K) :=
      (mem_fixedSubspace φ S hSsemi _).mp v.property
    have h := hSBmL (v : Fin d → K)
    rwa [hvfix] at h
  have hSpolar : ∀ u w : Fin d → K, polar Q (S u) (S w) = ν * φ (polar Q u w) := by
    intro u w
    rw [hS_apply, hS_apply, QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right,
      polar_coordinateSemilinearMap' (g := ga) u w, smul_smul, hνdef, smul_eq_mul]
    ring
  have hBmL_eig : ∀ v : ↥V₀, polar Q (v : Fin d → K) (BmL (v : Fin d → K)) =
      ν * φ (polar Q (v : Fin d → K) (BmL (v : Fin d → K))) := by
    intro v
    have hvfix : S (v : Fin d → K) = (v : Fin d → K) :=
      (mem_fixedSubspace φ S hSsemi _).mp v.property
    calc polar Q (v : Fin d → K) (BmL (v : Fin d → K))
        = polar Q (S (v : Fin d → K)) (S (BmL (v : Fin d → K))) := by
          rw [hvfix, hBmL_fix v]
      _ = ν * φ (polar Q (v : Fin d → K) (BmL (v : Fin d → K))) := hSpolar _ _
  let q2K : QuadraticForm K (Fin d → K) := (Q.comp (LinearMap.id + BmL)) - Q - Q.comp BmL
  have hq2K : ∀ v : Fin d → K, q2K v = polar Q v (BmL v) := by
    intro v
    simp only [q2K, QuadraticMap.sub_apply, QuadraticMap.comp_apply, LinearMap.add_apply,
      LinearMap.id_apply]
    rw [QuadraticMap.map_add Q v (BmL v)]
    abel
  let q2 : QuadraticForm k ↥V₀ := (L.compQuadraticMap' q2K).comp V₀.subtype
  have hq2val : ∀ v : ↥V₀, ((q2 v : k) : K) =
      2 * (s * polar Q (v : Fin d → K) (BmL (v : Fin d → K))) := by
    intro v
    have h1 : q2 v = L (q2K (v : Fin d → K)) := rfl
    rw [h1, hL, hq2K, hskill (polar Q (v : Fin d → K) (BmL (v : Fin d → K))) (hBmL_eig v)]
    ring
  have : FiniteDimensional k ↥V₀ := FiniteDimensional.of_finrank_pos (by rw [hdim]; omega)
  obtain ⟨v, hvzero, hv⟩ :=
    CFSG.FiniteField.exists_ne_zero_forall_eq_zero_of_quadraticForm
      (fun i : Fin 2 => if i = 0 then q1 else q2) (by rw [hdim]; omega)
  have hv1 : q1 v = 0 := by simpa using hv 0
  have hv2 : q2 v = 0 := by simpa using hv 1
  have hvne : (v : Fin d → K) ≠ 0 := by
    intro h
    exact hvzero (Subtype.ext h)
  have hQv : Q (v : Fin d → K) = 0 := by
    have h := hq1val v
    rw [hv1] at h
    rw [show ((0 : k) : K) = 0 from rfl] at h
    rcases mul_eq_zero.1 h.symm with h2' | h2'
    · exact absurd h2' h2
    · exact (mul_eq_zero.1 h2').resolve_left hsne
  have hBv : polar Q (v : Fin d → K) (BmL (v : Fin d → K)) = 0 := by
    have h := hq2val v
    rw [hv2] at h
    rw [show ((0 : k) : K) = 0 from rfl] at h
    rcases mul_eq_zero.1 h.symm with h2' | h2'
    · exact absurd h2' h2
    · exact (mul_eq_zero.1 h2').resolve_left hsne
  have hBmv : polar Q (v : Fin d → K) (Bm (v : Fin d → K)) = 0 := by
    have h := hBv
    rw [hBmL_apply, QuadraticMap.polar_smul_right, smul_eq_mul] at h
    exact (mul_eq_zero.1 h).resolve_left hzne
  have hQBmv : Q (Bm (v : Fin d → K)) = 0 := by
    rw [hBm_sim, hQv, mul_zero]
  have hvfix : S (v : Fin d → K) = (v : Fin d → K) :=
    (mem_fixedSubspace φ S hSsemi _).mp v.property
  have hσv : coordinateSemilinearMap ga.val (v : Fin d → K) = (t : K)⁻¹ • (v : Fin d → K) := by
    have h : (t : K) • coordinateSemilinearMap ga.val (v : Fin d → K) = (v : Fin d → K) := by
      rw [← hS_apply]; exact hvfix
    conv_rhs => rw [← h]
    rw [smul_smul, inv_mul_cancel₀ (Units.ne_zero t), one_smul]
  have hσBm : coordinateSemilinearMap ga.val (Bm (v : Fin d → K)) =
      ((t : K)⁻¹ * (cl : K)) • Bm (v : Fin d → K) := by
    have hSBmv : S (Bm (v : Fin d → K)) = (cl : K) • Bm (v : Fin d → K) := by
      have h := hSBmS (v : Fin d → K)
      rwa [hvfix] at h
    have h : (t : K) • coordinateSemilinearMap ga.val (Bm (v : Fin d → K)) =
        (cl : K) • Bm (v : Fin d → K) := by
      rw [← hS_apply]; exact hSBmv
    have h' : (t : K)⁻¹ • ((t : K) • coordinateSemilinearMap ga.val (Bm (v : Fin d → K))) =
        (t : K)⁻¹ • ((cl : K) • Bm (v : Fin d → K)) := by rw [h]
    rw [smul_smul, inv_mul_cancel₀ (Units.ne_zero t), one_smul, smul_smul] at h'
    exact h' 
  have hσBm' : coordinateSemilinearMap ga.val (Bm (v : Fin d → K)) ∈
      Submodule.span K {(v : Fin d → K), Bm (v : Fin d → K)} := by
    rw [hσBm]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  have hσv' : coordinateSemilinearMap ga.val (v : Fin d → K) ∈
      Submodule.span K {(v : Fin d → K), Bm (v : Fin d → K)} := by
    rw [hσv]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  have hvW : (v : Fin d → K) ∈ Submodule.span K {(v : Fin d → K), Bm (v : Fin d → K)} :=
    Submodule.subset_span (by simp)
  have hBmvW : Bm (v : Fin d → K) ∈ Submodule.span K
      {(v : Fin d → K), Bm (v : Fin d → K)} :=
    Submodule.subset_span (by simp)
  refine ⟨Submodule.span K {(v : Fin d → K), Bm (v : Fin d → K)}, ?_, ?_, ?_, ?_⟩
  · intro hbot
    rw [hbot] at hvW
    exact hvne (by simpa using hvW)
  · intro x hx
    obtain ⟨a, b, rfl⟩ := (Submodule.mem_span_pair).mp hx
    rw [QuadraticMap.map_add Q (a • (v : Fin d → K)) (b • Bm (v : Fin d → K)),
      QuadraticMap.map_smul, QuadraticMap.map_smul,
      QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right, hQv, hQBmv, hBmv]
    ring
  · intro x hx
    obtain ⟨a, b, rfl⟩ := (Submodule.mem_span_pair).mp hx
    rw [map_add, coordinateSemilinearMap_smul, coordinateSemilinearMap_smul]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ hσv')
      (Submodule.smul_mem _ _ hσBm')
  · intro x hx
    obtain ⟨a, b, rfl⟩ := (Submodule.mem_span_pair).mp hx
    rw [hgb_map, map_add, LinearEquiv.map_smul, LinearEquiv.map_smul, hBm2]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ hBmvW)
      (Submodule.smul_mem _ _ (Submodule.smul_mem _ _ hvW))

end CFSG.LocalAnalysis.WeakClosure81.POmegaOuter
