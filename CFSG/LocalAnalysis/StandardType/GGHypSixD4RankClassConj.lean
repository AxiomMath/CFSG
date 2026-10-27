module

public import CFSG.LocalAnalysis.StandardType.GGHypSixD4RankClassRep
public import CFSG.RankThree.OrthogonalInvolutions.Witt

public section

namespace CFSG.StandardType

namespace D4Rank

open Module CFSG.StandardType.Triality CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData CFSG.LieType.Universal.Spin
  CFSG.RankThree.PartOne.AUTSL QuadraticMap
open scoped Matrix

variable {K : Type} [Field K]

section Iso

theorem act_add (x : Om8 K) (y z : Fin (2 * 4) → K) : act x (y + z) = act x y + act x z :=
  Matrix.mulVec_add _ _ _

theorem act_sub (x : Om8 K) (y z : Fin (2 * 4) → K) : act x (y - z) = act x y - act x z :=
  Matrix.mulVec_sub _ _ _

theorem act_smul (x : Om8 K) (a : K) (y : Fin (2 * 4) → K) : act x (a • y) = a • act x y :=
  Matrix.mulVec_smul _ _ _

theorem Q_act (x : Om8 K) (y : Fin (2 * 4) → K) :
    coordinateQuadPlus 4 K (act x y) = coordinateQuadPlus 4 K y :=
  (mem_matrixIsometries_iff _ _).1 (matrixDerived_le_isometries _ x.2) y

theorem polar_act (x : Om8 K) (y z : Fin (2 * 4) → K) :
    polar (coordinateQuadPlus 4 K) (act x y) (act x z) = polar (coordinateQuadPlus 4 K) y z := by
  simp only [polar, ← act_add, Q_act]

theorem act_inv_act (x : Om8 K) (y : Fin (2 * 4) → K) : act x⁻¹ (act x y) = y := by
  rw [← act_mul, inv_mul_cancel, act_one]

theorem act_act_inv (x : Om8 K) (y : Fin (2 * 4) → K) : act x (act x⁻¹ y) = y := by
  rw [← act_mul, mul_inv_cancel, act_one]

end Iso

section Cube

variable [CharP K 2] {x : Om8 K}

theorem two_smul_vec (w : Fin (2 * 4) → K) : w + w = 0 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [← two_smul K w, h2, zero_smul]

theorem neg_vec (w : Fin (2 * 4) → K) : -w = w :=
  neg_eq_of_add_eq_zero_right (two_smul_vec w)

omit [CharP K 2] in
theorem act_cube (hx3 : x ^ 3 = 1) (y : Fin (2 * 4) → K) : act x (act x (act x y)) = y := by
  have h : act (x ^ 3) y = y := by rw [hx3, act_one]
  rwa [pow_succ, pow_succ, pow_one, act_mul, act_mul] at h

theorem act_sq_of_sum {v : Fin (2 * 4) → K} (hv : act x (act x v) + act x v + v = 0) :
    act x (act x v) = act x v + v := by
  rw [add_assoc] at hv
  rw [eq_neg_of_add_eq_zero_left hv, neg_vec]

omit [CharP K 2] in
theorem sum_of_range (hx3 : x ^ 3 = 1) (y : Fin (2 * 4) → K) :
    act x (act x (act x y - y)) + act x (act x y - y) + (act x y - y) = 0 := by
  rw [act_sub, act_sub, act_cube hx3]
  abel

theorem act_sq_of_range (hx3 : x ^ 3 = 1) (y : Fin (2 * 4) → K) :
    act x (act x (act x y - y)) = act x (act x y - y) + (act x y - y) :=
  act_sq_of_sum (sum_of_range hx3 y)

theorem act_sq_of_free (hx3 : x ^ 3 = 1) (hfree : ∀ y, act x y = y → y = 0)
    (v : Fin (2 * 4) → K) : act x (act x v) = act x v + v := by
  refine act_sq_of_sum (hfree _ ?_)
  rw [act_add, act_add, act_cube hx3]
  abel

omit [CharP K 2] in
theorem polar_fix_range {c : Fin (2 * 4) → K} (hc : act x c = c) (y : Fin (2 * 4) → K) :
    polar (coordinateQuadPlus 4 K) c (act x y - y) = 0 := by
  rw [polar_sub_right, ← polar_act x c y, hc, sub_self]

omit [CharP K 2] in
theorem act_fixPart (hx3 : x ^ 3 = 1) (y : Fin (2 * 4) → K) :
    act x (y + act x y + act x (act x y)) = y + act x y + act x (act x y) := by
  rw [act_add, act_add, act_cube hx3]
  abel

theorem decomp (y : Fin (2 * 4) → K) :
    y = (y + act x y + act x (act x y)) + (act x (act x y) - act x y) := by
  have h := two_smul_vec (act x (act x y))
  rw [sub_eq_add_neg, neg_vec]
  calc y = y + act x y + act x y + (act x (act x y) + act x (act x y)) := by
        rw [h, add_zero, add_assoc y, two_smul_vec, add_zero]
    _ = _ := by abel

end Cube

section Plane

variable [CharP K 2] {x : Om8 K}

theorem polar_self_zero (y : Fin (2 * 4) → K) : polar (coordinateQuadPlus 4 K) y y = 0 := by
  rw [polar_self, two_nsmul, CharTwo.add_self_eq_zero]

theorem polar_v_act_v {v : Fin (2 * 4) → K} (hQ : coordinateQuadPlus 4 K v = 1)
    (hv : act x (act x v) = act x v + v) : polar (coordinateQuadPlus 4 K) v (act x v) = 1 := by
  have h1 : v + act x v = act x (act x v) := by rw [hv, add_comm]
  rw [polar, h1]
  simp only [Q_act]
  rw [hQ]
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  linear_combination -h2

omit [CharP K 2] in
theorem linIndep_of_dual {ι : Type*} [Fintype ι] [DecidableEq ι] {u w : ι → Fin (2 * 4) → K}
    (h : ∀ i j, polar (coordinateQuadPlus 4 K) (u i) (w j) = if i = j then 1 else 0) :
    LinearIndependent K u := by
  rw [Fintype.linearIndependent_iff]
  intro g hg j
  have h1 : polarBilin (coordinateQuadPlus 4 K) (∑ i, g i • u i) (w j) = 0 := by
    rw [hg, map_zero, LinearMap.zero_apply]
  rw [map_sum, LinearMap.sum_apply] at h1
  simp only [map_smul, LinearMap.smul_apply, polarBilin_apply_apply, h, smul_eq_mul, mul_ite,
    mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h1
  exact h1

theorem linIndep_pair {v : Fin (2 * 4) → K} (hQ : coordinateQuadPlus 4 K v = 1)
    (hv : act x (act x v) = act x v + v) : LinearIndependent K ![v, act x v] := by
  have h1 := polar_v_act_v hQ hv
  have h2 : polar (coordinateQuadPlus 4 K) (act x v) v = 1 := by rw [polar_comm, h1]
  refine linIndep_of_dual (w := ![act x v, v]) fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [h1, h2, CharTwo.two_eq_zero]

end Plane

section Norm

variable [CharP K 2] {x : Om8 K}

omit [CharP K 2] in
theorem eq_one_of_act (h : ∀ y, act x y = y) : x = 1 := by
  apply Subtype.ext
  apply Units.ext
  apply Matrix.toLin'.injective
  refine LinearMap.ext fun y => ?_
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply]
  exact (h y).trans (by rw [Subgroup.coe_one, Units.val_one, Matrix.one_mulVec])

theorem exists_range_Q_ne_zero (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) :
    ∃ y, coordinateQuadPlus 4 K (act x y - y) ≠ 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨y₀, hy₀⟩ : ∃ y₀, act x y₀ ≠ y₀ := by
    by_contra h
    push Not at h
    exact hx1 (eq_one_of_act h)
  apply hy₀
  rw [← sub_eq_zero]
  have hnd := (regular_coordinateQuadPlus 4 K (by norm_num)).1
  refine hnd.1 _ fun z => ?_
  rw [polarBilin_apply_apply, decomp (x := x) z, polar_add_right, polar_comm,
    polar_fix_range (act_fixPart hx3 z), zero_add]
  have e : act x y₀ - y₀ + (act x (act x z) - act x z) =
      act x (y₀ + act x z) - (y₀ + act x z) := by
    rw [act_add]
    abel
  rw [polar, e, hcon, hcon, hcon, sub_zero, sub_zero]

theorem exists_range_Q_one [Finite K] (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) :
    ∃ y, coordinateQuadPlus 4 K (act x y - y) = 1 := by
  obtain ⟨y, hy⟩ := exists_range_Q_ne_zero hx3 hx1
  obtain ⟨t, ht⟩ := isSquare_of_charTwo' (coordinateQuadPlus 4 K (act x y - y))⁻¹
  refine ⟨t • y, ?_⟩
  rw [act_smul, ← smul_sub, QuadraticMap.map_smul, smul_eq_mul, ← ht, inv_mul_cancel₀ hy]

end Norm

section C1

variable [CharP K 2] {x : Om8 K}

omit [CharP K 2] in
theorem omFixDim_one : omFixDim (1 : Om8 K) = 8 := by
  rw [omFixDim, fixDim, map_one, sub_self, LinearMap.ker_zero, finrank_top, Module.finrank_fin_fun]

theorem range_eq_span (hx3 : x ^ 3 = 1) (hd : omFixDim x = 6) {y₁ : Fin (2 * 4) → K}
    (hQ : coordinateQuadPlus 4 K (act x y₁ - y₁) = 1) :
    LinearMap.range (omRep x - 1) =
      Submodule.span K (Set.range ![act x y₁ - y₁, act x (act x y₁ - y₁)]) := by
  have hv := act_sq_of_range hx3 y₁
  have hrn := LinearMap.finrank_range_add_finrank_ker (omRep x - 1)
  rw [Module.finrank_fin_fun] at hrn
  have hsp := finrank_span_eq_card (linIndep_pair hQ hv)
  rw [Fintype.card_fin] at hsp
  have hle : Submodule.span K (Set.range ![act x y₁ - y₁, act x (act x y₁ - y₁)]) ≤
      LinearMap.range (omRep x - 1) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact ⟨y₁, rfl⟩
    · refine ⟨act x y₁, ?_⟩
      change act x (act x y₁) - act x y₁ = act x (act x y₁ - y₁)
      rw [act_sub]
  refine (Submodule.eq_of_le_of_finrank_eq hle ?_).symm
  have : finrank K (LinearMap.ker (omRep x - 1)) = 6 := hd
  omega

theorem fixed_of_orth (hx3 : x ^ 3 = 1) (hd : omFixDim x = 6) {y₁ : Fin (2 * 4) → K}
    (hQ : coordinateQuadPlus 4 K (act x y₁ - y₁) = 1) {w : Fin (2 * 4) → K}
    (h1 : polar (coordinateQuadPlus 4 K) w (act x y₁ - y₁) = 0)
    (h2 : polar (coordinateQuadPlus 4 K) w (act x (act x y₁ - y₁)) = 0) : act x w = w := by
  set v := act x y₁ - y₁ with hvdef
  have hv := act_sq_of_range hx3 y₁
  have hvv := polar_v_act_v hQ hv
  have hxvv : polar (coordinateQuadPlus 4 K) (act x v) v = 1 := by rw [polar_comm, hvv]
  set c := w + act x w + act x (act x w)
  have hc : act x c = c := act_fixPart hx3 w
  have hcv : polar (coordinateQuadPlus 4 K) c v = 0 := polar_fix_range hc y₁
  have hcxv : polar (coordinateQuadPlus 4 K) c (act x v) = 0 := by
    rw [hvdef, act_sub]
    exact polar_fix_range hc (act x y₁)
  have hp : act x (act x w) - act x w ∈ LinearMap.range (omRep x - 1) := ⟨act x w, rfl⟩
  rw [range_eq_span hx3 hd hQ, Submodule.mem_span_range_iff_exists_fun] at hp
  obtain ⟨a, ha⟩ := hp
  rw [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at ha
  have hw : w = c + (act x (act x w) - act x w) := decomp w
  have e1 : polar (coordinateQuadPlus 4 K) (act x (act x w) - act x w) v = 0 := by
    have := congrArg (fun y => polar (coordinateQuadPlus 4 K) y v) hw
    simp only [polar_add_left, hcv, zero_add] at this
    rw [← this, h1]
  have e2 : polar (coordinateQuadPlus 4 K) (act x (act x w) - act x w) (act x v) = 0 := by
    have := congrArg (fun y => polar (coordinateQuadPlus 4 K) y (act x v)) hw
    simp only [polar_add_left, hcxv, zero_add] at this
    rw [← this, h2]
  rw [← ha, polar_add_left, polar_smul_left, polar_smul_left, polar_self_zero, hxvv,
    smul_eq_mul, smul_eq_mul, mul_zero, zero_add, mul_one] at e1
  rw [← ha, polar_add_left, polar_smul_left, polar_smul_left, polar_self_zero, hvv,
    smul_eq_mul, smul_eq_mul, mul_zero, add_zero, mul_one] at e2
  rw [e1, e2, zero_smul, zero_smul, add_zero] at ha
  rw [← ha, add_zero] at hw
  rw [hw]
  exact hc

end C1

section C1Conj

variable [Finite K] [CharP K 2]

omit [Finite K] [CharP K 2] in
theorem symm_mulVec (g : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K)) (y : Fin (2 * 4) → K) :
    (matrixLinearIso.symm g : GL (Fin (2 * 4)) K).val *ᵥ y = g y := by
  rw [← matrixLinearIso_apply, MulEquiv.apply_symm_apply]

omit [Finite K] [CharP K 2] in
theorem symm_mem_isometries {g : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K)}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup (coordinateQuadPlus 4 K)) :
    matrixLinearIso.symm g ∈ matrixIsometries (coordinateQuadPlus 4 K) := by
  change matrixLinearIso (matrixLinearIso.symm g) ∈
    TauCeti.QuadraticMap.orthogonalGroup (coordinateQuadPlus 4 K)
  rw [MulEquiv.apply_symm_apply]
  exact hg

omit [Finite K] [CharP K 2] in
theorem gl_eq_of_mulVec {A B : GL (Fin (2 * 4)) K} (h : ∀ y, A.val *ᵥ y = B.val *ᵥ y) : A = B := by
  apply Units.ext
  apply Matrix.toLin'.injective
  exact LinearMap.ext fun y => by rw [Matrix.toLin'_apply, Matrix.toLin'_apply, h]

omit [Finite K] in
theorem reflMat_comm {z : Om8 K} {u : Fin (2 * 4) → K} (hu : coordinateQuadPlus 4 K u = 1)
    (hu0 : coordinateQuadPlus 4 K u ≠ 0) (hzu : act z u = u) :
    reflMat (coordinateQuadPlus 4 K) u hu0 * (z : GL (Fin (2 * 4)) K) =
      (z : GL (Fin (2 * 4)) K) * reflMat (coordinateQuadPlus 4 K) u hu0 := by
  refine gl_eq_of_mulVec fun y => ?_
  rw [Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    reflMat_mulVec_one u hu hu0, reflMat_mulVec_one u hu hu0]
  change act z y + polar (coordinateQuadPlus 4 K) u (act z y) • u =
    act z (y + polar (coordinateQuadPlus 4 K) u y • u)
  have h := polar_act z u y
  rw [hzu] at h
  rw [act_add, act_smul, hzu, h]

theorem exists_conj_of_C1 {x z : Om8 K} (hx3 : x ^ 3 = 1) (hz3 : z ^ 3 = 1)
    (hdx : omFixDim x = 6) (hdz : omFixDim z = 6) {u : Fin (2 * 4) → K}
    (hu : coordinateQuadPlus 4 K u = 1) (hzu : act z u = u) : ∃ h : Om8 K, x = h * z * h⁻¹ := by
  have hne : ∀ {w : Om8 K}, omFixDim w = 6 → w ≠ 1 := fun hw h1 => by
    rw [h1, omFixDim_one] at hw
    omega
  obtain ⟨y₁, hy₁⟩ := exists_range_Q_one hx3 (hne hdx)
  obtain ⟨y₀, hy₀⟩ := exists_range_Q_one hz3 (hne hdz)
  set v := act x y₁ - y₁ with hvdef
  set v₀ := act z y₀ - y₀ with hv₀def
  have hv := act_sq_of_range hx3 y₁
  have hv₀ := act_sq_of_range hz3 y₀
  have hnd := (regular_coordinateQuadPlus 4 K (by norm_num)).1
  have hT := (regular_coordinateQuadPlus 4 K (by norm_num)).2
  obtain ⟨g, hgO, hg⟩ := CFSG.RankThree.OrthogonalInvolutions.exists_mem_orthogonalGroup_apply_eq
    hnd ![v₀, act z v₀] ![v, act x v] (linIndep_pair hy₀ hv₀) (linIndep_pair hy₁ hv)
    (fun i => by
      fin_cases i
      · change coordinateQuadPlus 4 K v = coordinateQuadPlus 4 K v₀
        rw [hy₁, hy₀]
      · change coordinateQuadPlus 4 K (act x v) = coordinateQuadPlus 4 K (act z v₀)
        rw [Q_act, Q_act, hy₁, hy₀])
    (fun i j => by
      fin_cases i <;> fin_cases j
      · change polar (coordinateQuadPlus 4 K) v v = polar (coordinateQuadPlus 4 K) v₀ v₀
        rw [polar_self_zero, polar_self_zero]
      · change polar (coordinateQuadPlus 4 K) v (act x v) =
          polar (coordinateQuadPlus 4 K) v₀ (act z v₀)
        rw [polar_v_act_v hy₁ hv, polar_v_act_v hy₀ hv₀]
      · change polar (coordinateQuadPlus 4 K) (act x v) v =
          polar (coordinateQuadPlus 4 K) (act z v₀) v₀
        rw [polar_comm, polar_v_act_v hy₁ hv, polar_comm, polar_v_act_v hy₀ hv₀]
      · change polar (coordinateQuadPlus 4 K) (act x v) (act x v) =
          polar (coordinateQuadPlus 4 K) (act z v₀) (act z v₀)
        rw [polar_self_zero, polar_self_zero])
  have hg0 : g v₀ = v := hg 0
  have hg1 : g (act z v₀) = act x v := hg 1
  have hgpol : ∀ a b, polar (coordinateQuadPlus 4 K) (g a) (g b) =
      polar (coordinateQuadPlus 4 K) a b :=
    TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hgO
  have key : ∀ y, act x (g y) = g (act z y) := by
    intro y
    set c := y + act z y + act z (act z y)
    have hc : act z c = c := act_fixPart hz3 y
    have hyd : y = c + (act z (act z y) - act z y) := decomp y
    have hgc : act x (g c) = g c := by
      refine fixed_of_orth hx3 hdx hy₁ ?_ ?_
      · rw [← hvdef, ← hg0, hgpol]
        exact polar_fix_range hc y₀
      · rw [← hvdef, ← hg1, hgpol, hv₀def, act_sub]
        exact polar_fix_range hc (act z y₀)
    have hp : act z (act z y) - act z y ∈ LinearMap.range (omRep z - 1) := ⟨act z y, rfl⟩
    rw [range_eq_span hz3 hdz hy₀, Submodule.mem_span_range_iff_exists_fun] at hp
    obtain ⟨a, ha⟩ := hp
    rw [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      ← hv₀def] at ha
    have hgp : act x (g (act z (act z y) - act z y)) = g (act z (act z (act z y) - act z y)) := by
      rw [← ha, map_add, map_smul, map_smul, hg0, hg1, act_add, act_smul, act_smul, hv, act_add,
        act_smul, act_smul, hv₀, map_add, map_smul, map_smul, map_add, hg0, hg1]
    calc act x (g y) = act x (g c) + act x (g (act z (act z y) - act z y)) := by
          rw [← act_add, ← map_add, ← hyd]
      _ = g (act z c) + g (act z (act z (act z y) - act z y)) := by rw [hgc, hgp, hc]
      _ = g (act z y) := by rw [← map_add, ← act_add, ← hyd]
  set G := matrixLinearIso.symm g
  have hGI := symm_mem_isometries hgO
  have hunit : (x : GL (Fin (2 * 4)) K) * G = G * (z : GL (Fin (2 * 4)) K) := by
    refine gl_eq_of_mulVec fun y => ?_
    rw [Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, symm_mulVec,
      symm_mulVec]
    exact key y
  have hu0 : coordinateQuadPlus 4 K u ≠ 0 := by rw [hu]; exact one_ne_zero
  rcases mem_or_mul_reflMat_mem hnd hT hGI u hu0 with hGΩ | hGrΩ
  · refine ⟨⟨G, hGΩ⟩, Subtype.ext ?_⟩
    change (x : GL (Fin (2 * 4)) K) = G * (z : GL (Fin (2 * 4)) K) * G⁻¹
    exact eq_mul_inv_of_mul_eq hunit
  · refine ⟨⟨G * reflMat (coordinateQuadPlus 4 K) u hu0, hGrΩ⟩, Subtype.ext ?_⟩
    change (x : GL (Fin (2 * 4)) K) = G * reflMat (coordinateQuadPlus 4 K) u hu0 *
      (z : GL (Fin (2 * 4)) K) * (G * reflMat (coordinateQuadPlus 4 K) u hu0)⁻¹
    calc (x : GL (Fin (2 * 4)) K) = G * (z : GL (Fin (2 * 4)) K) * G⁻¹ :=
          eq_mul_inv_of_mul_eq hunit
      _ = G * (reflMat (coordinateQuadPlus 4 K) u hu0 * (z : GL (Fin (2 * 4)) K)) *
          (G * reflMat (coordinateQuadPlus 4 K) u hu0)⁻¹ := by
          rw [reflMat_comm hu hu0 hzu, mul_inv_rev]
          group
      _ = _ := by group

end C1Conj

section Frame

variable [CharP K 2] {x : Om8 K}

@[expose] def IsFrame (x : Om8 K) {k : ℕ} (v : Fin k → Fin (2 * 4) → K) : Prop :=
  (∀ i, coordinateQuadPlus 4 K (v i) = 1) ∧
    ∀ i j, i ≠ j → polar (coordinateQuadPlus 4 K) (v i) (v j) = 0 ∧
      polar (coordinateQuadPlus 4 K) (v i) (act x (v j)) = 0

theorem polar_act_right (hx3 : x ^ 3 = 1) (hfree : ∀ y, act x y = y → y = 0)
    (a b : Fin (2 * 4) → K) :
    polar (coordinateQuadPlus 4 K) a (act x b) =
      polar (coordinateQuadPlus 4 K) (act x a) b + polar (coordinateQuadPlus 4 K) a b := by
  rw [← polar_act x a (act x b), act_sq_of_free hx3 hfree b, polar_add_right, polar_act, add_comm]

@[expose] noncomputable def frameProj (x : Om8 K) {k : ℕ} (v : Fin k → Fin (2 * 4) → K)
    (y : Fin (2 * 4) → K) : Fin (2 * 4) → K :=
  y - ∑ j, (polar (coordinateQuadPlus 4 K) y (act x (v j)) • v j +
    polar (coordinateQuadPlus 4 K) y (v j) • act x (v j))

omit [CharP K 2] in
theorem frameProj_sub {k : ℕ} (v : Fin k → Fin (2 * 4) → K) (y : Fin (2 * 4) → K) :
    y - frameProj x v y = ∑ j, (polar (coordinateQuadPlus 4 K) y (act x (v j)) • v j +
      polar (coordinateQuadPlus 4 K) y (v j) • act x (v j)) := by
  rw [frameProj, sub_sub_cancel]

omit [CharP K 2] in
theorem polar_frame_sum {k : ℕ} (v : Fin k → Fin (2 * 4) → K) (a b : Fin k → K)
    (w : Fin (2 * 4) → K) :
    polar (coordinateQuadPlus 4 K) (∑ j, (a j • v j + b j • act x (v j))) w =
      ∑ j, (a j * polar (coordinateQuadPlus 4 K) (v j) w +
        b j * polar (coordinateQuadPlus 4 K) (act x (v j)) w) := by
  have h : polar (coordinateQuadPlus 4 K) (∑ j, (a j • v j + b j • act x (v j))) w =
      polarBilin (coordinateQuadPlus 4 K) (∑ j, (a j • v j + b j • act x (v j))) w := rfl
  rw [h, map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_add, map_smul, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    LinearMap.smul_apply, polarBilin_apply_apply, polarBilin_apply_apply, smul_eq_mul, smul_eq_mul]

theorem polar_frameProj (hx3 : x ^ 3 = 1) (hfree : ∀ y, act x y = y → y = 0) {k : ℕ}
    {v : Fin k → Fin (2 * 4) → K} (hv : IsFrame x v) (y : Fin (2 * 4) → K) (i : Fin k) :
    polar (coordinateQuadPlus 4 K) (frameProj x v y) (v i) = 0 ∧
      polar (coordinateQuadPlus 4 K) (frameProj x v y) (act x (v i)) = 0 := by
  have hvx : ∀ j, polar (coordinateQuadPlus 4 K) (v j) (act x (v j)) = 1 := fun j =>
    polar_v_act_v (hv.1 j) (act_sq_of_free hx3 hfree (v j))
  have h1 : ∀ j, polar (coordinateQuadPlus 4 K) (v j) (v i) = 0 := by
    intro j
    by_cases hji : j = i
    · rw [hji, polar_self_zero]
    · exact (hv.2 j i hji).1
  have h2 : ∀ j, polar (coordinateQuadPlus 4 K) (act x (v j)) (v i) =
      if j = i then 1 else 0 := by
    intro j
    split_ifs with hji
    · rw [hji, polar_comm, hvx]
    · rw [polar_comm]
      exact (hv.2 i j (Ne.symm hji)).2
  have h3 : ∀ j, polar (coordinateQuadPlus 4 K) (v j) (act x (v i)) =
      if j = i then 1 else 0 := by
    intro j
    split_ifs with hji
    · rw [hji, hvx]
    · exact (hv.2 j i hji).2
  have h4 : ∀ j, polar (coordinateQuadPlus 4 K) (act x (v j)) (act x (v i)) = 0 := by
    intro j
    rw [polar_act]
    exact h1 j
  constructor
  · rw [frameProj, polar_sub_left, polar_frame_sum]
    simp only [h1, h2, mul_zero, zero_add, mul_ite, mul_one, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true, sub_self]
  · rw [frameProj, polar_sub_left, polar_frame_sum]
    simp only [h3, h4, mul_zero, add_zero, mul_ite, mul_one, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true, sub_self]

omit [CharP K 2] in
theorem frameProj_add {k : ℕ} (v : Fin k → Fin (2 * 4) → K) (y z : Fin (2 * 4) → K) :
    frameProj x v (y + z) = frameProj x v y + frameProj x v z := by
  simp only [frameProj, polar_add_left, add_smul, Finset.sum_add_distrib]
  abel

theorem exists_frame_ext [Finite K] (hx3 : x ^ 3 = 1) (hfree : ∀ y, act x y = y → y = 0)
    {k : ℕ} (hk : k < 4) {v : Fin k → Fin (2 * 4) → K} (hv : IsFrame x v) :
    ∃ w, coordinateQuadPlus 4 K w = 1 ∧ ∀ j, polar (coordinateQuadPlus 4 K) w (v j) = 0 ∧
      polar (coordinateQuadPlus 4 K) w (act x (v j)) = 0 := by
  have hnd := (regular_coordinateQuadPlus 4 K (by norm_num)).1
  obtain ⟨y, hy⟩ : ∃ y, coordinateQuadPlus 4 K (frameProj x v y) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hzero : ∀ y, frameProj x v y = 0 := by
      intro y
      refine hnd.1 _ fun z => ?_
      rw [polarBilin_apply_apply]
      have hz : z = frameProj x v z + (z - frameProj x v z) := by abel
      rw [hz, polar_add_right, frameProj_sub]
      have e1 : polar (coordinateQuadPlus 4 K) (frameProj x v y) (frameProj x v z) = 0 := by
        rw [polar, ← frameProj_add, hcon, hcon, hcon, sub_zero, sub_zero]
      have e2 : polar (coordinateQuadPlus 4 K) (frameProj x v y)
          (∑ j, (polar (coordinateQuadPlus 4 K) z (act x (v j)) • v j +
            polar (coordinateQuadPlus 4 K) z (v j) • act x (v j))) = 0 := by
        rw [polar_comm, polar_frame_sum]
        refine Finset.sum_eq_zero fun j _ => ?_
        rw [polar_comm _ (v j) (frameProj x v y), (polar_frameProj hx3 hfree hv y j).1,
          polar_comm _ (act x (v j)) (frameProj x v y), (polar_frameProj hx3 hfree hv y j).2,
          mul_zero, mul_zero, add_zero]
      rw [e1, e2, zero_add]
    set f : Fin k × Fin 2 → Fin (2 * 4) → K := fun p => ![v p.1, act x (v p.1)] p.2
    have htop : Submodule.span K (Set.range f) = ⊤ := by
      rw [eq_top_iff]
      intro y _
      have hy' : y = y - frameProj x v y := by rw [hzero, sub_zero]
      rw [hy', frameProj_sub]
      refine Submodule.sum_mem _ fun j _ => Submodule.add_mem _ ?_ ?_
      · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(j, 0), rfl⟩)
      · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(j, 1), rfl⟩)
    have hle := finrank_range_le_card (R := K) f
    rw [Set.finrank, htop, finrank_top, Module.finrank_fin_fun, Fintype.card_prod,
      Fintype.card_fin, Fintype.card_fin] at hle
    omega
  obtain ⟨t, ht⟩ := isSquare_of_charTwo' (coordinateQuadPlus 4 K (frameProj x v y))⁻¹
  refine ⟨t • frameProj x v y, ?_, fun j => ?_⟩
  · rw [QuadraticMap.map_smul, smul_eq_mul, ← ht, inv_mul_cancel₀ hy]
  · rw [polar_smul_left, polar_smul_left, (polar_frameProj hx3 hfree hv y j).1,
      (polar_frameProj hx3 hfree hv y j).2, smul_zero]
    exact ⟨rfl, rfl⟩

theorem exists_frame [Finite K] (hx3 : x ^ 3 = 1) (hfree : ∀ y, act x y = y → y = 0) :
    ∀ k, k ≤ 4 → ∃ v : Fin k → Fin (2 * 4) → K, IsFrame x v := by
  intro k
  induction k with
  | zero => exact fun _ => ⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0⟩
  | succ k ih =>
    intro hk
    obtain ⟨v, hv⟩ := ih (by omega)
    obtain ⟨w, hw1, hw⟩ := exists_frame_ext hx3 hfree (by omega) hv
    refine ⟨Fin.snoc v w, fun i => ?_, fun i j hij => ?_⟩
    · induction i using Fin.lastCases with
      | last => rw [Fin.snoc_last]; exact hw1
      | cast i => rw [Fin.snoc_castSucc]; exact hv.1 i
    · induction i using Fin.lastCases with
      | last =>
        induction j using Fin.lastCases with
        | last => exact absurd rfl hij
        | cast j => rw [Fin.snoc_last, Fin.snoc_castSucc]; exact hw j
      | cast i =>
        induction j using Fin.lastCases with
        | last =>
          rw [Fin.snoc_last, Fin.snoc_castSucc]
          refine ⟨by rw [polar_comm]; exact (hw i).1, ?_⟩
          rw [polar_act_right hx3 hfree, polar_comm, (hw i).2, polar_comm, (hw i).1, add_zero]
        | cast j =>
          rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
          exact hv.2 i j fun h => hij (by rw [h])

end Frame

end D4Rank

end CFSG.StandardType
