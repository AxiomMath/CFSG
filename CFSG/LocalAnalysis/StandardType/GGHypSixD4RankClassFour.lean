module

public import CFSG.LocalAnalysis.StandardType.GGHypSixD4RankClassConj

public section

namespace CFSG.StandardType

namespace D4Rank

open Module CFSG.StandardType.Triality CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData CFSG.LieType.Universal.Spin
  CFSG.RankThree.PartOne.AUTSL QuadraticMap
open scoped Matrix

variable {K : Type} [Field K]

section Fam

variable [CharP K 2] {x : Om8 K}

@[expose] noncomputable def frameFam (x : Om8 K) (v : Fin 4 → Fin (2 * 4) → K)
    (p : Fin 4 × Fin 2) : Fin (2 * 4) → K :=
  ![v p.1, act x (v p.1)] p.2

theorem polar_frameFam (hx3 : x ^ 3 = 1) (hfree : ∀ y, act x y = y → y = 0)
    {v : Fin 4 → Fin (2 * 4) → K} (hv : IsFrame x v) (p q : Fin 4 × Fin 2) :
    polar (coordinateQuadPlus 4 K) (frameFam x v p) (frameFam x v q) =
      if p.1 = q.1 ∧ p.2 ≠ q.2 then 1 else 0 := by
  have hvx : ∀ j, polar (coordinateQuadPlus 4 K) (v j) (act x (v j)) = 1 := fun j =>
    polar_v_act_v (hv.1 j) (act_sq_of_free hx3 hfree (v j))
  have h00 : ∀ i j, polar (coordinateQuadPlus 4 K) (v i) (v j) = 0 := by
    intro i j
    by_cases hij : i = j
    · rw [hij, polar_self_zero]
    · exact (hv.2 i j hij).1
  have h01 : ∀ i j, polar (coordinateQuadPlus 4 K) (v i) (act x (v j)) =
      if i = j then 1 else 0 := by
    intro i j
    split_ifs with hij
    · rw [hij, hvx]
    · exact (hv.2 i j hij).2
  obtain ⟨i, a⟩ := p
  obtain ⟨j, b⟩ := q
  fin_cases a <;> fin_cases b
  · simp [frameFam, h00]
  · simp [frameFam, h01]
  · simp only [frameFam]
    simp [polar_comm _ (act x (v i)) (v j), h01, eq_comm]
  · show polar _ (act x (v i)) (act x (v j)) = _
    rw [polar_act, h00]
    simp

theorem linIndep_frameFam (hx3 : x ^ 3 = 1) (hfree : ∀ y, act x y = y → y = 0)
    {v : Fin 4 → Fin (2 * 4) → K} (hv : IsFrame x v) : LinearIndependent K (frameFam x v) := by
  refine linIndep_of_dual (w := fun q => frameFam x v (q.1, Fin.rev q.2)) fun p q => ?_
  rw [polar_frameFam hx3 hfree hv]
  obtain ⟨i, a⟩ := p
  obtain ⟨j, b⟩ := q
  fin_cases a <;> fin_cases b <;> simp [Prod.ext_iff]

omit [CharP K 2] in
theorem Q_frameFam {v : Fin 4 → Fin (2 * 4) → K} (hv : IsFrame x v) (p : Fin 4 × Fin 2) :
    coordinateQuadPlus 4 K (frameFam x v p) = 1 := by
  obtain ⟨i, a⟩ := p
  fin_cases a
  · exact hv.1 i
  · change coordinateQuadPlus 4 K (act x (v i)) = 1
    rw [Q_act]
    exact hv.1 i

end Fam

section C4

variable [Finite K] [CharP K 2]

theorem exists_conj_of_C4 {x z : Om8 K} (hx3 : x ^ 3 = 1) (hz3 : z ^ 3 = 1)
    (hfx : ∀ y, act x y = y → y = 0) (hfz : ∀ y, act z y = y → y = 0) :
    ∃ h : Om8 K, x = h * z * h⁻¹ ∨ x = h * AutOm.plusRefl one_le_four z * h⁻¹ := by
  obtain ⟨vx, hvx⟩ := exists_frame hx3 hfx 4 le_rfl
  obtain ⟨vz, hvz⟩ := exists_frame hz3 hfz 4 le_rfl
  have hnd := (regular_coordinateQuadPlus 4 K (by norm_num)).1
  have hT := (regular_coordinateQuadPlus 4 K (by norm_num)).2
  set e : Fin 4 × Fin 2 ≃ Fin (4 * 2) := finProdFinEquiv
  have hix : LinearIndependent K (frameFam x vx ∘ e.symm) :=
    (linIndep_frameFam hx3 hfx hvx).comp _ e.symm.injective
  have hiz : LinearIndependent K (frameFam z vz ∘ e.symm) :=
    (linIndep_frameFam hz3 hfz hvz).comp _ e.symm.injective
  obtain ⟨g, hgO, hg⟩ := CFSG.RankThree.OrthogonalInvolutions.exists_mem_orthogonalGroup_apply_eq
    hnd (frameFam z vz ∘ e.symm) (frameFam x vx ∘ e.symm) hiz hix
    (fun a => by simp only [Function.comp, Q_frameFam hvx, Q_frameFam hvz])
    (fun a b => by
      simp only [Function.comp, polar_frameFam hx3 hfx hvx, polar_frameFam hz3 hfz hvz])
  have hg' : ∀ p, g (frameFam z vz p) = frameFam x vx p := fun p => by
    have := hg (e p)
    simpa only [Function.comp, Equiv.symm_apply_apply] using this
  have hspan : Submodule.span K (Set.range (frameFam z vz ∘ e.symm)) = ⊤ :=
    hiz.span_eq_top_of_card_eq_finrank' (by rw [Fintype.card_fin, Module.finrank_fin_fun])
  have key : (omRep x).comp g.toLinearMap = g.toLinearMap.comp (omRep z) := by
    refine LinearMap.ext_on_range hspan fun a => ?_
    obtain ⟨⟨i, b⟩, rfl⟩ := e.surjective a
    simp only [Function.comp, Equiv.symm_apply_apply, LinearMap.comp_apply, LinearEquiv.coe_coe]
    have h0 := hg' (i, 0)
    have h1 := hg' (i, 1)
    change g (vz i) = vx i at h0
    change g (act z (vz i)) = act x (vx i) at h1
    fin_cases b
    · change act x (g (vz i)) = g (act z (vz i))
      rw [h0, h1]
    · change act x (g (act z (vz i))) = g (act z (act z (vz i)))
      rw [h1, act_sq_of_free hz3 hfz, map_add, h1, h0, act_sq_of_free hx3 hfx]
  set G := matrixLinearIso.symm g
  have hGI := symm_mem_isometries hgO
  have hunit : (x : GL (Fin (2 * 4)) K) * G = G * (z : GL (Fin (2 * 4)) K) := by
    refine gl_eq_of_mulVec fun y => ?_
    rw [Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, symm_mulVec,
      symm_mulVec]
    exact LinearMap.congr_fun key y
  set w := CFSG.SeitzReduction.OmegaPilot.plusUnitVector (F := K) one_le_four
  have hw0 : coordinateQuadPlus 4 K w ≠ 0 := AutOm.plusUnitVector_form_ne_zero one_le_four
  rcases mem_or_mul_reflMat_mem hnd hT hGI w hw0 with hGΩ | hGrΩ
  · exact ⟨⟨G, hGΩ⟩, Or.inl (Subtype.ext (eq_mul_inv_of_mul_eq hunit))⟩
  · refine ⟨⟨G * reflMat (coordinateQuadPlus 4 K) w hw0, hGrΩ⟩, Or.inr (Subtype.ext ?_)⟩
    have hr := reflMat_mul_self (Q := coordinateQuadPlus 4 K) w hw0
    have hri : (reflMat (coordinateQuadPlus 4 K) w hw0)⁻¹ =
        reflMat (coordinateQuadPlus 4 K) w hw0 := inv_eq_of_mul_eq_one_right hr
    change (x : GL (Fin (2 * 4)) K) = G * reflMat (coordinateQuadPlus 4 K) w hw0 *
      (reflAut (coordinateQuadPlus 4 K) w hw0 z : GL (Fin (2 * 4)) K) *
        (G * reflMat (coordinateQuadPlus 4 K) w hw0)⁻¹
    rw [reflAut_apply_val, hri, mul_inv_rev, hri, eq_mul_inv_of_mul_eq hunit]
    have e1 : G * reflMat (coordinateQuadPlus 4 K) w hw0 *
        (reflMat (coordinateQuadPlus 4 K) w hw0 * (z : GL (Fin (2 * 4)) K) *
          reflMat (coordinateQuadPlus 4 K) w hw0) * (reflMat (coordinateQuadPlus 4 K) w hw0 * G⁻¹) =
        G * (reflMat (coordinateQuadPlus 4 K) w hw0 * reflMat (coordinateQuadPlus 4 K) w hw0) *
          (z : GL (Fin (2 * 4)) K) *
          (reflMat (coordinateQuadPlus 4 K) w hw0 * reflMat (coordinateQuadPlus 4 K) w hw0) *
            G⁻¹ := by
      group
    rw [e1, hr, mul_one, mul_one]

end C4

end D4Rank

end CFSG.StandardType
