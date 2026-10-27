module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8SpinIso
public import CFSG.ClassicalInvolution.Solomon73.YamakiPres
public import CFSG.LieType.SpinGeom.FrameVec

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.LieType.SpinGeom CFSG.LieType.D4Small CFSG.StandardType.Triality
open QuadraticMap
open scoped Matrix

private abbrev sixteenC8SpinTrans_mat (h : Om8 (ZMod 2)) :
    Matrix (Fin (2 * 4)) (Fin (2 * 4)) (ZMod 2) :=
  ((h : GL (Fin (2 * 4)) (ZMod 2)) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) (ZMod 2))

private theorem sixteenC8SpinTrans_mat_unfold (h : Om8 (ZMod 2)) :
    sixteenC8SpinTrans_mat h = ((h : GL (Fin (2 * 4)) (ZMod 2)) :
      Matrix (Fin (2 * 4)) (Fin (2 * 4)) (ZMod 2)) := rfl

private theorem sixteenC8SpinTrans_zmod2_eq_one {t : ZMod 2} (h : t ≠ 0) : t = 1 := by
  have h1 : 0 < t.val := ZMod.val_pos.mpr h
  have h2 : t.val < 2 := ZMod.val_lt t
  have h3 : t.val = 1 := by omega
  exact (ZMod.val_eq_one (by norm_num) t).mp h3

private theorem sixteenC8SpinTrans_frameE_ne_zero (k : Fin 4) : frameE (ZMod 2) k ≠ 0 := by
  intro h
  have h1 := polar_frameE_frameF (K := ZMod 2) k k
  rw [h, polar_zero_left, if_pos rfl] at h1
  exact zero_ne_one h1

private theorem sixteenC8SpinTrans_frameF_ne_zero (k : Fin 4) : frameF (ZMod 2) k ≠ 0 := by
  intro h
  have h1 := polar_frameF_frameE (K := ZMod 2) k k
  rw [h, polar_zero_left, if_pos rfl] at h1
  exact zero_ne_one h1

set_option maxRecDepth 100000 in
private theorem sixteenC8SpinTrans_exists_sl_mulVec_eq (x x' : Fin 3 → ZMod 2)
    (hx : x ≠ 0) (hx' : x' ≠ 0) :
    ∃ g : Matrix (Fin 3) (Fin 3) (ZMod 2), g.det = 1 ∧ g *ᵥ x = x' := by
  classical
  decide +revert

set_option maxRecDepth 100000 in
private theorem sixteenC8SpinTrans_altMat_mulVec_surj (x' z : Fin 3 → ZMod 2)
    (hx' : x' ≠ 0) (hz : x' ⬝ᵥ z = 0) :
    ∃ m : Fin 3 → ZMod 2, CFSG.LieType.SpinGeom.altMat (ZMod 2) x' *ᵥ m = z := by
  classical
  decide +revert

set_option maxRecDepth 100000 in
private theorem sixteenC8SpinTrans_dot_surj (x' : Fin 3 → ZMod 2) (hx' : x' ≠ 0)
    (t : ZMod 2) : ∃ c : Fin 3 → ZMod 2, c ⬝ᵥ x' = t := by
  classical
  decide +revert

private theorem sixteenC8SpinTrans_polar_mulVec (h : Om8 (ZMod 2))
    (v w : Fin (2 * 4) → ZMod 2) :
    polar (coordinateQuadPlus 4 (ZMod 2))
        (sixteenC8SpinTrans_mat h *ᵥ v) (sixteenC8SpinTrans_mat h *ᵥ w) =
      polar (coordinateQuadPlus 4 (ZMod 2)) v w := by
  have hM : sixteenC8SpinTrans_mat h *ᵥ v + sixteenC8SpinTrans_mat h *ᵥ w =
      sixteenC8SpinTrans_mat h *ᵥ (v + w) := by
    rw [← Matrix.mulVec_add]
  have h1 : coordinateQuadPlus 4 (ZMod 2) (sixteenC8SpinTrans_mat h *ᵥ v) =
      coordinateQuadPlus 4 (ZMod 2) v := coordinateQuadPlus_mulVec_om8 h v
  have h2 : coordinateQuadPlus 4 (ZMod 2) (sixteenC8SpinTrans_mat h *ᵥ w) =
      coordinateQuadPlus 4 (ZMod 2) w := coordinateQuadPlus_mulVec_om8 h w
  have h3 : coordinateQuadPlus 4 (ZMod 2) (sixteenC8SpinTrans_mat h *ᵥ (v + w)) =
      coordinateQuadPlus 4 (ZMod 2) (v + w) := coordinateQuadPlus_mulVec_om8 h (v + w)
  calc polar (coordinateQuadPlus 4 (ZMod 2))
        (sixteenC8SpinTrans_mat h *ᵥ v) (sixteenC8SpinTrans_mat h *ᵥ w)
      = coordinateQuadPlus 4 (ZMod 2) (sixteenC8SpinTrans_mat h *ᵥ v +
            sixteenC8SpinTrans_mat h *ᵥ w) -
          coordinateQuadPlus 4 (ZMod 2) (sixteenC8SpinTrans_mat h *ᵥ v) -
          coordinateQuadPlus 4 (ZMod 2) (sixteenC8SpinTrans_mat h *ᵥ w) := rfl
    _ = coordinateQuadPlus 4 (ZMod 2) (sixteenC8SpinTrans_mat h *ᵥ (v + w)) -
          coordinateQuadPlus 4 (ZMod 2) (sixteenC8SpinTrans_mat h *ᵥ v) -
          coordinateQuadPlus 4 (ZMod 2) (sixteenC8SpinTrans_mat h *ᵥ w) :=
        congrArg (fun x => x - coordinateQuadPlus 4 (ZMod 2) (sixteenC8SpinTrans_mat h *ᵥ v) -
          coordinateQuadPlus 4 (ZMod 2) (sixteenC8SpinTrans_mat h *ᵥ w))
          (congrArg (coordinateQuadPlus 4 (ZMod 2)) hM)
    _ = coordinateQuadPlus 4 (ZMod 2) (sixteenC8SpinTrans_mat h *ᵥ (v + w)) -
          coordinateQuadPlus 4 (ZMod 2) v -
          coordinateQuadPlus 4 (ZMod 2) (sixteenC8SpinTrans_mat h *ᵥ w) :=
        congrArg (fun x => coordinateQuadPlus 4 (ZMod 2)
          (sixteenC8SpinTrans_mat h *ᵥ (v + w)) - x -
          coordinateQuadPlus 4 (ZMod 2) (sixteenC8SpinTrans_mat h *ᵥ w)) h1
    _ = coordinateQuadPlus 4 (ZMod 2) (sixteenC8SpinTrans_mat h *ᵥ (v + w)) -
          coordinateQuadPlus 4 (ZMod 2) v - coordinateQuadPlus 4 (ZMod 2) w :=
        congrArg (fun x => coordinateQuadPlus 4 (ZMod 2)
          (sixteenC8SpinTrans_mat h *ᵥ (v + w)) -
          coordinateQuadPlus 4 (ZMod 2) v - x) h2
    _ = coordinateQuadPlus 4 (ZMod 2) (v + w) -
          coordinateQuadPlus 4 (ZMod 2) v - coordinateQuadPlus 4 (ZMod 2) w :=
        congrArg (fun x => x - coordinateQuadPlus 4 (ZMod 2) v -
          coordinateQuadPlus 4 (ZMod 2) w) h3
    _ = polar (coordinateQuadPlus 4 (ZMod 2)) v w := rfl

private theorem sixteenC8SpinTrans_mat_mul_inv_mulVec (h : Om8 (ZMod 2))
    (v : Fin (2 * 4) → ZMod 2) :
    sixteenC8SpinTrans_mat h *ᵥ (sixteenC8SpinTrans_mat h⁻¹ *ᵥ v) = v := by
  rw [sixteenC8SpinTrans_mat_unfold]
  rw [Matrix.mulVec_mulVec]
  have hmul : ((h : GL (Fin (2 * 4)) (ZMod 2)) :
      Matrix (Fin (2 * 4)) (Fin (2 * 4)) (ZMod 2)) *
      (((h⁻¹ : Om8 (ZMod 2)) : GL (Fin (2 * 4)) (ZMod 2)) :
        Matrix (Fin (2 * 4)) (Fin (2 * 4)) (ZMod 2)) = 1 := by
    show (((h * h⁻¹ : Om8 (ZMod 2)) : GL (Fin (2 * 4)) (ZMod 2)) :
      Matrix (Fin (2 * 4)) (Fin (2 * 4)) (ZMod 2)) = 1
    rw [mul_inv_cancel]
    rfl
  rw [hmul, Matrix.one_mulVec]

private theorem sixteenC8SpinTrans_exists_singular_orthogonal (v : Fin (2 * 4) → ZMod 2)
    (hv : coordinateQuadPlus 4 (ZMod 2) v ≠ 0) :
    ∃ s : Fin (2 * 4) → ZMod 2,
      s ≠ 0 ∧ coordinateQuadPlus 4 (ZMod 2) s = 0 ∧
        polar (coordinateQuadPlus 4 (ZMod 2)) v s = 0 := by
  classical
  by_cases hy : ∃ k : Fin 4, coordY (ZMod 2) v k = 0
  · obtain ⟨k, hk⟩ := hy
    exact ⟨frameE (ZMod 2) k, sixteenC8SpinTrans_frameE_ne_zero k, quad_frameE k, hk⟩
  · have hy' : ∀ k : Fin 4, coordY (ZMod 2) v k ≠ 0 := fun k hk => hy ⟨k, hk⟩
    have hy1 : ∀ k : Fin 4, coordY (ZMod 2) v k = 1 := fun k =>
      sixteenC8SpinTrans_zmod2_eq_one (hy' k)
    have hsum : ∑ k : Fin 4, coordX (ZMod 2) v k = 1 := by
      have h := sixteenC8SpinTrans_zmod2_eq_one hv
      rw [quad_eq_sum] at h
      rw [Finset.sum_congr rfl (fun k _ => by rw [hy1 k, mul_one])] at h
      exact h
    have hx0 : ∃ k : Fin 4, coordX (ZMod 2) v k = 0 := by
      by_contra hcon
      have hx1 : ∀ k : Fin 4, coordX (ZMod 2) v k = 1 := fun k =>
        sixteenC8SpinTrans_zmod2_eq_one (fun hk => hcon ⟨k, hk⟩)
      have hzero : ∑ k : Fin 4, coordX (ZMod 2) v k = 0 := by
        rw [Finset.sum_congr rfl (fun k _ => hx1 k)]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
        decide
      rw [hzero] at hsum
      exact zero_ne_one hsum
    obtain ⟨k, hk⟩ := hx0
    exact ⟨frameF (ZMod 2) k, sixteenC8SpinTrans_frameF_ne_zero k, quad_frameF k, hk⟩

private theorem sixteenC8SpinTrans_stab_trans (v v' : Fin (2 * 4) → ZMod 2)
    (hQ : coordinateQuadPlus 4 (ZMod 2) v = 1)
    (hQ' : coordinateQuadPlus 4 (ZMod 2) v' = 1)
    (hy : coordY (ZMod 2) v 0 = 0) (hy' : coordY (ZMod 2) v' 0 = 0) :
    ∃ h ∈ spinSeven (ZMod 2), sixteenC8SpinTrans_mat h *ᵥ v = v' := by
  classical
  let x : Fin 3 → ZMod 2 := fun j => coordX (ZMod 2) v j.succ
  let y : Fin 3 → ZMod 2 := fun j => coordY (ZMod 2) v j.succ
  let x₀ : ZMod 2 := coordX (ZMod 2) v 0
  let x' : Fin 3 → ZMod 2 := fun j => coordX (ZMod 2) v' j.succ
  let y' : Fin 3 → ZMod 2 := fun j => coordY (ZMod 2) v' j.succ
  let x₀' : ZMod 2 := coordX (ZMod 2) v' 0
  have hdot : x ⬝ᵥ y = 1 := by
    have h := hQ
    rw [quad_eq_sum, Fin.sum_univ_succ] at h
    simp only [hy, mul_zero, zero_add] at h
    rw [← h]
    rfl
  have hdot' : x' ⬝ᵥ y' = 1 := by
    have h := hQ'
    rw [quad_eq_sum, Fin.sum_univ_succ] at h
    simp only [hy', mul_zero, zero_add] at h
    rw [← h]
    rfl
  have hx : x ≠ 0 := by
    intro hx0
    rw [hx0, zero_dotProduct] at hdot
    exact zero_ne_one hdot
  have hx' : x' ≠ 0 := by
    intro hx0
    rw [hx0, zero_dotProduct] at hdot'
    exact zero_ne_one hdot'
  obtain ⟨g, hgdet, hgx⟩ := sixteenC8SpinTrans_exists_sl_mulVec_eq x x' hx hx'
  have hcontra : x' ⬝ᵥ ((g.adjugate)ᵀ *ᵥ y) = x ⬝ᵥ y := by
    rw [← hgx, dotProduct_comm (g *ᵥ x) ((g.adjugate)ᵀ *ᵥ y),
      dot_contra_mulVec g hgdet y x]
    exact dotProduct_comm y x
  have hz : x' ⬝ᵥ (y' + (g.adjugate)ᵀ *ᵥ y) = 0 := by
    rw [dotProduct_add, hdot', hcontra, hdot]
    decide
  obtain ⟨m, hm⟩ :=
    sixteenC8SpinTrans_altMat_mulVec_surj x' (y' + (g.adjugate)ᵀ *ᵥ y) hx' hz
  have hmy : CFSG.LieType.SpinGeom.altMat (ZMod 2) m *ᵥ x' = y' + (g.adjugate)ᵀ *ᵥ y := by
    rw [CFSG.LieType.SpinGeom.altMat_mulVec_comm, hm]
  obtain ⟨c, hc⟩ :=
    sixteenC8SpinTrans_dot_surj x' hx' (x₀' + x₀ + m ⬝ᵥ ((g.adjugate)ᵀ *ᵥ y))
  obtain ⟨h, hh, hact⟩ := exists_mem_spinSeven_spinElt c m g hgdet
  refine ⟨h, hh, ?_⟩
  have hv : frameVec (ZMod 2) x₀ x y 0 = v := by
    rw [← frameVec_coords v, hy]
  have hv' : frameVec (ZMod 2) x₀' x' y' 0 = v' := by
    rw [← frameVec_coords v', hy']
  rw [sixteenC8SpinTrans_mat_unfold]
  rw [hact v, ← hv, ← hv', CFSG.LieType.SpinGeom.spinElt_frameVec]
  have e2 : g *ᵥ x + (0 : ZMod 2) • m = x' := by rw [hgx, zero_smul, add_zero]
  have e3 : (g.adjugate)ᵀ *ᵥ y + CFSG.LieType.SpinGeom.altMat (ZMod 2) m *ᵥ (g *ᵥ x) +
      (0 : ZMod 2) • c = y' := by
    rw [hgx, hmy, zero_smul, add_zero]
    rw [show (g.adjugate)ᵀ *ᵥ y + (y' + (g.adjugate)ᵀ *ᵥ y) =
        y' + ((g.adjugate)ᵀ *ᵥ y + (g.adjugate)ᵀ *ᵥ y) by abel]
    rw [CharTwo.add_self_eq_zero, add_zero]
  have e1 : x₀ + c ⬝ᵥ (g *ᵥ x) + m ⬝ᵥ ((g.adjugate)ᵀ *ᵥ y) + 0 * (c ⬝ᵥ m) = x₀' := by
    rw [hgx, hc, zero_mul, add_zero]
    rw [show x₀ + (x₀' + x₀ + m ⬝ᵥ ((g.adjugate)ᵀ *ᵥ y)) +
        m ⬝ᵥ ((g.adjugate)ᵀ *ᵥ y) =
        x₀' + (x₀ + x₀) + (m ⬝ᵥ ((g.adjugate)ᵀ *ᵥ y) +
          m ⬝ᵥ ((g.adjugate)ᵀ *ᵥ y)) by abel]
    rw [CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero]
    simp
  rw [e1]
  congr 1

private theorem sixteenC8SpinTrans_spinSeven_trans_nonsing (v v' : Fin (2 * 4) → ZMod 2)
    (hv : coordinateQuadPlus 4 (ZMod 2) v ≠ 0)
    (hv' : coordinateQuadPlus 4 (ZMod 2) v' ≠ 0) :
    ∃ h ∈ spinSeven (ZMod 2), sixteenC8SpinTrans_mat h *ᵥ v = v' := by
  have hQv : coordinateQuadPlus 4 (ZMod 2) v = 1 := sixteenC8SpinTrans_zmod2_eq_one hv
  have hQv' : coordinateQuadPlus 4 (ZMod 2) v' = 1 := sixteenC8SpinTrans_zmod2_eq_one hv'
  obtain ⟨s, hs0, hsQ, hsv⟩ := sixteenC8SpinTrans_exists_singular_orthogonal v hv
  obtain ⟨s', hs0', hsQ', hs'v'⟩ := sixteenC8SpinTrans_exists_singular_orthogonal v' hv'
  obtain ⟨hv1, hhv1, hsv1⟩ := spinSeven_transitive (ZMod 2) s hs0 hsQ
  obtain ⟨hw1, hhw1, hsw1⟩ := spinSeven_transitive (ZMod 2) s' hs0' hsQ'
  let v₁ : Fin (2 * 4) → ZMod 2 := sixteenC8SpinTrans_mat hv1⁻¹ *ᵥ v
  let w₁ : Fin (2 * 4) → ZMod 2 := sixteenC8SpinTrans_mat hw1⁻¹ *ᵥ v'
  have hQv₁ : coordinateQuadPlus 4 (ZMod 2) v₁ = 1 := by
    rw [show v₁ = sixteenC8SpinTrans_mat hv1⁻¹ *ᵥ v from rfl,
      sixteenC8SpinTrans_mat_unfold, coordinateQuadPlus_mulVec_om8, hQv]
  have hQw₁ : coordinateQuadPlus 4 (ZMod 2) w₁ = 1 := by
    rw [show w₁ = sixteenC8SpinTrans_mat hw1⁻¹ *ᵥ v' from rfl,
      sixteenC8SpinTrans_mat_unfold, coordinateQuadPlus_mulVec_om8, hQv']
  have hyv₁ : coordY (ZMod 2) v₁ 0 = 0 := by
    have h1 : sixteenC8SpinTrans_mat hv1 *ᵥ v₁ = v :=
      sixteenC8SpinTrans_mat_mul_inv_mulVec hv1 v
    have h2 : sixteenC8SpinTrans_mat hv1 *ᵥ frameE (ZMod 2) 0 = s := by
      rw [sixteenC8SpinTrans_mat_unfold]
      exact hsv1
    have hpol := sixteenC8SpinTrans_polar_mulVec hv1 v₁ (frameE (ZMod 2) 0)
    rw [h1, h2, hsv] at hpol
    exact hpol.symm
  have hyw₁ : coordY (ZMod 2) w₁ 0 = 0 := by
    have h1 : sixteenC8SpinTrans_mat hw1 *ᵥ w₁ = v' :=
      sixteenC8SpinTrans_mat_mul_inv_mulVec hw1 v'
    have h2 : sixteenC8SpinTrans_mat hw1 *ᵥ frameE (ZMod 2) 0 = s' := by
      rw [sixteenC8SpinTrans_mat_unfold]
      exact hsw1
    have hpol := sixteenC8SpinTrans_polar_mulVec hw1 w₁ (frameE (ZMod 2) 0)
    rw [h1, h2, hs'v'] at hpol
    exact hpol.symm
  obtain ⟨p, hp, hpv⟩ := sixteenC8SpinTrans_stab_trans v₁ w₁ hQv₁ hQw₁ hyv₁ hyw₁
  refine ⟨hw1 * p * hv1⁻¹, mul_mem (mul_mem hhw1 hp) (inv_mem hhv1), ?_⟩
  rw [show sixteenC8SpinTrans_mat (hw1 * p * hv1⁻¹) =
      sixteenC8SpinTrans_mat hw1 * sixteenC8SpinTrans_mat p * sixteenC8SpinTrans_mat hv1⁻¹
      from rfl]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  rw [show sixteenC8SpinTrans_mat hv1⁻¹ *ᵥ v = v₁ from rfl, hpv]
  exact sixteenC8SpinTrans_mat_mul_inv_mulVec hw1 v'

private theorem sixteenC8SpinTrans_card_nonzero_singular :
    Nat.card {v : Fin (2 * 4) → ZMod 2 //
      v ≠ 0 ∧ coordinateQuadPlus 4 (ZMod 2) v = 0} = 135 := by
  rw [card_nonzero_singular_eight, Nat.card_zmod]
  norm_num

private noncomputable def sixteenC8SpinTrans_zeroOrSing :
    {v : Fin (2 * 4) → ZMod 2 // coordinateQuadPlus 4 (ZMod 2) v = 0} ≃
      ({v : Fin (2 * 4) → ZMod 2 //
        v ≠ 0 ∧ coordinateQuadPlus 4 (ZMod 2) v = 0} ⊕ Unit) where
  toFun x := if h : (x : Fin (2 * 4) → ZMod 2) = 0 then Sum.inr ()
    else Sum.inl ⟨x.1, h, x.2⟩
  invFun y := match y with
    | Sum.inl z => ⟨z.1, z.2.2⟩
    | Sum.inr _ => ⟨0, by simp⟩
  left_inv x := by
    by_cases h : (x : Fin (2 * 4) → ZMod 2) = 0
    · dsimp only
      rw [dif_pos h]
      exact Subtype.ext h.symm
    · dsimp only
      rw [dif_neg h]
  right_inv y := by
    rcases y with z | u
    · dsimp only
      rw [dif_neg z.2.1]
    · dsimp only
      rw [dif_pos (rfl : (0 : Fin (2 * 4) → ZMod 2) = 0)]

private theorem sixteenC8SpinTrans_card_singular :
    Nat.card {v : Fin (2 * 4) → ZMod 2 //
      coordinateQuadPlus 4 (ZMod 2) v = 0} = 136 := by
  have hpunit : Nat.card PUnit = 1 := Nat.card_unique
  rw [Nat.card_congr sixteenC8SpinTrans_zeroOrSing, Nat.card_sum,
    sixteenC8SpinTrans_card_nonzero_singular, hpunit]

private theorem sixteenC8SpinTrans_card_nonsing :
    Nat.card {v : Fin (2 * 4) → ZMod 2 //
      coordinateQuadPlus 4 (ZMod 2) v ≠ 0} = 120 := by
  have hcompl := Set.ncard_compl
    (s := {v : Fin (2 * 4) → ZMod 2 | coordinateQuadPlus 4 (ZMod 2) v = 0})
  have htotal : Nat.card (Fin (2 * 4) → ZMod 2) = 256 := by
    rw [Nat.card_fun, Nat.card_fin, Nat.card_zmod]
    norm_num
  have hsing : ({v : Fin (2 * 4) → ZMod 2 |
      coordinateQuadPlus 4 (ZMod 2) v = 0} : Set _).ncard = 136 := by
    rw [← Nat.card_coe_set_eq]
    exact sixteenC8SpinTrans_card_singular
  have hset : ({v : Fin (2 * 4) → ZMod 2 |
      coordinateQuadPlus 4 (ZMod 2) v ≠ 0} : Set _) =
      ({v : Fin (2 * 4) → ZMod 2 | coordinateQuadPlus 4 (ZMod 2) v = 0} : Set _)ᶜ := by
    ext v
    simp
  rw [show Nat.card {v : Fin (2 * 4) → ZMod 2 //
        coordinateQuadPlus 4 (ZMod 2) v ≠ 0} =
      ({v : Fin (2 * 4) → ZMod 2 |
        coordinateQuadPlus 4 (ZMod 2) v ≠ 0} : Set _).ncard from Nat.card_coe_set_eq _,
    hset, hcompl, htotal, hsing]

private theorem sixteenC8SpinTrans_card_nonsing_spinW :
    Nat.card {w : SpinW // spinQ w ≠ 0} = 120 := by
  change Nat.card {w : Fin (2 * 4) → ZMod 2 //
    coordinateQuadPlus 4 (ZMod 2) w ≠ 0} = 120
  exact sixteenC8SpinTrans_card_nonsing

private noncomputable def sixteenC8SpinTrans_ptCentEquiv {w : SpinW} (hw : spinQ w ≠ 0) :
    ↥(MulAction.stabilizer ↥spinH w) ≃* ↥(ptCent spinH w) :=
  let S : Subgroup (MulAut SpinW) := MulAction.stabilizer (MulAut SpinW) w
  let e3 : ↥(S.subgroupOf spinH) ≃* ↥(MulAction.stabilizer ↥spinH w) :=
    MulEquiv.subgroupCongr (MulAction.stabilizer_subgroupOf spinH w)
  let e1 : ↥(S.subgroupOf spinH) ≃* ↥(S ⊓ spinH) :=
    (Subgroup.equivMapOfInjective (S.subgroupOf spinH) spinH.subtype
      spinH.subtype_injective).trans
      (MulEquiv.subgroupCongr (Subgroup.subgroupOf_map_subtype S spinH))
  let e2 : ↥(S ⊓ spinH) ≃* ↥(spinH ⊓ S) := MulEquiv.subgroupCongr (inf_comm S spinH)
  e3.symm.trans (e1.trans e2)

theorem spinH_trans_nonsing {w w' : SpinW} (hw : spinQ w ≠ 0) (hw' : spinQ w' ≠ 0) :
    ∃ g ∈ spinH, g w = w' := by
  obtain ⟨h, hh, hmul⟩ :=
    sixteenC8SpinTrans_spinSeven_trans_nonsing (Multiplicative.toAdd w)
      (Multiplicative.toAdd w') (by simpa only [spinQ] using hw)
      (by simpa only [spinQ] using hw')
  refine ⟨spinHom h, (mem_spinH_iff (spinHom h)).mpr ⟨h, hh, rfl⟩, ?_⟩
  rw [spinHom_apply, hmul]
  rfl

theorem card_spinH : Nat.card ↥spinH = 1451520 := by
  obtain ⟨e⟩ := nonempty_spinSeven_mulEquiv (ZMod 2)
  rw [← Nat.card_congr spinHEquiv.toEquiv, Nat.card_congr e.toEquiv]
  exact CFSG.ClassicalInvolution.Solomon73.Yamaki.card_sp62

theorem card_ptCent_nonsing {w : SpinW} (hw : spinQ w ≠ 0) :
    Nat.card ↥(ptCent spinH w) = 12096 := by
  have hXorbit : MulAction.orbit ↥spinH w = {w' : SpinW | spinQ w' ≠ 0} := by
    ext w'
    rw [MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨g, hg⟩
      rw [show w' = g • w from hg.symm]
      change spinQ ((g : MulAut SpinW) w) ≠ 0
      rw [spinQ_spinH g.2 w]
      exact hw
    · intro hw'
      obtain ⟨g, hg, hgw⟩ := spinH_trans_nonsing hw hw'
      exact ⟨⟨g, hg⟩, by rw [Subgroup.smul_def]; exact hgw⟩
  have hcardX : ({w' : SpinW | spinQ w' ≠ 0} : Set SpinW).ncard = 120 := by
    rw [← Nat.card_coe_set_eq]
    exact sixteenC8SpinTrans_card_nonsing_spinW
  have hidx := MulAction.index_stabilizer (↥spinH) w
  have hcm := Subgroup.card_mul_index (MulAction.stabilizer ↥spinH w)
  rw [hidx, hXorbit, hcardX, card_spinH] at hcm
  have hstab : Nat.card ↥(MulAction.stabilizer ↥spinH w) = 12096 := by
    refine Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 120) ?_
    rw [hcm]
  exact (Nat.card_congr (sixteenC8SpinTrans_ptCentEquiv hw).toEquiv).symm.trans hstab

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
