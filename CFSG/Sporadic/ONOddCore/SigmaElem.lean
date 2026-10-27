module

public import CFSG.Sporadic.ONOddCore.SigmaTriple
public import CFSG.Sporadic.ONOddCore.LocalAutData
import all CFSG.LocalAnalysis.ComponentClassification.PSL3FourActionData

public noncomputable section

namespace CFSG.Sporadic.ONOddCore

open Matrix CFSG.ONSchreier CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification
open CFSG.ComponentClassification.PSL3Four

@[expose] def elemOf (t : Triple) : SpecialLinearGroup (Fin 3) F4 :=
  if h : t.1 ≠ t.2.1 then elemSL t.1 t.2.1 h t.2.2 else 1

theorem elemOf_eq {t : Triple} (h : t.1 ≠ t.2.1) : elemOf t = elemSL t.1 t.2.1 h t.2.2 := by
  rw [elemOf, dite_eq_left h]

theorem coe_elemOf {t : Triple} (h : t.1 ≠ t.2.1) :
    (elemOf t : Matrix (Fin 3) (Fin 3) F4) = transvection t.1 t.2.1 t.2.2 := by
  rw [elemOf_eq h]
  rfl

theorem elemOf_mul {i j : Fin 3} (h : i ≠ j) (a b : F4) :
    elemOf (i, j, a) * elemOf (i, j, b) = elemOf (i, j, a + b) := by
  apply Subtype.ext
  show (elemOf (i, j, a) : Matrix (Fin 3) (Fin 3) F4) * elemOf (i, j, b) = elemOf (i, j, a + b)
  rw [coe_elemOf h, coe_elemOf h, coe_elemOf h]
  exact Matrix.transvection_mul_transvection_same i j h a b

theorem elemOf_zero {i j : Fin 3} (h : i ≠ j) : elemOf (i, j, 0) = 1 := by
  apply Subtype.ext
  show (elemOf (i, j, 0) : Matrix (Fin 3) (Fin 3) F4) = 1
  rw [coe_elemOf h]
  exact Matrix.transvection_zero i j

theorem elemOf_inv {i j : Fin 3} (h : i ≠ j) (a : F4) :
    (elemOf (i, j, a))⁻¹ = elemOf (i, j, a) := by
  apply inv_eq_of_mul_eq_one_right
  rw [elemOf_mul h, show a + a = 0 by revert a; decide, elemOf_zero h]

theorem elemOf_transpose {i j : Fin 3} (h : i ≠ j) (a : F4) :
    (elemOf (i, j, a)).transpose = elemOf (j, i, a) := by
  apply Subtype.ext
  show (elemOf (i, j, a) : Matrix (Fin 3) (Fin 3) F4)ᵀ = elemOf (j, i, a)
  rw [coe_elemOf h, coe_elemOf (Ne.symm h)]
  simp [transvection, transpose_add, transpose_single]

theorem map_frob_elemOf {i j : Fin 3} (h : i ≠ j) (a : F4) :
    SpecialLinearGroup.map frob.toRingHom (elemOf (i, j, a)) = elemOf (i, j, a ^ 2) := by
  apply Subtype.ext
  show (elemOf (i, j, a) : Matrix (Fin 3) (Fin 3) F4).map frob.toRingHom = elemOf (i, j, a ^ 2)
  rw [coe_elemOf h, coe_elemOf h]
  ext k l
  simp only [transvection, Matrix.map_apply, Matrix.add_apply, Matrix.one_apply,
    Matrix.single_apply]
  split_ifs <;> simp_all [frob_apply]

theorem dGL_mat : ((dGL : GL (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4) = diagonal dDiag := rfl

theorem dGL_inv_mat :
    ((dGL⁻¹ : GL (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4) = diagonal fun k => (dDiag k)⁻¹ := by
  have : ((dGL⁻¹ : GL (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4) = diagonal ![1 + F4.ω, 1, 1] := rfl
  rw [this]
  congr 1
  funext k
  fin_cases k <;> decide

theorem conj_dGL_elemOf {i j : Fin 3} (h : i ≠ j) (a : F4) :
    CatalogueBHigherLinearAction.slConjugation 3 F4 dGL (elemOf (i, j, a)) =
      elemOf (i, j, dDiag i * a * (dDiag j)⁻¹) := by
  apply Subtype.ext
  rw [LinearFlag.coe_slConjugation, dGL_mat, dGL_inv_mat]
  show diagonal dDiag * (elemOf (i, j, a) : Matrix (Fin 3) (Fin 3) F4) *
    diagonal (fun k => (dDiag k)⁻¹) = elemOf (i, j, dDiag i * a * (dDiag j)⁻¹)
  rw [coe_elemOf h, coe_elemOf h]
  ext k l
  simp only [diagonal_mul, mul_diagonal, transvection, Matrix.add_apply, Matrix.one_apply,
    Matrix.single_apply]
  have hd : ∀ k, dDiag k * (dDiag k)⁻¹ = 1 := by decide
  split_ifs with h1 h2 h2 <;> simp_all

theorem dualAut_elemOf {t : Triple} (h : t.1 ≠ t.2.1) :
    LinearFlag.dualAut 3 F4 (LinearFlag.proj 3 F4 (elemOf t)) =
      LinearFlag.proj 3 F4 (elemOf (dualT t)) := by
  obtain ⟨i, j, a⟩ := t
  rw [LinearFlag.dualAut_proj, elemOf_inv h, elemOf_transpose h]
  rfl

theorem fieldAut_elemOf {t : Triple} (h : t.1 ≠ t.2.1) :
    LinearFlag.fieldAut 3 F4 frob (LinearFlag.proj 3 F4 (elemOf t)) =
      LinearFlag.proj 3 F4 (elemOf (frobT t)) := by
  obtain ⟨i, j, a⟩ := t
  rw [LinearFlag.fieldAut_proj, map_frob_elemOf h]
  rfl

theorem conjAut_elemOf {t : Triple} (h : t.1 ≠ t.2.1) :
    LinearFlag.conjAut 3 F4 dGL (LinearFlag.proj 3 F4 (elemOf t)) =
      LinearFlag.proj 3 F4 (elemOf (conjDT t)) := by
  obtain ⟨i, j, a⟩ := t
  rw [LinearFlag.conjAut_proj, conj_dGL_elemOf h]
  rfl

theorem dualT_ne {t : Triple} (h : t.1 ≠ t.2.1) : (dualT t).1 ≠ (dualT t).2.1 := Ne.symm h

theorem iterate_dualAut (g : ℕ) {t : Triple} (h : t.1 ≠ t.2.1) :
    (LinearFlag.dualAut 3 F4 ^ g) (LinearFlag.proj 3 F4 (elemOf t)) =
      LinearFlag.proj 3 F4 (elemOf (dualT^[g] t)) ∧ (dualT^[g] t).1 ≠ (dualT^[g] t).2.1 := by
  induction g generalizing t with
  | zero => exact ⟨rfl, h⟩
  | succ g ih =>
    rw [pow_succ, MulAut.mul_apply, dualAut_elemOf h, Function.iterate_succ_apply]
    exact ih (dualT_ne h)

theorem iterate_fieldAut (f : ℕ) {t : Triple} (h : t.1 ≠ t.2.1) :
    (LinearFlag.fieldAut 3 F4 frob ^ f) (LinearFlag.proj 3 F4 (elemOf t)) =
      LinearFlag.proj 3 F4 (elemOf (frobT^[f] t)) ∧ (frobT^[f] t).1 ≠ (frobT^[f] t).2.1 := by
  induction f generalizing t with
  | zero => exact ⟨rfl, h⟩
  | succ f ih =>
    rw [pow_succ, MulAut.mul_apply, fieldAut_elemOf h, Function.iterate_succ_apply]
    exact ih h

theorem iterate_conjAut (d : ℕ) {t : Triple} (h : t.1 ≠ t.2.1) :
    (LinearFlag.conjAut 3 F4 (dGL ^ d)) (LinearFlag.proj 3 F4 (elemOf t)) =
      LinearFlag.proj 3 F4 (elemOf (conjDT^[d] t)) ∧ (conjDT^[d] t).1 ≠ (conjDT^[d] t).2.1 := by
  induction d generalizing t with
  | zero =>
    rw [pow_zero, map_one]
    exact ⟨rfl, h⟩
  | succ d ih =>
    rw [pow_succ, map_mul, MulAut.mul_apply, conjAut_elemOf h, Function.iterate_succ_apply]
    exact ih h

theorem gammaAut_elemOf (d f g : ℕ) {t : Triple} (h : t.1 ≠ t.2.1) :
    gammaAut d f g (LinearFlag.proj 3 F4 (elemOf t)) =
      LinearFlag.proj 3 F4 (elemOf (stepT d f g t)) ∧ (stepT d f g t).1 ≠ (stepT d f g t).2.1 := by
  obtain ⟨h1, h1'⟩ := iterate_dualAut g h
  obtain ⟨h2, h2'⟩ := iterate_fieldAut f h1'
  obtain ⟨h3, h3'⟩ := iterate_conjAut d h2'
  refine ⟨?_, h3'⟩
  rw [gammaAut, MulAut.mul_apply, MulAut.mul_apply, h1, h2, h3]
  rfl

@[expose] def xGen (m : ℕ) : Equiv.Perm (Fin 120) := permOfArr 120 Data.PSL120Chain.generators[m]!

@[expose] def xGens : List (Equiv.Perm (Fin 120)) := (List.range 12).map xGen

theorem elemTriples_ne : ∀ t ∈ elemTriples, t.1 ≠ t.2.1 := by decide

theorem elemAt_eq {m : ℕ} (hm : m < 12) : elemAt m = elemOf (elemTriples.getD m (0, 1, 1)) := by
  interval_cases m <;> rfl

theorem psi_elemTriple
    {m : ℕ} (hm : m < 12) :
    psi (elemOf (elemTriples.getD m (0, 1, 1))) = xGen m := by
  rw [← elemAt_eq hm, psi_elem hm]
  rfl

theorem mem_elemTriples {i j : Fin 3} (h : i ≠ j) :
    (i, j, 1) ∈ elemTriples ∧ (i, j, F4.ω) ∈ elemTriples := by
  revert i j
  decide

theorem psi_mem_elemTriples
    {t : Triple} (ht : t ∈ elemTriples) :
    psi (elemOf t) = evalPos xGens [tripleIdx t] := by
  have hlt' : elemTriples.idxOf t < elemTriples.length := List.idxOf_lt_length_iff.2 ht
  have hlt : elemTriples.idxOf t < 12 := hlt'
  have hget : elemTriples.getD (elemTriples.idxOf t) (0, 1, 1) = t := by
    rw [List.getD_eq_getElem _ _ hlt', List.getElem_idxOf]
  rw [evalPos_cons, evalPos_nil, mul_one, tripleIdx, Nat.add_sub_cancel,
    List.getD_eq_getElem _ _ (by simpa [xGens] using hlt)]
  simp only [xGens, List.getElem_map, List.getElem_range]
  rw [← psi_elemTriple hlt, hget]

theorem eq_one_add_omega : ∀ a : F4, a ≠ 0 → ¬(a = 1 ∨ a = F4.ω) → a = 1 + F4.ω := by
  decide

theorem psi_elemOf
    {t : Triple} (h : t.1 ≠ t.2.1) (ha : t.2.2 ≠ 0) :
    psi (elemOf t) = evalPos xGens (tripleWord t) := by
  obtain ⟨i, j, a⟩ := t
  obtain ⟨h1, hω⟩ := mem_elemTriples h
  unfold tripleWord
  by_cases hc : a = 1 ∨ a = F4.ω
  · rw [ite_eq_left hc]
    rcases hc with rfl | rfl
    · exact psi_mem_elemTriples h1
    · exact psi_mem_elemTriples hω
  · rw [ite_eq_right hc]
    have ha3 : a = 1 + F4.ω := eq_one_add_omega a ha hc
    rw [show [tripleIdx (i, j, 1), tripleIdx (i, j, F4.ω)] = [tripleIdx (i, j, 1)] ++
      [tripleIdx (i, j, F4.ω)] from rfl, evalPos_append, ← psi_mem_elemTriples h1,
      ← psi_mem_elemTriples hω, ← map_mul, elemOf_mul h, ha3]

theorem stepT_ne_zero (d f g : ℕ) {t : Triple} (ha : t.2.2 ≠ 0) : (stepT d f g t).2.2 ≠ 0 := by
  have hdual : ∀ k (t : Triple), t.2.2 ≠ 0 → (dualT^[k] t).2.2 ≠ 0 := by
    intro k
    induction k with
    | zero => exact fun _ h => h
    | succ k ih => intro t ht; rw [Function.iterate_succ_apply]; exact ih _ ht
  have hfrob : ∀ k (t : Triple), t.2.2 ≠ 0 → (frobT^[k] t).2.2 ≠ 0 := by
    intro k
    induction k with
    | zero => exact fun _ h => h
    | succ k ih =>
      intro t ht
      rw [Function.iterate_succ_apply]
      exact ih _ (by revert ht; exact (by revert t; decide : ∀ t : Triple, t.2.2 ≠ 0 →
        (frobT t).2.2 ≠ 0) t)
  have hconj : ∀ k (t : Triple), t.2.2 ≠ 0 → (conjDT^[k] t).2.2 ≠ 0 := by
    intro k
    induction k with
    | zero => exact fun _ h => h
    | succ k ih =>
      intro t ht
      rw [Function.iterate_succ_apply]
      exact ih _ (by revert ht; exact (by revert t; decide : ∀ t : Triple, t.2.2 ≠ 0 →
        (conjDT t).2.2 ≠ 0) t)
  exact hconj d _ (hfrob f _ (hdual g _ ha))

@[expose] def xGenX
    (m : ℕ) (hm : m < 12) : onX :=
  ⟨xGen m, by rw [← psi_range, ← psi_elemTriple hm]; exact ⟨_, rfl⟩⟩

theorem thetaX_elemTriple
    {m : ℕ} (hm : m < 12) :
    thetaX (LinearFlag.proj 3 F4 (elemOf (elemTriples.getD m (0, 1, 1)))) = xGenX m hm :=
  Subtype.ext (by rw [thetaX_proj, psi_elemTriple hm]; rfl)

theorem sigmaX_xGen
    (d f g : ℕ) {m : ℕ} (hm : m < 12) :
    ((sigmaX d f g (xGenX m hm) : onX) : Equiv.Perm (Fin 120)) =
      evalPos xGens (sigWord d f g m) := by
  have hm' : m < elemTriples.length := by simpa [elemTriples] using hm
  have hmem : elemTriples.getD m (0, 1, 1) ∈ elemTriples := by
    rw [List.getD_eq_getElem _ _ hm']
    exact List.getElem_mem hm'
  have hne := elemTriples_ne _ hmem
  have ha : (elemTriples.getD m (0, 1, 1)).2.2 ≠ 0 := by
    revert hmem
    generalize elemTriples.getD m (0, 1, 1) = t
    revert t
    decide
  obtain ⟨hγ, hne'⟩ := gammaAut_elemOf d f g hne
  rw [sigmaX, ← thetaX_elemTriple hm]
  simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  rw [hγ, thetaX_proj, psi_elemOf hne' (stepT_ne_zero d f g ha)]
  rfl

end CFSG.Sporadic.ONOddCore
