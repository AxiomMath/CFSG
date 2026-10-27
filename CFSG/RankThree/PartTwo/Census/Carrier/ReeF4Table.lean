module

public import CFSG.RankThree.PartTwo.Census.Carrier.ReeF4Basis
public import CFSG.LieType.Chevalley.RootOps.Check
public import TauCeti.Algebra.Lie.F4.ShortRoot.Carrier

public section

namespace CFSG.TauCetiBridge.ReeF4

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.RootOps

@[expose] def genRoot : Fin 4 ⊕ Fin 4 → ℕ
  | .inl i => i
  | .inr i => Tag.F4.rootCertificate.image i ⟨i, i.2⟩

@[expose] def combL (v : List (ℕ × ℤ)) : SpMat :=
  v.flatMap fun x => scaleL x.2 (bL x.1)

@[expose] def tabY (g : Fin 4 ⊕ Fin 4) (k s : ℕ) : SpMat :=
  combL (colOf (entries .F4 (genRoot g) k) s)

@[expose] def tableCheck (g : Fin 4 ⊕ Fin 4) (s : ℕ) : Bool :=
  eqB (mulL (spE g) (bL s) ++ negL (mulL (bL s) (spE g))) (tabY g 1 s) &&
  eqB (mulL (spE2 g) (bL s) ++ negL (mulL (mulL (spE g) (bL s)) (spE g)) ++
    mulL (bL s) (spE2 g)) (tabY g 2 s) &&
  eqB (mulL (mulL (spE g) (bL s)) (spE2 g) ++ negL (mulL (mulL (spE2 g) (bL s)) (spE g)))
    (tabY g 3 s) &&
  eqB (mulL (mulL (spE2 g) (bL s)) (spE2 g)) []

theorem tableCheck_inl_zero : ∀ s < 52, tableCheck (.inl 0) s = true := by
  decide +kernel

theorem tableCheck_inl_one : ∀ s < 52, tableCheck (.inl 1) s = true := by
  decide +kernel

theorem tableCheck_inl_two : ∀ s < 52, tableCheck (.inl 2) s = true := by
  decide +kernel

theorem tableCheck_inl_three : ∀ s < 52, tableCheck (.inl 3) s = true := by
  decide +kernel

theorem tableCheck_inr_zero : ∀ s < 52, tableCheck (.inr 0) s = true := by
  decide +kernel

theorem tableCheck_inr_one : ∀ s < 52, tableCheck (.inr 1) s = true := by
  decide +kernel

theorem tableCheck_inr_two : ∀ s < 52, tableCheck (.inr 2) s = true := by
  decide +kernel

theorem tableCheck_inr_three : ∀ s < 52, tableCheck (.inr 3) s = true := by
  decide +kernel

theorem tableCheck_all (g : Fin 4 ⊕ Fin 4) {s : ℕ} (hs : s < 52) : tableCheck g s = true := by
  rcases g with i | i <;> fin_cases i
  exacts [tableCheck_inl_zero s hs, tableCheck_inl_one s hs, tableCheck_inl_two s hs,
    tableCheck_inl_three s hs, tableCheck_inr_zero s hs, tableCheck_inr_one s hs,
    tableCheck_inr_two s hs, tableCheck_inr_three s hs]

theorem smat_combL (v : List (ℕ × ℤ)) : smat (combL v) = (v.map fun x => x.2 • bMat x.1).sum := by
  rw [combL, smat_flatMap]
  congr 1
  exact List.map_congr_left fun x _ => smat_scaleL _ _

theorem tableCheck_spec {g : Fin 4 ⊕ Fin 4} {s : ℕ} (h : tableCheck g s = true) :
    tcE g * bMat s - bMat s * tcE g = smat (tabY g 1 s) ∧
    tcE2 g * bMat s - tcE g * bMat s * tcE g + bMat s * tcE2 g = smat (tabY g 2 s) ∧
    tcE g * bMat s * tcE2 g - tcE2 g * bMat s * tcE g = smat (tabY g 3 s) ∧
    tcE2 g * bMat s * tcE2 g = 0 := by
  simp only [tableCheck, Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  have e1 := smat_eq_of_eqB h1
  have e2 := smat_eq_of_eqB h2
  have e3 := smat_eq_of_eqB h3
  have e4 := smat_eq_of_eqB h4
  simp only [smat_append, smat_negL, smat_mulL, smat_spE, smat_spE2, smat_nil] at e1 e2 e3 e4
  refine ⟨?_, ?_, ?_, e4⟩
  · rw [← e1, bMat, sub_eq_add_neg]
  · rw [← e2, bMat, sub_eq_add_neg]
  · rw [← e3, bMat, sub_eq_add_neg]

variable {A : Type*} [CommRing A]

noncomputable abbrev rootPointMat (k : Fin 4 ⊕ Fin 4) (t : A) : Matrix (Fin 26) (Fin 26) A :=
  ((TauCeti.F4ShortRoot.rootSubgroupPoints k A (Multiplicative.ofAdd t) :
    Matrix.GeneralLinearGroup (Fin 26) A) : Matrix (Fin 26) (Fin 26) A)

theorem rootPointMat_eq (k : Fin 4 ⊕ Fin 4) (t : A) :
    rootPointMat k t = 1 + t • (tcE k).map (Int.cast : ℤ → A) +
      t ^ 2 • (tcE2 k).map (Int.cast : ℤ → A) := by
  rw [rootPointMat, TauCeti.F4ShortRoot.coe_rootSubgroupPoints_eq, toAdd_ofAdd,
    rootMatrix_eq_tcE, rootDividedSquareMatrix_eq_tcE2]

theorem coe_rootPoint_inv (k : Fin 4 ⊕ Fin 4) (t : A) :
    (((TauCeti.F4ShortRoot.rootSubgroupPoints k A (Multiplicative.ofAdd t) :
      Matrix.GeneralLinearGroup (Fin 26) A)⁻¹ : Matrix.GeneralLinearGroup (Fin 26) A) :
        Matrix (Fin 26) (Fin 26) A) = rootPointMat k (-t) := by
  rw [rootPointMat, ofAdd_neg, map_inv, Subgroup.coe_inv]

theorem conj_expand_aux (t : A) (e f x : Matrix (Fin 26) (Fin 26) A) :
    (1 + t • e + t ^ 2 • f) * x * (1 + (-t) • e + (-t) ^ 2 • f) =
      x + t • (e * x - x * e) + t ^ 2 • (f * x - e * x * e + x * f) +
        t ^ 3 • (e * x * f - f * x * e) + t ^ 4 • (f * x * f) := by
  simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one, smul_add,
    smul_sub, smul_smul, Matrix.mul_assoc, neg_smul, mul_neg]
  module

theorem map_intCast_eq_mapMatrix (M : Matrix (Fin 26) (Fin 26) ℤ) :
    M.map (Int.cast : ℤ → A) = (Int.castRingHom A).mapMatrix M := by
  rw [RingHom.mapMatrix_apply, Int.coe_castRingHom]

@[expose] def combR (A : Type*) [CommRing A] (v : List (ℕ × ℤ)) : Matrix (Fin 26) (Fin 26) A :=
  (v.map fun x => (x.2 : A) • bMatR A x.1).sum

theorem map_smat_combL (v : List (ℕ × ℤ)) :
    (smat (combL v)).map (Int.cast : ℤ → A) = combR A v := by
  rw [smat_combL, combR, map_intCast_eq_mapMatrix, map_list_sum, List.map_map]
  congr 1
  refine List.map_congr_left fun x _ => ?_
  simp only [Function.comp_apply, map_zsmul, ← map_intCast_eq_mapMatrix, Int.cast_smul_eq_zsmul]

theorem conj_expand (E E2 X : Matrix (Fin 26) (Fin 26) ℤ) (t : A) :
    (1 + t • E.map (Int.cast : ℤ → A) + t ^ 2 • E2.map (Int.cast : ℤ → A)) *
        X.map (Int.cast : ℤ → A) *
        (1 + (-t) • E.map (Int.cast : ℤ → A) + (-t) ^ 2 • E2.map (Int.cast : ℤ → A)) =
      X.map (Int.cast : ℤ → A) + t • (E * X - X * E).map (Int.cast : ℤ → A) +
        t ^ 2 • (E2 * X - E * X * E + X * E2).map (Int.cast : ℤ → A) +
        t ^ 3 • (E * X * E2 - E2 * X * E).map (Int.cast : ℤ → A) +
        t ^ 4 • (E2 * X * E2).map (Int.cast : ℤ → A) := by
  simp only [map_intCast_eq_mapMatrix]
  rw [conj_expand_aux]
  simp only [map_sub, map_add, map_mul]

theorem conj_rootPoint (k : Fin 4 ⊕ Fin 4) (t : A) {s : ℕ} (hs : s < 52) :
    rootPointMat k t * bMatR A s * rootPointMat k (-t) =
      bMatR A s + t • combR A (colOf (entries .F4 (genRoot k) 1) s) +
        t ^ 2 • combR A (colOf (entries .F4 (genRoot k) 2) s) +
        t ^ 3 • combR A (colOf (entries .F4 (genRoot k) 3) s) := by
  obtain ⟨h1, h2, h3, h4⟩ := tableCheck_spec (tableCheck_all k hs)
  rw [rootPointMat_eq, rootPointMat_eq, conj_expand, h1, h2, h3, h4,
    Matrix.map_zero _ Int.cast_zero, smul_zero, add_zero, tabY, tabY, tabY, map_smat_combL,
    map_smat_combL, map_smat_combL]

end CFSG.TauCetiBridge.ReeF4
