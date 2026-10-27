module

public import CFSG.SignalizerFunctorTheorem.NonLocal.OrthHeis

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.SignalizerFunctorTheorem.NonLocal.Orth
open CFSG.ComponentClassification CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear

variable {K : Type} [Field K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}

theorem polar_coordinateSemilinearMap (g : similarityPairs Q) (x y : Fin d → K) :
    polar Q (coordinateSemilinearMap g.val x) (coordinateSemilinearMap g.val y) =
      (multiplier Q g : K) * g.val.right (polar Q x y) := by
  simp only [QuadraticMap.polar, ← map_add, multiplier_spec, map_sub, mul_sub]

theorem coordinateSemilinearMap_eichler (g : similarityPairs Q) (u w x : Fin d → K) :
    coordinateSemilinearMap g.val (eichler Q u w ((coordinateSemilinearMap g.val).symm x)) =
      eichler Q (coordinateSemilinearMap g.val u)
        ((multiplier Q g : K)⁻¹ • coordinateSemilinearMap g.val w) x := by
  have hμ : (multiplier Q g : K) ≠ 0 := Units.ne_zero (multiplier Q g)
  have hpol : ∀ a b, polar Q (coordinateSemilinearMap g.val a)
      (coordinateSemilinearMap g.val b) = (multiplier Q g : K) * g.val.right (polar Q a b) :=
    polar_coordinateSemilinearMap g
  by_cases h : Q u = 0 ∧ polar Q u w = 0
  · have hgu : Q (coordinateSemilinearMap g.val u) = 0 := by
      rw [multiplier_spec Q g u, h.1, map_zero, mul_zero]
    have hgw : polar Q (coordinateSemilinearMap g.val u)
        ((multiplier Q g : K)⁻¹ • coordinateSemilinearMap g.val w) = 0 := by
      rw [polar_smul_right_eq, hpol, h.2, map_zero, mul_zero, mul_zero]
    have hx : ∀ y, g.val.right (polar Q ((coordinateSemilinearMap g.val).symm x) y) =
        (multiplier Q g : K)⁻¹ * polar Q x (coordinateSemilinearMap g.val y) := fun y => by
      have h' := hpol ((coordinateSemilinearMap g.val).symm x) y
      rw [AddEquiv.apply_symm_apply] at h'
      rw [h']
      field_simp
    rw [eichler_apply h.1 h.2, eichler_apply hgu hgw, map_sub, map_add,
      coordinateSemilinearMap_smul, coordinateSemilinearMap_smul, map_add, map_mul,
      AddEquiv.apply_symm_apply, hx, hx, polar_smul_right_eq, map_smul_eq_sq,
      multiplier_spec Q g w]
    field_simp
    module
  · have h' : ¬(Q (coordinateSemilinearMap g.val u) = 0 ∧
        polar Q (coordinateSemilinearMap g.val u)
          ((multiplier Q g : K)⁻¹ • coordinateSemilinearMap g.val w) = 0) := by
      rintro ⟨h1, h2⟩
      apply h
      constructor
      · have h1' : g.val.right (Q u) = 0 := by
          apply (mul_eq_zero.mp ?_).resolve_left hμ
          rw [← multiplier_spec Q g u, h1]
        exact (map_eq_zero_iff g.val.right g.val.right.injective).mp h1'
      · rw [polar_smul_right_eq, hpol] at h2
        have h2' : g.val.right (polar Q u w) = 0 := by
          rwa [← mul_assoc, inv_mul_cancel₀ hμ, one_mul] at h2
        exact (map_eq_zero_iff g.val.right g.val.right.injective).mp h2'
    rw [eichler_of_not h, eichler_of_not h']
    exact AddEquiv.apply_symm_apply (coordinateSemilinearMap g.val) x

theorem exists_map_ne_zero_of_nondegenerate (hd : 1 ≤ d) (hQ : (polarBilin Q).Nondegenerate) :
    ∃ v, Q v ≠ 0 := by
  by_contra! h
  have hx : (Pi.single ⟨0, hd⟩ 1 : Fin d → K) = 0 := by
    refine hQ.1 _ fun y => ?_
    rw [polarBilin_apply_apply, polar, h, h, h, sub_zero, sub_zero]
  exact one_ne_zero (congrFun hx ⟨0, hd⟩ |>.symm.trans (Pi.single_eq_same _ _)).symm

theorem coordinateSemilinearMap_sq (g : coordinateSemilinearGroup d K) (hσ2 : g.right ^ 2 = 1)
    {c : Kˣ} (hc : g.left * CatalogueBHigherLinearField.glFieldAut (Fin d) K g.right g.left =
      Matrix.GeneralLinearGroup.scalar (Fin d) c) (v : Fin d → K) :
    coordinateSemilinearMap g (coordinateSemilinearMap g v) = (c : K) • v := by
  have hright : (g * g).right = 1 := by
    rw [coordinateSemilinearGroup_mul_field, ← _root_.sq, hσ2]
  have hleft : (g * g).left = Matrix.GeneralLinearGroup.scalar (Fin d) c := by
    rw [coordinateSemilinearGroup_mul_matrix, hc]
  rw [← coordinateSemilinearMap_mul, coordinateSemilinearMap_apply, hright, hleft]
  funext i
  simp [Matrix.GeneralLinearGroup.coe_scalar, Matrix.mulVec_diagonal]

theorem right_apply_scalar_eq (g : coordinateSemilinearGroup d K) (hd : 1 ≤ d)
    (hσ2 : g.right ^ 2 = 1) {c : Kˣ}
    (hc : g.left * CatalogueBHigherLinearField.glFieldAut (Fin d) K g.right g.left =
      Matrix.GeneralLinearGroup.scalar (Fin d) c) :
    g.right (c : K) = c := by
  let w : Fin d → K := Pi.single ⟨0, hd⟩ 1
  have hw : w ⟨0, hd⟩ = 1 := by simp [w]
  have h1 : coordinateSemilinearMap g
      (coordinateSemilinearMap g (coordinateSemilinearMap g
        ((coordinateSemilinearMap g).symm w))) = g.right (c : K) • w := by
    rw [coordinateSemilinearMap_sq g hσ2 hc ((coordinateSemilinearMap g).symm w),
      coordinateSemilinearMap_smul, AddEquiv.apply_symm_apply]
  have h2 : coordinateSemilinearMap g
      (coordinateSemilinearMap g (coordinateSemilinearMap g
        ((coordinateSemilinearMap g).symm w))) = (c : K) • w := by
    rw [coordinateSemilinearMap_sq g hσ2 hc
      (coordinateSemilinearMap g ((coordinateSemilinearMap g).symm w)),
      AddEquiv.apply_symm_apply]
  have h : g.right (c : K) • w = (c : K) • w := h1.symm.trans h2
  have h0 := congrFun h ⟨0, hd⟩
  simpa [hw] using h0

theorem multiplier_mul_right_multiplier (g : similarityPairs Q) (hσ2 : g.val.right ^ 2 = 1)
    {c : Kˣ} (hc : g.val.left * CatalogueBHigherLinearField.glFieldAut (Fin d) K g.val.right
      g.val.left = Matrix.GeneralLinearGroup.scalar (Fin d) c) {v : Fin d → K} (hv : Q v ≠ 0) :
    (multiplier Q g : K) * g.val.right (multiplier Q g : K) = (c : K) ^ 2 := by
  have h1 : Q (coordinateSemilinearMap g.val (coordinateSemilinearMap g.val v)) =
      (c : K) ^ 2 * Q v := by
    rw [coordinateSemilinearMap_sq g.val hσ2 hc v, map_smul_eq_sq]
  have h2 : Q (coordinateSemilinearMap g.val (coordinateSemilinearMap g.val v)) =
      ((multiplier Q g : K) * g.val.right (multiplier Q g : K)) * Q v := by
    rw [multiplier_spec Q g (coordinateSemilinearMap g.val v), multiplier_spec Q g v, map_mul]
    have hσ2' : g.val.right (g.val.right (Q v)) = Q v := by
      have h := congrArg (fun f : K ≃+* K => f (Q v)) hσ2
      simpa [pow_two] using h
    rw [hσ2']
    ring
  exact (mul_right_cancel₀ hv (h1.symm.trans h2)).symm

section Hex

variable (hex : ∀ u w : Fin d → K, ∃ x : matrixDerived Q,
  matrixLinearIso (d := d) (K := K) x.val = eichler Q u w)

theorem eMat_eq_of_eichler_eq {u w u' w' : Fin d → K} (h : eichler Q u w = eichler Q u' w') :
    eMat hex u w = eMat hex u' w' :=
  omegaLin_injective (by rw [omegaLin_eMat, omegaLin_eMat, h])

theorem eMat_smul_left (c : K) (u w : Fin d → K) : eMat hex (c • u) w = eMat hex u (c • w) :=
  eMat_eq_of_eichler_eq hex (eichler_smul_left c u w)

theorem matrixProjectiveConjugationHom_eMat (g : similarityPairs Q) (u w : Fin d → K) :
    matrixProjectiveConjugationHom Q g (matrixProjectiveProjection Q (eMat hex u w)) =
      matrixProjectiveProjection Q (eMat hex (coordinateSemilinearMap g.val u)
        ((multiplier Q g : K)⁻¹ • coordinateSemilinearMap g.val w)) := by
  change matrixProjectiveConjugation Q g (matrixProjectiveProjection Q (eMat hex u w)) =
    matrixProjectiveProjection Q (eMat hex (coordinateSemilinearMap g.val u)
      ((multiplier Q g : K)⁻¹ • coordinateSemilinearMap g.val w))
  rw [matrixProjectiveConjugation_mk]
  refine congrArg (matrixProjectiveProjection Q) ?_
  apply omegaLin_injective
  apply LinearEquiv.ext
  intro v
  rw [omegaLin_eMat]
  change matrixLinearEquiv (matrixDerivedConjugation Q g (eMat hex u w)).val v =
    eichler Q (coordinateSemilinearMap g.val u)
      ((multiplier Q g : K)⁻¹ • coordinateSemilinearMap g.val w) v
  rw [matrixDerivedConjugation_val]
  change matrixLinearEquiv (matrixConjugation g.val (eMat hex u w).val) v =
    eichler Q (coordinateSemilinearMap g.val u)
      ((multiplier Q g : K)⁻¹ • coordinateSemilinearMap g.val w) v
  rw [matrixConjugation_vector]
  change coordinateSemilinearMap g.val ((omegaLin (eMat hex u w))
      ((coordinateSemilinearMap g.val).symm v)) =
    eichler Q (coordinateSemilinearMap g.val u)
      ((multiplier Q g : K)⁻¹ • coordinateSemilinearMap g.val w) v
  rw [omegaLin_eMat]
  exact coordinateSemilinearMap_eichler g u w v

end Hex

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive
