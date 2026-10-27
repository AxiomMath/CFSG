module

public import CFSG.RankThree.PartTwo.Sec21.LangTwisted2ProofD4Theta

public noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace CFSG.RankThree.PartTwo.Sec8.LangTwisted2Proof

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley LangTwistedProof

variable {L : Type} [Field L]

@[expose] def xkU (κ t : L) : ModGL TwistTag.D4.tag L :=
  xUnit TwistTag.D4.tag L 0 t * xUnit TwistTag.D4.tag L 1 (κ * t) *
    xUnit TwistTag.D4.tag L 3 (κ ^ 2 * t)

@[expose] def ykU (κ t : L) : ModGL TwistTag.D4.tag L :=
  yUnit TwistTag.D4.tag L 0 t * yUnit TwistTag.D4.tag L 1 (κ ^ 2 * t) *
    yUnit TwistTag.D4.tag L 3 (κ * t)

theorem coe_xkU (κ t : L) :
    ((xkU κ t : ModGL TwistTag.D4.tag L) : Module.End L (RootModule TwistTag.D4.tag L)) =
      xkEnd κ t := by
  simp only [xkU, xkEnd, Units.val_mul, coe_xUnit]

theorem coe_ykU (κ t : L) :
    ((ykU κ t : ModGL TwistTag.D4.tag L) : Module.End L (RootModule TwistTag.D4.tag L)) =
      ykEnd κ t := by
  simp only [ykU, ykEnd, Units.val_mul, coe_yUnit]

theorem secOrbitX_eq_conj (h2 : (2 : L) = 0) (μ : Lˣ) (j : Fin 3) (a : L) :
    secOrbitX μ j a = canonicalRep (coxeterSystem TwistTag.D4.tag) L (secW j) *
      xkU (secKappa μ j) a * (canonicalRep (coxeterSystem TwistTag.D4.tag) L (secW j))⁻¹ := by
  set n := canonicalRep (coxeterSystem TwistTag.D4.tag) L (secW j) with hn
  have hc : ∀ (i : Fin 3) (c : L), pinnedX TwistTag.D4.tag L (secVec j i) c =
      n * xUnit TwistTag.D4.tag L (![0, 1, 3] i) c * n⁻¹ := by
    intro i c
    rw [← pinnedX_single, hn, canonicalRep_mul_pinnedX_mul_inv_of_two h2 _ (isRoot_single _ _),
      secW_smul]
  rw [secOrbitX, hc 0, hc 1, hc 2, xkU]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  group

theorem secOrbitY_eq_conj (h2 : (2 : L) = 0) (μ : Lˣ) (j : Fin 3) (a : L) :
    secOrbitY μ j a = canonicalRep (coxeterSystem TwistTag.D4.tag) L (secW j) *
      ykU (secKappa μ j) a * (canonicalRep (coxeterSystem TwistTag.D4.tag) L (secW j))⁻¹ := by
  set n := canonicalRep (coxeterSystem TwistTag.D4.tag) L (secW j) with hn
  have hc : ∀ (i : Fin 3) (c : L), pinnedX TwistTag.D4.tag L (-secVec j i) c =
      n * yUnit TwistTag.D4.tag L (![0, 1, 3] i) c * n⁻¹ := by
    intro i c
    rw [← pinnedX_neg_single, hn,
      canonicalRep_mul_pinnedX_mul_inv_of_two h2 _ (IsRoot.neg (isRoot_single _ _)), smul_neg,
      secW_smul]
  rw [secOrbitY, hc 0, hc 1, hc 2, ykU]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  group

theorem canonicalRep_secW_zero :
    canonicalRep (coxeterSystem TwistTag.D4.tag) L (secW 0) = 1 :=
  canonicalRep_one _ _

theorem canonicalRep_secW_one :
    canonicalRep (coxeterSystem TwistTag.D4.tag) L (secW 1) = weylElt TwistTag.D4.tag L 2 1 :=
  canonicalRep_simple _ _ 2

theorem canonicalRep_secW_two :
    canonicalRep (coxeterSystem TwistTag.D4.tag) L (secW 2) =
      weylElt TwistTag.D4.tag L 0 1 * weylElt TwistTag.D4.tag L 1 1 *
        weylElt TwistTag.D4.tag L 3 1 * weylElt TwistTag.D4.tag L 2 1 := by
  have hw : secW 2 = (coxeterSystem TwistTag.D4.tag).wordProd [0, 1, 3, 2] := by
    simp only [secW, secSE, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons,
      CoxeterSystem.wordProd_cons, CoxeterSystem.wordProd_nil, mul_one, mul_assoc]
  have hred : (coxeterSystem TwistTag.D4.tag).IsReduced [0, 1, 3, 2] :=
    isReduced_of_reducedCheck (by decide +kernel)
  rw [hw, canonicalRep_wordProd hred]
  simp [mul_assoc]

theorem secKappa_zero (μ : Lˣ) : secKappa μ 0 = (μ : L) := by
  simp [secKappa]

theorem secKappa_one (μ : Lˣ) : secKappa μ 1 = (μ : L) ^ 2 := by
  simp only [secKappa]
  norm_num

theorem secKappa_two {μ : Lˣ} (hμ3 : μ ^ 3 = 1) : secKappa μ 2 = 1 := by
  simp only [secKappa]
  norm_num [hμ3]

theorem inv_apply_of_apply {n : ModGL TwistTag.D4.tag L} {v w : RootModule TwistTag.D4.tag L}
    (h : (n : Module.End L (RootModule TwistTag.D4.tag L)) v = w) :
    ((n⁻¹ : ModGL TwistTag.D4.tag L) : Module.End L (RootModule TwistTag.D4.tag L)) w = v := by
  rw [← h, ← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    Module.End.one_apply]

theorem nE_secThL1 [CharP L 2] (μ : L) (X : Matrix (Fin 3) (Fin 3) L) :
    nE 2 (secThL μ 1 X) = secThL μ 0 X := by
  have h := secThL_conj_of_single μ (j := 1) (j' := 0) (nE 2) 1 1
    (fun a b => by rw [Matrix.one_mul, Matrix.mul_one, secThL_single]; exact nE_secTh1 μ a b) X
  rwa [Matrix.one_mul, Matrix.mul_one] at h

theorem nE_secThL2 [CharP L 2] (μ : L) (X : Matrix (Fin 3) (Fin 3) L) :
    nE 0 (nE 1 (nE 3 (nE 2 (secThL μ 2 X)))) = secThL μ 0 X := by
  have h := secThL_conj_of_single μ (j := 2) (j' := 0)
    (nE (L := L) 0 * nE 1 * nE 3 * nE 2) 1 1
    (fun a b => by
      rw [Matrix.one_mul, Matrix.mul_one, secThL_single]
      simp only [Module.End.mul_apply]
      exact nE_secTh2 μ a b) X
  rwa [Matrix.one_mul, Matrix.mul_one] at h

theorem coe_canonicalRep_secW_two (v : RootModule TwistTag.D4.tag L) :
    (canonicalRep (coxeterSystem TwistTag.D4.tag) L (secW 2) :
      Module.End L (RootModule TwistTag.D4.tag L)) v = nE 0 (nE 1 (nE 3 (nE 2 v))) := by
  rw [canonicalRep_secW_two]
  rfl

theorem secOrbitX_zero_secThL [CharP L 2] (μ : Lˣ) (hμ : (μ : L) ^ 2 + μ + 1 = 0) (t : L)
    (X : Matrix (Fin 3) (Fin 3) L) :
    (secOrbitX μ 0 t : Module.End L (RootModule TwistTag.D4.tag L)) (secThL (μ : L) 0 X) =
      secThL (μ : L) 0 (Matrix.transvection 0 1 t * X * Matrix.transvection 0 1 (-t)) := by
  rw [secOrbitX_eq_conj (CharP.cast_eq_zero L 2), canonicalRep_secW_zero, inv_one, mul_one,
    one_mul, coe_xkU, secKappa_zero]
  exact secThL_conj_of_single _ _ _ _ (fun a b => xk_secTh0 _ hμ t a b) X

theorem secOrbitX_one_secThL [CharP L 2] (μ : Lˣ) (hμ : (μ : L) ^ 2 + μ + 1 = 0) (t : L)
    (X : Matrix (Fin 3) (Fin 3) L) :
    (secOrbitX μ 1 t : Module.End L (RootModule TwistTag.D4.tag L)) (secThL (μ : L) 0 X) =
      secThL (μ : L) 0 (Matrix.transvection 1 2 t * X * Matrix.transvection 1 2 (-t)) := by
  rw [secOrbitX_eq_conj (CharP.cast_eq_zero L 2), canonicalRep_secW_one, Units.val_mul,
    Units.val_mul, Module.End.mul_apply, Module.End.mul_apply, coe_xkU, secKappa_one,
    inv_apply_of_apply (nE_secThL1 (μ : L) X),
    secThL_conj_of_single _ _ _ _ (fun a b => xk_secTh1 _ hμ t a b) X]
  exact nE_secThL1 (μ : L) _

theorem secOrbitX_two_secThL [CharP L 2] (μ : Lˣ) (hμ : (μ : L) ^ 2 + μ + 1 = 0) (t : L)
    (X : Matrix (Fin 3) (Fin 3) L) :
    (secOrbitX μ 2 t : Module.End L (RootModule TwistTag.D4.tag L)) (secThL (μ : L) 0 X) =
      secThL (μ : L) 0 (Matrix.transvection 0 2 t * X * Matrix.transvection 0 2 (-t)) := by
  have hμ3 : μ ^ 3 = 1 := pow_three_of_sq_add hμ
  have hinv := inv_apply_of_apply (n := canonicalRep (coxeterSystem TwistTag.D4.tag) L (secW 2))
    (v := secThL (μ : L) 2 X) (w := secThL (μ : L) 0 X)
    (by rw [coe_canonicalRep_secW_two]; exact nE_secThL2 (μ : L) X)
  rw [secOrbitX_eq_conj (CharP.cast_eq_zero L 2), Units.val_mul, Units.val_mul,
    Module.End.mul_apply, Module.End.mul_apply, coe_xkU, secKappa_two hμ3, hinv,
    secThL_conj_of_single _ _ _ _ (fun a b => xk_secTh2 _ hμ t a b) X,
    coe_canonicalRep_secW_two]
  exact nE_secThL2 (μ : L) _

theorem secOrbitY_zero_secThL [CharP L 2] (μ : Lˣ) (hμ : (μ : L) ^ 2 + μ + 1 = 0) (t : L)
    (X : Matrix (Fin 3) (Fin 3) L) :
    (secOrbitY μ 0 t : Module.End L (RootModule TwistTag.D4.tag L)) (secThL (μ : L) 0 X) =
      secThL (μ : L) 0 (Matrix.transvection 1 0 t * X * Matrix.transvection 1 0 (-t)) := by
  rw [secOrbitY_eq_conj (CharP.cast_eq_zero L 2), canonicalRep_secW_zero, inv_one, mul_one,
    one_mul, coe_ykU, secKappa_zero]
  exact secThL_conj_of_single _ _ _ _ (fun a b => yk_secTh0 _ hμ t a b) X

theorem secOrbitY_one_secThL [CharP L 2] (μ : Lˣ) (hμ : (μ : L) ^ 2 + μ + 1 = 0) (t : L)
    (X : Matrix (Fin 3) (Fin 3) L) :
    (secOrbitY μ 1 t : Module.End L (RootModule TwistTag.D4.tag L)) (secThL (μ : L) 0 X) =
      secThL (μ : L) 0 (Matrix.transvection 2 1 t * X * Matrix.transvection 2 1 (-t)) := by
  rw [secOrbitY_eq_conj (CharP.cast_eq_zero L 2), canonicalRep_secW_one, Units.val_mul,
    Units.val_mul, Module.End.mul_apply, Module.End.mul_apply, coe_ykU, secKappa_one,
    inv_apply_of_apply (nE_secThL1 (μ : L) X),
    secThL_conj_of_single _ _ _ _ (fun a b => yk_secTh1 _ hμ t a b) X]
  exact nE_secThL1 (μ : L) _

theorem secOrbitY_two_secThL [CharP L 2] (μ : Lˣ) (hμ : (μ : L) ^ 2 + μ + 1 = 0) (t : L)
    (X : Matrix (Fin 3) (Fin 3) L) :
    (secOrbitY μ 2 t : Module.End L (RootModule TwistTag.D4.tag L)) (secThL (μ : L) 0 X) =
      secThL (μ : L) 0 (Matrix.transvection 2 0 t * X * Matrix.transvection 2 0 (-t)) := by
  have hμ3 : μ ^ 3 = 1 := pow_three_of_sq_add hμ
  have hinv := inv_apply_of_apply (n := canonicalRep (coxeterSystem TwistTag.D4.tag) L (secW 2))
    (v := secThL (μ : L) 2 X) (w := secThL (μ : L) 0 X)
    (by rw [coe_canonicalRep_secW_two]; exact nE_secThL2 (μ : L) X)
  rw [secOrbitY_eq_conj (CharP.cast_eq_zero L 2), Units.val_mul, Units.val_mul,
    Module.End.mul_apply, Module.End.mul_apply, coe_ykU, secKappa_two hμ3, hinv,
    secThL_conj_of_single _ _ _ _ (fun a b => yk_secTh2 _ hμ t a b) X,
    coe_canonicalRep_secW_two]
  exact nE_secThL2 (μ : L) _

theorem dv_apply (p q r s : ℤ) :
    dv p q r s 0 = p ∧ dv p q r s 1 = q ∧ dv p q r s 2 = r ∧ dv p q r s 3 = s :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem rootChar_dv {a : Fin TwistTag.D4.tag.rank → Lˣ} (ha1 : a 1 = a 0) (ha3 : a 3 = a 0)
    (p q r s : ℤ) : rootChar a (dv p q r s) = a 0 ^ (p + q + s) * a 2 ^ r := by
  have e : ∀ v : Fin TwistTag.D4.tag.rank → ℤ,
      rootChar a v = a 0 ^ v 0 * a 1 ^ v 1 * a 2 ^ v 2 * a 3 ^ v 3 := by
    intro v
    simp only [rootChar]
    exact Fin.prod_univ_four (fun i => a i ^ v i)
  obtain ⟨d0, d1, d2, d3⟩ := dv_apply p q r s
  rw [e, ha1, ha3, d0, d1, d2, d3, zpow_add, zpow_add, mul_assoc (a 0 ^ p * a 0 ^ q),
    mul_comm (a 2 ^ r), ← mul_assoc]

@[expose] def secTorD (a : Fin TwistTag.D4.tag.rank → Lˣ) : Matrix (Fin 3) (Fin 3) L :=
  Matrix.diagonal ![((a 0 : L)) ^ 2 * a 2, (a 0 : L) * a 2, 1]

@[expose] def secTorDinv (a : Fin TwistTag.D4.tag.rank → Lˣ) : Matrix (Fin 3) (Fin 3) L :=
  Matrix.diagonal ![((a 0 : L) ^ 2 * a 2)⁻¹, ((a 0 : L) * a 2)⁻¹, 1]

set_option maxHeartbeats 4000000 in
theorem rootDiag_secTh0 (μ : L) {a : Fin TwistTag.D4.tag.rank → Lˣ} (ha1 : a 1 = a 0)
    (ha3 : a 3 = a 0) (i j : Fin 3) :
    rootDiag a (secTh0 μ i j) = secThL μ 0 (secTorD a * Matrix.single i j 1 * secTorDinv a) := by
  have h0 : (a 0 : L) ≠ 0 := Units.ne_zero _
  have h2' : (a 2 : L) ≠ 0 := Units.ne_zero _
  fin_cases i <;> fin_cases j <;>
  · simp (disch := d4root) only [secTh0, map_add, map_smul, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
      Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, rootDiag_hVec, rootDiag_rootVec,
      rootChar_dv ha1 ha3]
    simp only [secThL_apply, secTh, secTh0, Fin.sum_univ_three, secTorD, secTorDinv,
      Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.single_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    simp
    all_goals (match_scalars <;> field_simp)

theorem rootDiagUnit_secThL (μ : L) {a : Fin TwistTag.D4.tag.rank → Lˣ} (ha1 : a 1 = a 0)
    (ha3 : a 3 = a 0) (X : Matrix (Fin 3) (Fin 3) L) :
    (rootDiagUnit TwistTag.D4.tag a : Module.End L (RootModule TwistTag.D4.tag L))
      (secThL μ 0 X) = secThL μ 0 (secTorD a * X * secTorDinv a) :=
  secThL_conj_of_single μ _ _ _ (fun i j => rootDiag_secTh0 μ ha1 ha3 i j) X

end CFSG.RankThree.PartTwo.Sec8.LangTwisted2Proof
