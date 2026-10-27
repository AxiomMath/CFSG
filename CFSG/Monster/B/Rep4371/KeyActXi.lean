module

public import CFSG.Monster.B.Rep4371.KeyAct

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.Rep4371

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice CFSG.Monster.Lifts
  CFSG.Monster.Visible CFSG.Monster.Xi CFSG.Monster.Griess CFSG.Monster.ScalarKernel Matrix

@[expose] noncomputable def xiSignPair : Pvis := xiPair * signPair 1

theorem xiSignPair_spin :
    (((xiSignPair : GL SpinIdx ℚ × latticeO).1 : GL SpinIdx ℚ) : Matrix SpinIdx SpinIdx ℚ) =
      Ximat * Ymat ⟨toC 1, 0⟩ := rfl

theorem xiSignPair_mat : mat (xiSignPair : GL SpinIdx ℚ × latticeO).2 = gXi * gmat (toC 1) := rfl

theorem C4_eq_c4N : ∀ r r' : Fin 4, C4 r r' = (Model.c4N r r' : ℚ) / 64 := by
  intro r r'
  rw [C4_eq]
  fin_cases r <;> fin_cases r' <;> norm_num [Model.c4N]

theorem gXi_gmat_apply (i l : Fin 24) :
    (gXi * gmat (toC 1)) i l = if Code.col i = Code.col l then
      (Model.c4N (Code.row i) (Code.row l) : ℚ) / 64 *
        ((Model.sgnI ((Model.bmaskN 0).testBit l) : ℤ) : ℚ) else 0 := by
  rw [gmat, mul_diagonal, gXi_apply, coe_toC_apply, sgn_boolZ]
  have hw : Model.wordN 1 = Model.bmaskN 0 := rfl
  rw [hw]
  split_ifs with h
  · rw [C4_eq_c4N]
  · rw [zero_mul]

theorem bmaskN_zero_testBit : ∀ l : Fin 24, (Model.bmaskN 0).testBit l =
    ![false, true, true, true, true, false, false, false, true, false, false, false,
      true, false, false, false, true, false, false, false, true, false, false, false] l := by
  decide

theorem wvec_vecMul_gXi : wvec ᵥ* (gXi * gmat (toC 1)) = -wvec := by
  funext l
  rw [wvec, sub_vecMul, single_one_vecMul, single_one_vecMul, Pi.sub_apply, Matrix.row_apply,
    Matrix.row_apply, gXi_gmat_apply, gXi_gmat_apply, Pi.neg_apply, Pi.sub_apply,
    bmaskN_zero_testBit]
  fin_cases l <;> simp [Code.col, Code.row, Model.c4N, Model.sgnI] <;> norm_num

theorem unitVec_vecMul_gXi {j : ℕ} (hj : j < 24) :
    unitVec j ᵥ* (gXi * gmat (toC 1)) = ∑ r' : Fin 4,
      ((Model.c4N (j % 4) r' : ℚ) / 64 *
        ((Model.sgnI ((Model.bmaskN 0).testBit (4 * (j / 4) + r')) : ℤ) : ℚ)) •
          unitVec (4 * (j / 4) + r') := by
  funext l
  rw [unitVec_eq_single hj, single_one_vecMul, Matrix.row_apply, gXi_gmat_apply,
    Finset.sum_apply]
  simp only [Pi.smul_apply, unitVec, smul_eq_mul, mul_ite, mul_one, mul_zero]
  have hl := l.2
  by_cases hc : Code.col ⟨j, hj⟩ = Code.col l
  · have hcol : (l : ℕ) / 4 = j / 4 := by
      have := congrArg Fin.val hc
      simp only [Code.col] at this
      omega
    rw [ite_eq_left hc]
    rw [Finset.sum_eq_single ⟨(l : ℕ) % 4, Nat.mod_lt _ (by norm_num)⟩]
    · have e : (l : ℕ) = 4 * (j / 4) + (l : ℕ) % 4 := by omega
      rw [ite_eq_left e]
      simp only [Code.row]
      rw [← e]
    · intro r' _ hr'
      refine ite_eq_right fun h => hr' (Fin.ext ?_)
      simp only
      omega
    · simp
  · rw [ite_eq_right hc]
    refine (Finset.sum_eq_zero fun r' _ => ite_eq_right fun h => hc ?_).symm
    apply Fin.ext
    simp only [Code.col]
    omega

theorem interp_range_map (D : ℚ) (f : ℕ → Model.Key × ℤ) :
    ∀ n, interp D ((List.range n).map f) = ∑ i : Fin n, (((f i).2 : ℚ) / D) • keyVec (f i).1
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.map_append, interp_append, interp_range_map D f n,
      Fin.sum_univ_castSucc, List.map_singleton, interp_cons, interp_nil, add_zero]
    rfl

theorem Evec_vecMul_XiG_Ymat (η : Bool) (c : ℕ) :
    Evec η c ᵥ* XiG ᵥ* Ymat ⟨toC 1, 0⟩ = (1 / 8 : ℚ) • ∑ n : Fin 64,
      sgn (boolZ ((Model.xiGTerm η c n).1 ^^
        (Model.eYN 1 (Model.xiGTerm η c n).2.1 (Model.xiGTerm η c n).2.2).1)) •
        Evec (Model.eYN 1 (Model.xiGTerm η c n).2.1 (Model.xiGTerm η c n).2.2).2.1
          (Model.eYN 1 (Model.xiGTerm η c n).2.1 (Model.xiGTerm η c n).2.2).2.2 := by
  rw [Evec_vecMul_XiG, smul_vecMul, sum_vecMul]
  congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [smul_vecMul, Evec_vecMul_Ymat, smul_smul, ← sgn_add, ← boolZ_xor]

theorem combine_xi (a b : ℚ) (u v : Fin 64 → ℚ) (F G : Fin 64 → SpinIdx → ℚ) :
    (1 / 8 : ℚ) • (a • ((1 / 8 : ℚ) • ∑ n, u n • F n) + b • ((1 / 8 : ℚ) • ∑ n, v n • G n)) =
      ∑ n, ((a * u n) / 64) • F n + ∑ n, ((b * v n) / 64) • G n := by
  rw [smul_add, Finset.smul_sum, Finset.smul_sum, Finset.smul_sum, Finset.smul_sum,
    Finset.smul_sum, Finset.smul_sum]
  congr 1 <;> refine Finset.sum_congr rfl fun n _ => ?_ <;> rw [smul_smul, smul_smul, smul_smul] <;>
    congr 1 <;> ring

@[expose] noncomputable def xiCoef (η : Bool) (c : ℕ) (e : Bool) (n : ℕ) : ℚ :=
  (Model.xiGammaN c e : ℚ) * sgn (boolZ ((Model.xiGTerm (η ^^ e) c n).1 ^^
    (Model.eYN 1 (Model.xiGTerm (η ^^ e) c n).2.1 (Model.xiGTerm (η ^^ e) c n).2.2).1))

@[expose] noncomputable def xiVec (η : Bool) (c : ℕ) (e : Bool) (n : ℕ) : SpinIdx → ℚ :=
  Evec (Model.eYN 1 (Model.xiGTerm (η ^^ e) c n).2.1 (Model.xiGTerm (η ^^ e) c n).2.2).2.1
    (Model.eYN 1 (Model.xiGTerm (η ^^ e) c n).2.1 (Model.xiGTerm (η ^^ e) c n).2.2).2.2

theorem Evec_vecMul_xiSign (η : Bool) (c : ℕ) :
    Evec η c ᵥ* (Ximat * Ymat ⟨toC 1, 0⟩) =
      ∑ n : Fin 64, (xiCoef η c false n / 64) • xiVec η c false n +
        ∑ n : Fin 64, (xiCoef η c true n / 64) • xiVec η c true n := by
  rw [← vecMul_vecMul, Ximat, ← vecMul_vecMul, Evec_vecMul_XiGamma]
  simp only [smul_vecMul, add_vecMul]
  rw [Evec_vecMul_XiG_Ymat, Evec_vecMul_XiG_Ymat, combine_xi]
  simp only [xiCoef, xiVec, Bool.xor_false, Bool.xor_true, mul_div_assoc]

theorem keyAct_xi_sound (κ : Model.Key) (hκ : KeyValid κ) :
    thetaEquiv xiSignPair (keyVec κ) = interp 64 (Model.keyActXi κ) := by
  rw [thetaEquiv_apply]
  obtain ⟨t, x, y⟩ := κ
  rcases t with _ | _ | t
  · have hj : x < 24 := hκ rfl
    have hk : Model.keyActXi (0, x, y) = (List.range 4).map fun r' =>
        (Model.Key.A (4 * (x / 4) + r'), -(Model.c4N (x % 4) r' *
          Model.sgnI ((Model.bmaskN 0).testBit (4 * (x / 4) + r')))) := rfl
    rw [theta_keyVec_A, xiSignPair_mat, wvec_vecMul_gXi, unitVec_vecMul_gXi hj,
      ← neg_one_smul ℚ wvec, crossMat_smul_left, crossMat_sum_right, Finset.smul_sum, inA_sum, hk,
      interp_range_map]
    refine Finset.sum_congr rfl fun r' _ => ?_
    rw [crossMat_smul_right, smul_smul, inA_smul, keyVec_A]
    congr 1
    push_cast
    ring
  · have hk : Model.keyActXi (1, x, y) =
        [Model.signedTerm (Model.Key.X (Model.conjYN 1 (Model.conjXiN (false, x, y))).a
          (Model.conjYN 1 (Model.conjXiN (false, x, y))).d)
            (Model.conjYN 1 (Model.conjXiN (false, x, y))).s] := rfl
    rw [theta_keyVec_X, xiSignPair, conjQ_mul, conjQ_xi_toQ, hk]
    exact (congrArg (fun r => inX (Xlift r)) (conjQ_sign_toQ 1 _)).trans (keyVec_X_conj _)
  · set η := x != 0
    have hk : Model.keyActXi (t + 2, x, y) =
        (List.range 64).map (fun ν => (Model.Key.W
          (Model.eYN 1 (Model.xiGTerm (η ^^ false) y ν).2.1 (Model.xiGTerm (η ^^ false) y ν).2.2).2.1
          (Model.eYN 1 (Model.xiGTerm (η ^^ false) y ν).2.1 (Model.xiGTerm (η ^^ false) y ν).2.2).2.2,
          -(Model.xiGammaN y false * Model.sgnI ((Model.xiGTerm (η ^^ false) y ν).1 ^^
            (Model.eYN 1 (Model.xiGTerm (η ^^ false) y ν).2.1
              (Model.xiGTerm (η ^^ false) y ν).2.2).1)))) ++
        (List.range 64).map (fun ν => (Model.Key.W
          (Model.eYN 1 (Model.xiGTerm (η ^^ true) y ν).2.1 (Model.xiGTerm (η ^^ true) y ν).2.2).2.1
          (Model.eYN 1 (Model.xiGTerm (η ^^ true) y ν).2.1 (Model.xiGTerm (η ^^ true) y ν).2.2).2.2,
          -(Model.xiGammaN y true * Model.sgnI ((Model.xiGTerm (η ^^ true) y ν).1 ^^
            (Model.eYN 1 (Model.xiGTerm (η ^^ true) y ν).2.1
              (Model.xiGTerm (η ^^ true) y ν).2.2).1)))) := by
      show ([false, true].flatMap fun f => (List.range 64).map fun ν => _) = _
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      rfl
    rw [theta_keyVec_W, xiSignPair_spin, xiSignPair_mat, wvec_vecMul_gXi, Evec_vecMul_xiSign, hk,
      interp_append, interp_range_map, interp_range_map, ← neg_one_smul ℚ wvec, tensor_smul_right,
      inW_smul, tensor_add_left, tensor_sum_left, tensor_sum_left]
    have hW : ∀ (s : Fin 64 → ℚ) (F : Fin 64 → SpinIdx → ℚ),
        inW (∑ n, tensor (s n • F n) wvec) = ∑ n, s n • inW (tensor (F n) wvec) := by
      intro s F
      rw [inW_sum]
      exact Finset.sum_congr rfl fun n _ => by rw [tensor_smul_left, inW_smul]
    have hadd : ∀ x y : SpaceW, inW (x + y) = inW x + inW y := fun x y => by
      simp [inW, Prod.mk_add_mk]
    rw [hadd, hW, hW, smul_add, Finset.smul_sum, Finset.smul_sum]
    have hc : ∀ (e : Bool) (n : ℕ), (-1 : ℚ) * (xiCoef η y e n / 64) =
        ((-(Model.xiGammaN y e * Model.sgnI ((Model.xiGTerm (η ^^ e) y n).1 ^^
          (Model.eYN 1 (Model.xiGTerm (η ^^ e) y n).2.1 (Model.xiGTerm (η ^^ e) y n).2.2).1)) :
            ℤ) : ℚ) / 64 := by
      intro e n
      rw [xiCoef, sgn_boolZ]
      push_cast
      ring
    congr 1
    · refine Finset.sum_congr rfl fun n _ => ?_
      rw [smul_smul, hc, xiVec, keyVec_W]
    · refine Finset.sum_congr rfl fun n _ => ?_
      rw [smul_smul, hc, xiVec, keyVec_W]

end CFSG.Monster.B.Rep4371
