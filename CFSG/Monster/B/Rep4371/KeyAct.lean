module

public import CFSG.Monster.B.Rep4371.Interp

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.Rep4371

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice CFSG.Monster.Lifts
  CFSG.Monster.Visible CFSG.Monster.Xi CFSG.Monster.Griess CFSG.Monster.ScalarKernel Matrix

theorem thetaA_crossMat (g : Matrix (Fin 24) (Fin 24) ℚ) (u v : Fin 24 → ℚ) :
    Visible.thetaA g (crossMat u v) = crossMat (u ᵥ* g) (v ᵥ* g) := by
  apply Subtype.ext
  rw [coe_thetaA, coe_crossMat, coe_crossMat, Matrix.mul_add, Matrix.add_mul, mul_vecMulVec,
    mul_vecMulVec, vecMulVec_mul, vecMulVec_mul, mulVec_transpose, mulVec_transpose]

theorem crossMat_smul_left (c : ℚ) (u v : Fin 24 → ℚ) :
    crossMat (c • u) v = c • crossMat u v := by
  apply Subtype.ext
  rw [coe_crossMat, Submodule.coe_smul, coe_crossMat, smul_vecMulVec, vecMulVec_smul, smul_add]

theorem crossMat_smul_right (c : ℚ) (u v : Fin 24 → ℚ) :
    crossMat u (c • v) = c • crossMat u v := by
  apply Subtype.ext
  rw [coe_crossMat, Submodule.coe_smul, coe_crossMat, smul_vecMulVec, vecMulVec_smul, smul_add]

theorem crossMat_add_right (u v v' : Fin 24 → ℚ) :
    crossMat u (v + v') = crossMat u v + crossMat u v' := by
  apply Subtype.ext
  rw [coe_crossMat, Submodule.coe_add, coe_crossMat, coe_crossMat, vecMulVec_add, add_vecMulVec]
  abel

theorem crossMat_sum_right {ι : Type*} (s : Finset ι) (u : Fin 24 → ℚ) (v : ι → Fin 24 → ℚ) :
    crossMat u (∑ i ∈ s, v i) = ∑ i ∈ s, crossMat u (v i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    apply Subtype.ext
    simp [coe_crossMat]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, crossMat_add_right, ih]

theorem tensor_smul_left (c : ℚ) (q : SpinIdx → ℚ) (v : Fin 24 → ℚ) :
    tensor (c • q) v = c • tensor q v := smul_vecMulVec c q v

theorem tensor_smul_right (c : ℚ) (q : SpinIdx → ℚ) (v : Fin 24 → ℚ) :
    tensor q (c • v) = c • tensor q v := by
  ext i j
  simp only [tensor, vecMulVec_apply, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul]
  ring

theorem tensor_add_left (q q' : SpinIdx → ℚ) (v : Fin 24 → ℚ) :
    tensor (q + q') v = tensor q v + tensor q' v := add_vecMulVec q q' v

theorem tensor_sum_left {ι : Type*} (s : Finset ι) (q : ι → SpinIdx → ℚ) (v : Fin 24 → ℚ) :
    tensor (∑ i ∈ s, q i) v = ∑ i ∈ s, tensor (q i) v := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [tensor]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, tensor_add_left, ih]

theorem inA_smul (c : ℚ) (A : symMat) : inA (c • A) = c • inA A := by
  simp [inA, Prod.smul_mk]

theorem inA_sum {ι : Type*} (s : Finset ι) (A : ι → symMat) :
    inA (∑ i ∈ s, A i) = ∑ i ∈ s, inA (A i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, ← ih]
    simp [inA, Prod.mk_add_mk]

theorem inX_smul (c : ℚ) (x : SpaceX) : inX (c • x) = c • inX x := by
  simp [inX, Prod.smul_mk]

theorem inW_smul (c : ℚ) (N : SpaceW) : inW (c • N) = c • inW N := by
  simp [inW, Prod.smul_mk]

theorem inW_sum {ι : Type*} (s : Finset ι) (N : ι → SpaceW) :
    inW (∑ i ∈ s, N i) = ∑ i ∈ s, inW (N i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, ← ih]
    simp [inW, Prod.mk_add_mk]

theorem interp_signedTerm (κ : Model.Key) (s : Bool) :
    interp 64 [Model.signedTerm κ s] = sgn (boolZ s) • keyVec κ := by
  rw [interp_cons, interp_nil, add_zero, Model.signedTerm, sgn_boolZ]
  congr 1
  push_cast
  ring

theorem Xlift_pauliQ (y : Model.Pauli) :
    Xlift (pauliQ y) = sgn (boolZ y.s) • Xlift (pauliQ (false, y.a, y.d)) := by
  refine Visible.Xlift_eq_sgn_smul ?_ ?_
  · rw [pauliQ, pauliQ, Griess.coordOf_spinEquiv, Griess.coordOf_spinEquiv]
    rfl
  · rw [pauliQ, pauliQ, Griess.centralCoord_spinEquiv, Griess.centralCoord_spinEquiv, toSC_s,
      toSC_s, pauli_s, boolZ_false, add_zero]

theorem theta_keyVec_A (p : Pvis) (j x : ℕ) :
    theta p (keyVec (0, j, x)) = inA (crossMat (wvec ᵥ* mat p.1.2) (unitVec j ᵥ* mat p.1.2)) := by
  rw [keyVec_zero, theta_symMat, thetaA_crossMat]

theorem theta_keyVec_X (p : Pvis) (a d : ℕ) :
    theta p (keyVec (1, a, d)) = inX (Xlift (conjQ p (pauliQ (false, a, d)))) := by
  rw [keyVec_one, theta_Xlift]

theorem theta_keyVec_W (p : Pvis) (t e c : ℕ) :
    theta p (keyVec (t + 2, e, c)) =
      inW (tensor (Evec (e != 0) c ᵥ* (p.1.1 : Matrix SpinIdx SpinIdx ℚ)) (wvec ᵥ* mat p.1.2)) := by
  rw [keyVec_two, theta_tensor]

theorem keyVec_X_conj (y : Model.Pauli) :
    inX (Xlift (pauliQ y)) = interp 64 [Model.signedTerm (Model.Key.X y.a y.d) y.s] := by
  rw [interp_signedTerm, Xlift_pauliQ, inX_smul, keyVec_X]

theorem interp_A64 (j : ℕ) : interp 64 [(Model.Key.A j, 64)] = keyVec (Model.Key.A j) := by
  rw [interp_cons, interp_nil, add_zero]
  norm_num

theorem keyAct_pauli_sound (q : Model.Pauli) (κ : Model.Key) :
    rhoEquiv (pauliQ q) (keyVec κ) = interp 64 (Model.keyActPauli q κ) := by
  rw [rhoEquiv, thetaEquiv_apply]
  obtain ⟨t, x, y⟩ := κ
  rcases t with _ | _ | t
  · have hk : Model.keyActPauli q (0, x, y) = [(Model.Key.A x, 64)] := rfl
    rw [theta_keyVec_A, coe_rhoPair, mat_one, vecMul_one, vecMul_one, hk, interp_A64, keyVec_A]
  · have hk : Model.keyActPauli q (1, x, y) =
        [Model.signedTerm (Model.Key.X (Model.conjPauliN q (false, x, y)).a
          (Model.conjPauliN q (false, x, y)).d) (Model.conjPauliN q (false, x, y)).s] := rfl
    rw [theta_keyVec_X, conjQ_rhoPair_toQ, hk, ← keyVec_X_conj]
  · have hk : Model.keyActPauli q (t + 2, x, y) =
        [Model.signedTerm (Model.Key.W (Model.ePauliN q (x != 0) y).2.1
          (Model.ePauliN q (x != 0) y).2.2) (Model.ePauliN q (x != 0) y).1] := rfl
    rw [theta_keyVec_W, coe_rhoPair, mat_one, vecMul_one, qmatR_toSC_eq, Evec_vecMul_qmatR,
      tensor_smul_left, inW_smul, hk, interp_signedTerm, keyVec_W]

theorem wvec_vecMul_Pmat (p : Equiv.Perm (Fin 24)) {arr : Array ℕ} (hp : RepPerm p arr)
    (hw : (arr[0]! = 0 ∧ arr[1]! = 1) ∨ (arr[0]! = 1 ∧ arr[1]! = 0)) :
    wvec ᵥ* Pmat p = ((Model.sgnI (arr[0]! != 0) : ℤ) : ℚ) • wvec := by
  have h0 := hp 0
  have h1 := hp 1
  rw [wvec, sub_vecMul, single_vecMul_Pmat, single_vecMul_Pmat]
  rcases hw with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · have e0 : p 0 = 0 := Fin.ext (by rw [h0]; exact ha)
    have e1 : p 1 = 1 := Fin.ext (by rw [h1]; exact hb)
    rw [e0, e1, ha]
    simp [Model.sgnI]
  · have e0 : p 0 = 1 := Fin.ext (by rw [h0]; exact ha)
    have e1 : p 1 = 0 := Fin.ext (by rw [h1]; exact hb)
    rw [e0, e1, ha]
    simp only [Model.sgnI, bne_iff_ne, ne_eq, one_ne_zero, not_false_eq_true,
      ite_true, Int.reduceNeg, Int.cast_neg, Int.cast_one, neg_smul, one_smul, neg_sub]

theorem keyAct_perm_sound (p : AutPerm) {arr : Array ℕ} (hp : RepPerm p arr)
    (hw : (arr[0]! = 0 ∧ arr[1]! = 1) ∨ (arr[0]! = 1 ∧ arr[1]! = 0)) (κ : Model.Key)
    (hκ : KeyValid κ) :
    thetaEquiv ⟨(sU p, PO p), sU_PO_mem_Pvis p⟩ (keyVec κ) =
      interp 64 (Model.keyActPerm arr κ) := by
  rw [thetaEquiv_apply]
  obtain ⟨t, x, y⟩ := κ
  rcases t with _ | _ | t
  · have hj : x < 24 := hκ rfl
    have hk : Model.keyActPerm arr (0, x, y) =
        [(Model.Key.A arr[x]!, Model.sgnI (arr[0]! != 0) * 64)] := rfl
    rw [theta_keyVec_A]
    show inA (crossMat (wvec ᵥ* Pmat p) (unitVec x ᵥ* Pmat p)) = _
    rw [wvec_vecMul_Pmat p hp hw, unitVec_eq_single hj, single_vecMul_Pmat, crossMat_smul_left,
      inA_smul, hk, interp_cons, interp_nil, add_zero, keyVec_A]
    have hpj : ((p : Equiv.Perm (Fin 24)) ⟨x, hj⟩ : ℕ) = arr[x]! := hp ⟨x, hj⟩
    have hu : Pi.single ((p : Equiv.Perm (Fin 24)) ⟨x, hj⟩) (1 : ℚ) = unitVec arr[x]! := by
      rw [← hpj, unitVec_eq_single ((p : Equiv.Perm (Fin 24)) ⟨x, hj⟩).2]
    rw [hu]
    congr 1
    push_cast
    ring
  · have hk : Model.keyActPerm arr (1, x, y) =
        [Model.signedTerm (Model.Key.X (Model.conjPermN arr (false, x, y)).a
          (Model.conjPermN arr (false, x, y)).d) (Model.conjPermN arr (false, x, y)).s] := rfl
    rw [theta_keyVec_X, conjQ_perm_toQ p hp, hk, ← keyVec_X_conj]
  · have hk : Model.keyActPerm arr (t + 2, x, y) =
        [Model.signedTerm (Model.Key.W (Model.ePermN arr (x != 0) y).2.1
          (Model.ePermN arr (x != 0) y).2.2) ((Model.ePermN arr (x != 0) y).1 ^^
            (arr[0]! != 0))] := rfl
    rw [theta_keyVec_W]
    show inW (tensor (Evec (x != 0) y ᵥ* smat p) (wvec ᵥ* Pmat p)) = _
    rw [wvec_vecMul_Pmat p hp hw, Evec_vecMul_smat p hp, tensor_smul_left, tensor_smul_right,
      smul_smul, inW_smul, hk, interp_signedTerm, sgn_boolZ, sgn_boolZ, sgnI_xor, keyVec_W]

theorem wvec_vecMul_gmat (a : ℕ) (ha : (Model.wordN a).testBit 0 = (Model.wordN a).testBit 1) :
    wvec ᵥ* gmat (toC a) = sgn (boolZ ((Model.wordN a).testBit 0)) • wvec := by
  rw [wvec, sub_vecMul, single_vecMul_gmat, single_vecMul_gmat, coe_toC_apply, coe_toC_apply,
    smul_sub]
  congr 2
  exact congrArg (fun b => sgn (boolZ b)) ha.symm

@[expose] noncomputable def signPair (a : ℕ) : Pvis :=
  ⟨(YU ⟨toC a, 0⟩, gO (toC a)), YU_gO_mem_Pvis ⟨toC a, 0⟩⟩

theorem keyAct_sign_sound (a : ℕ) (ha : (Model.wordN a).testBit 0 = (Model.wordN a).testBit 1)
    (κ : Model.Key) (hκ : KeyValid κ) :
    thetaEquiv (signPair a) (keyVec κ) = interp 64 (Model.keyActSign a κ) := by
  rw [thetaEquiv_apply]
  obtain ⟨t, x, y⟩ := κ
  rcases t with _ | _ | t
  · have hj : x < 24 := hκ rfl
    have hk : Model.keyActSign a (0, x, y) =
        [Model.signedTerm (Model.Key.A x) ((Model.wordN a).testBit 0 ^^
          (Model.wordN a).testBit x)] := rfl
    rw [theta_keyVec_A]
    show inA (crossMat (wvec ᵥ* gmat (toC a)) (unitVec x ᵥ* gmat (toC a))) = _
    rw [wvec_vecMul_gmat a ha, unitVec_eq_single hj, single_vecMul_gmat, crossMat_smul_left,
      crossMat_smul_right, smul_smul, inA_smul, hk, interp_signedTerm, coe_toC_apply, sgn_boolZ,
      sgn_boolZ, sgn_boolZ, sgnI_xor, ← unitVec_eq_single hj, keyVec_A]
  · have hk : Model.keyActSign a (1, x, y) =
        [Model.signedTerm (Model.Key.X (Model.conjYN a (false, x, y)).a
          (Model.conjYN a (false, x, y)).d) (Model.conjYN a (false, x, y)).s] := rfl
    rw [theta_keyVec_X, hk]
    exact (congrArg (fun r => inX (Xlift r)) (conjQ_sign_toQ a _)).trans (keyVec_X_conj _)
  · have hk : Model.keyActSign a (t + 2, x, y) =
        [Model.signedTerm (Model.Key.W (Model.eYN a (x != 0) y).2.1
          (Model.eYN a (x != 0) y).2.2) ((Model.eYN a (x != 0) y).1 ^^
            (Model.wordN a).testBit 0)] := rfl
    rw [theta_keyVec_W]
    show inW (tensor (Evec (x != 0) y ᵥ* Ymat ⟨toC a, 0⟩) (wvec ᵥ* gmat (toC a))) = _
    rw [wvec_vecMul_gmat a ha, Evec_vecMul_Ymat, tensor_smul_left, tensor_smul_right, smul_smul,
      inW_smul, hk, interp_signedTerm, sgn_boolZ, sgn_boolZ, sgn_boolZ, sgnI_xor, keyVec_W]

end CFSG.Monster.B.Rep4371
