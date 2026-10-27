
module

public import CFSG.Monster.B.TwoA.Sp8.GenActionDiffBase

public import CFSG.Monster.B.TwoA.Sp8.GenActionLifts
public import Certificates.Data.CFSGNative.MonsterB.Sp8Check
public meta import Certificates.Data.CFSGNative.MonsterB.Sp8Check
public meta import CFSG.Monster.B.Rep4371.GlueDefs
public meta import CFSG.Monster.B.TwoA.Sp8.GenActionLifts
public import CFSG.Monster.B.TwoA.Sp8.GenActionDiffInputs
public import Certificates.Certificate3073
public import CFSG.Monster.B.TwoA.Sp8.A8Inputs
public import CFSG.Monster.B.TwoA.Base.WCls
public import CFSG.Monster.B.TwoA.Census.PermBFS
public import CFSG.Monster.B.TwoA.Co2Inv.Data
public import CFSG.Monster.B.TwoA.Co2Inv.RowsInputs

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Sp8

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short
  CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Co2Inv CFSG.Monster.B.Rep4371
  CFSG.Monster.Lifts CFSG.Monster.VisQuot CFSG.Monster.ScalarKernel CFSG.Monster.Xi Matrix

theorem slPair_mul_rhoPair (r : Q) : slPair * rhoPair r = rhoPair
    (conjQ slPair r) * slPair :=
  mul_eq_of_inv_mul_mul slPair_mul_self (Census.inv_mul_rhoPair_mul slPair r)

theorem pauliDiff_check : ∀ k < 23,
    Model.conjYN 3 (pauliGen k) = Model.Pauli.mul (pauliGen k) (gDiff k) :=
  Certificates.certificate3073.1

theorem slPair_mul_pauli {k : ℕ}
    (hk : k < 23) :
    slPair * rhoPair (pauliQ (pauliGen k)) =
      rhoPair (pauliQ (pauliGen k)) * rhoPair (pauliQ (gDiff k)) * slPair := by
  have e1 : conjQ slPair (pauliQ (pauliGen k)) = pauliQ (pauliGen k) * pauliQ (gDiff k) :=
    (conjQ_slPair_pauliQ _).trans ((congrArg pauliQ (pauliDiff_check k hk)).trans (pauliQ_mul _ _))
  calc slPair * rhoPair (pauliQ (pauliGen k))
      = rhoPair (conjQ slPair (pauliQ (pauliGen k))) * slPair := slPair_mul_rhoPair _
    _ = rhoPair (pauliQ (pauliGen k) * pauliQ (gDiff k)) * slPair :=
        congrArg (fun x => rhoPair x * slPair) e1
    _ = rhoPair (pauliQ (pauliGen k)) * rhoPair (pauliQ (gDiff k)) * slPair :=
        congrArg (· * slPair) (map_mul rhoPair _ _)

theorem permRows_native : ∀ j < 9,
    Native.Sp8.rowChainEq (Native.eYN 3 :: permFs Native.ePermN Native.ePauliN Native.kappaN j)
      (permFs Native.ePermN Native.ePauliN Native.kappaN j ++
        [Native.ePauliN (gDiff (23 + j)), Native.eYN 3]) = true :=
  Certificates.certificate3073.2.1

theorem permRows_model {j : ℕ} (hj : j < 9) :
    Native.Sp8.rowChainEq (Model.eYN 3 :: permFs Model.ePermN Model.ePauliN Model.kappaN j)
      (permFs Model.ePermN Model.ePauliN Model.kappaN j ++
        [Model.ePauliN (gDiff (23 + j)), Model.eYN 3]) = true := by
  have h := permRows_native j hj
  rwa [native_eYN, native_ePermN, native_ePauliN, native_kappaN] at h

theorem gO_comm_PO (j : Fin 9) :
    gO (toC 3) * PO (fAut j) = PO (fAut j) * gO (toC 3) := by
  rw [gO_mul_PO, permC_toC _ (repPerm_fAut j), permCN_three j j.2]

theorem gPair_fAut_fst (j : Fin 9) :
    (((gPair (fAut j) : Pvis) : GL SpinIdx ℚ × latticeO).1 : Matrix SpinIdx SpinIdx ℚ) =
      [smat (fAut j), qmatR ℚ (boolZ (epsQ j).s) (toC (epsQ j).a) (toD (epsQ j).d)].prod := by
  rw [gPair_fAut, pvis_fst_mul, rhoPair_fst, List.prod_cons, List.prod_cons, List.prod_nil,
    mul_one, ← qmatR_toSC_eq]
  rfl

theorem gPair_fAut_snd (j : Fin 9) :
    ((gPair (fAut j) : Pvis) : GL SpinIdx ℚ × latticeO).2 = PO (fAut j) := by
  rw [gPair_fAut, pvis_snd_mul, rhoPair_snd, mul_one]
  rfl

theorem slPair_mul_gPair (j : Fin 9)
    :
    slPair * gPair (fAut j) = gPair (fAut j) * rhoPair (pauliQ (gDiff (23 + j))) * slPair := by
  refine slPair_mul_eq_of_rows (gPair_fAut_fst j)
    (.cons (rowOK_smat _ (repPerm_fAut j)) (.cons (rowOK_qmatR (epsQ j)) .nil))
    _ (permRows_model j.2) ?_
  rw [gPair_fAut_snd]
  exact gO_comm_PO j

theorem signRows_native : ∀ j < 11,
    Native.Sp8.rowChainEq (Native.eYN 3 :: signFs Native.eYN j)
      (signFs Native.eYN j ++ [Native.ePauliN (gDiff (32 + j)), Native.eYN 3]) = true :=
  Certificates.certificate3073.2.2.1

theorem signRows_model {j : ℕ} (hj : j < 11) :
    Native.Sp8.rowChainEq (Model.eYN 3 :: signFs Model.eYN j)
      (signFs Model.eYN j ++ [Model.ePauliN (gDiff (32 + j)), Model.eYN 3]) = true := by
  have h := signRows_native j hj
  rwa [native_eYN, native_ePauliN] at h

theorem slPair_mul_signProd {j : ℕ} (hj : j < 11) :
    slPair * signProd (signCodesOf j) =
      signProd (signCodesOf j) * rhoPair (pauliQ (gDiff (32 + j))) * slPair := by
  refine slPair_mul_eq_of_rows (signProd_fst _) (forall₂_signFs j) _ (signRows_model hj) ?_
  rw [signProd_snd]
  exact gO_comm _ _

theorem xiKeyCheck_native :
    Native.Sp8.xiKeyCheck (gDiff 43) = true :=
  Certificates.certificate3073.2.2.2

theorem xiKeyRow_model {η : Bool} {c : ℕ} (hc : c < 4096) :
    (Model.actVec (Model.keyActSign 3) [(Model.Key.W η c, 1)]).all
        (fun e => e.1.1 != 0) = true ∧
      (Model.actVec (Model.keyActPauli (gDiff 43))
        (Model.actVec Model.keyActXi [(Model.Key.W η c, 1)])).all (fun e => e.1.1 != 0) = true ∧
      Model.eqModel 4096 (Model.actVec Model.keyActXi
          (Model.actVec (Model.keyActSign 3) [(Model.Key.W η c, 1)])) 262144
        (Model.actVec (Model.keyActSign 3) (Model.actVec (Model.keyActPauli (gDiff 43))
          (Model.actVec Model.keyActXi [(Model.Key.W η c, 1)]))) = true := by
  have h := xiKeyCheck_native
  simp only [Native.Sp8.xiKeyCheck, List.all_eq_true, List.mem_range, List.mem_cons,
    List.not_mem_nil, or_false] at h
  have h1 := h c hc η (by cases η <;> simp)
  simp only [Native.Sp8.xiKeyRow, Native.Sp8.noAKeys, Bool.and_eq_true] at h1
  rw [native_actVec, native_keyActSign, native_keyActXi, native_keyActPauli, native_eqModel,
    native_Key_W] at h1
  exact ⟨h1.1.1, h1.1.2, h1.2⟩

theorem xi_key {η : Bool} {c : ℕ} (hc : c < 4096) :
    theta (slPair * xiSignPair) (keyVec (Model.Key.W η c)) =
      theta (xiSignPair * rhoPair (pauliQ (gDiff 43)) * slPair) (keyVec (Model.Key.W η c)) := by
  obtain ⟨hl, hr, he⟩ := xiKeyRow_model (η := η) hc
  rw [List.all_eq_true] at hl hr
  have hv : ∀ e ∈ [(Model.Key.W η c, (1 : ℤ))], KeyValid e.1 := fun e he => by
    rw [List.mem_singleton] at he
    subst he
    exact fun h0 => absurd (show (2 : ℕ) = 0 from h0) (by decide)
  have L : theta (slPair * xiSignPair) (keyVec (Model.Key.W η c)) =
      interp (1 * 64 * 64) (Model.actVec Model.keyActXi
        (Model.actVec (Model.keyActSign 3) [(Model.Key.W η c, 1)])) :=
    (theta_mul_apply _ _ _).trans ((congrArg (theta xiSignPair)
      ((congrArg (theta slPair) (keyVec_eq_interp _)).trans
        (interp_actVec _ (theta slPair) 1 _ fun e he => theta_slPair_key _ (hv e he)))).trans
      (interp_actVec _ (theta xiSignPair) _ _ fun e he =>
        theta_xi_key _ (keyValid_of_ne (hl e he))))
  have R : theta (xiSignPair * rhoPair (pauliQ (gDiff 43)) * slPair)
      (keyVec (Model.Key.W η c)) =
      interp (1 * 64 * 64 * 64) (Model.actVec (Model.keyActSign 3)
        (Model.actVec (Model.keyActPauli (gDiff 43))
          (Model.actVec Model.keyActXi [(Model.Key.W η c, 1)]))) :=
    (theta_mul_apply _ _ _).trans ((congrArg (theta slPair)
      ((theta_mul_apply _ _ _).trans ((congrArg (theta (rhoPair (pauliQ (gDiff 43))))
        ((congrArg (theta xiSignPair) (keyVec_eq_interp _)).trans
          (interp_actVec _ (theta xiSignPair) 1 _ fun e he => theta_xi_key _ (hv e he)))).trans
        (interp_actVec _ (theta (rhoPair (pauliQ (gDiff 43)))) _ _ fun e _ =>
          theta_rhoPair_key _ _)))).trans
      (interp_actVec _ (theta slPair) _ _ fun e he =>
        theta_slPair_key _ (keyValid_of_ne (hr e he))))
  have e1 : ((1 : ℚ) * 64 * 64) = ((4096 : ℤ) : ℚ) := by norm_num
  have e2 : ((1 : ℚ) * 64 * 64 * 64) = ((262144 : ℤ) : ℚ) := by norm_num
  rw [e1] at L
  rw [e2] at R
  exact L.trans ((eqModel_sound (by norm_num) (by norm_num) he).trans R.symm)

theorem slPair_mul_xi :
    slPair * xiSignPair = xiSignPair * rhoPair (pauliQ (gDiff 43)) * slPair := by
  have hlat : ((slPair * xiSignPair : Pvis) : GL SpinIdx ℚ × latticeO).2 =
      ((xiSignPair * rhoPair (pauliQ (gDiff 43)) * slPair : Pvis) :
        GL SpinIdx ℚ × latticeO).2 := by
    rw [pvis_snd_mul, pvis_snd_mul, pvis_snd_mul, rhoPair_snd, slPair_snd, xiSignPair_snd,
      mul_one]
    exact gO3_comm_xi
  exact pvis_eq (Census.matrix_eq_of_Evec fun η c hc => spin_rows_of_theta hlat η c (xi_key hc))
    hlat

theorem slPair_mul_h1Lift
    (k : Fin 44)
    :
    slPair * h1Lift k = h1Lift k * rhoPair (pauliQ (gDiff k)) * slPair := by
  by_cases h1 : (k : ℕ) < 23
  · have e := h1Lift_pauli h1
    calc slPair * h1Lift k = slPair * rhoPair (pauliQ (pauliGen k)) := congrArg (slPair * ·) e
      _ = rhoPair (pauliQ (pauliGen k)) * rhoPair (pauliQ (gDiff k)) * slPair :=
          slPair_mul_pauli h1
      _ = h1Lift k * rhoPair (pauliQ (gDiff k)) * slPair :=
          congrArg (· * rhoPair (pauliQ (gDiff k)) * slPair) e.symm
  by_cases h2 : (k : ℕ) < 32
  · have e := h1Lift_perm (k := k) (by omega) h2
    have hn : 23 + ((⟨(k : ℕ) - 23, by omega⟩ : Fin 9) : ℕ) = k := by
      show 23 + ((k : ℕ) - 23) = k
      omega
    have e' := (slPair_mul_gPair ⟨(k : ℕ) - 23, by omega⟩).trans (congrArg (fun n =>
      gPair (fAut ⟨(k : ℕ) - 23, by omega⟩) * rhoPair (pauliQ (gDiff n)) * slPair) hn)
    calc slPair * h1Lift k = slPair * gPair (fAut ⟨(k : ℕ) - 23, by omega⟩) :=
          congrArg (slPair * ·) e
      _ = gPair (fAut ⟨(k : ℕ) - 23, by omega⟩) * rhoPair (pauliQ (gDiff k)) * slPair := e'
      _ = h1Lift k * rhoPair (pauliQ (gDiff k)) * slPair :=
          congrArg (· * rhoPair (pauliQ (gDiff k)) * slPair) e.symm
  by_cases h3 : (k : ℕ) < 43
  · have e := h1Lift_sign (k := k) (by omega) h3
    have hn : 32 + ((k : ℕ) - 32) = k := by omega
    have e' := (slPair_mul_signProd (j := (k : ℕ) - 32) (by omega)).trans (congrArg (fun n =>
      signProd (signCodesOf ((k : ℕ) - 32)) * rhoPair (pauliQ (gDiff n)) * slPair) hn)
    calc slPair * h1Lift k = slPair * signProd (signCodesOf ((k : ℕ) - 32)) :=
          congrArg (slPair * ·) e
      _ = signProd (signCodesOf ((k : ℕ) - 32)) * rhoPair (pauliQ (gDiff k)) * slPair := e'
      _ = h1Lift k * rhoPair (pauliQ (gDiff k)) * slPair :=
          congrArg (· * rhoPair (pauliQ (gDiff k)) * slPair) e.symm
  · have e := h1Lift_xi (k := k) (by omega)
    have hn : (43 : ℕ) = k := by omega
    have e' := slPair_mul_xi.trans (congrArg (fun n =>
      xiSignPair * rhoPair (pauliQ (gDiff n)) * slPair) hn)
    calc slPair * h1Lift k = slPair * xiSignPair := congrArg (slPair * ·) e
      _ = xiSignPair * rhoPair (pauliQ (gDiff k)) * slPair := e'
      _ = h1Lift k * rhoPair (pauliQ (gDiff k)) * slPair :=
          congrArg (· * rhoPair (pauliQ (gDiff k)) * slPair) e.symm

end CFSG.Monster.B.TwoA.Sp8
