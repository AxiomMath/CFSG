
module

public import CFSG.Monster.B.TwoA.Sp8.GenActionLiftsBase
public import Certificates.Data.CFSGNative.MonsterB.Sp8Check
public meta import Certificates.Data.CFSGNative.MonsterB.Sp8Check
public meta import CFSG.Monster.B.Rep4371.GlueDefs
public meta import CFSG.Monster.B.TwoA.Sp8.GenActionLiftsBase
public import CFSG.Monster.B.TwoA.Sp8.GenActionDiffInputs
public import CFSG.Monster.B.TwoA.Sp8.A8Inputs
public import CFSG.Monster.B.TwoA.Base.WCls
public import CFSG.Monster.B.TwoA.Census.PermBFS
public import CFSG.Monster.B.TwoA.Co2Inv.Data
public import CFSG.Monster.B.TwoA.Co2Inv.RowsInputs

@[expose] public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Sp8

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short
  CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Co2Inv CFSG.Monster.B.Rep4371
  CFSG.Monster.Lifts CFSG.Monster.VisQuot CFSG.Monster.ScalarKernel CFSG.Monster.Xi Matrix

theorem pvis_eq {P R : Pvis}
    (hs : (((P : GL SpinIdx ℚ × latticeO).1 : GL SpinIdx ℚ) : Matrix SpinIdx SpinIdx ℚ) =
      (((R : GL SpinIdx ℚ × latticeO).1 : GL SpinIdx ℚ) : Matrix SpinIdx SpinIdx ℚ))
    (hl : (P : GL SpinIdx ℚ × latticeO).2 = (R : GL SpinIdx ℚ × latticeO).2) : P = R :=
  Subtype.ext (Prod.ext (Units.ext hs) hl)

theorem pvis_fst_mul (P R : Pvis) :
    (((P * R : Pvis) : GL SpinIdx ℚ × latticeO).1 : Matrix SpinIdx SpinIdx ℚ) =
      (((P : GL SpinIdx ℚ × latticeO).1 : GL SpinIdx ℚ) : Matrix SpinIdx SpinIdx ℚ) *
        (((R : GL SpinIdx ℚ × latticeO).1 : GL SpinIdx ℚ) : Matrix SpinIdx SpinIdx ℚ) := rfl

theorem pvis_snd_mul (P R : Pvis) :
    ((P * R : Pvis) : GL SpinIdx ℚ × latticeO).2 =
      (P : GL SpinIdx ℚ × latticeO).2 * (R : GL SpinIdx ℚ × latticeO).2 := rfl

theorem rhoPair_fst (r : Q) :
    (((rhoPair r : Pvis) : GL SpinIdx ℚ × latticeO).1 : Matrix SpinIdx SpinIdx ℚ) =
      ((r : GL SpinIdx ℚ) : Matrix SpinIdx SpinIdx ℚ) := rfl

theorem rhoPair_snd (r : Q) : ((rhoPair r : Pvis) : GL SpinIdx ℚ × latticeO).2 = 1 := rfl

theorem slPair_eq_signPair : slPair = signPair 3 := slPair_eq

theorem slPair_fst : (((slPair : Pvis) : GL SpinIdx ℚ × latticeO).1 : Matrix SpinIdx SpinIdx ℚ) =
    Ymat ⟨toC 3, 0⟩ := by
  rw [slPair_eq]
  rfl

theorem slPair_snd : ((slPair : Pvis) : GL SpinIdx ℚ × latticeO).2 = gO (toC 3) := by
  rw [slPair_eq]

theorem mul_eq_of_inv_mul_mul {G : Type*} [Group G] {s x y : G} (hs : s * s = 1)
    (h : s⁻¹ * x * s = y) : s * x = y * s := by
  have hinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  rw [hinv] at h
  calc s * x = s * x * s * s := by rw [mul_assoc (s * x) s s, hs, mul_one]
    _ = y * s := by rw [h]

def RowOK (f : Bool → ℕ → Bool × Bool × ℕ) (M : Matrix SpinIdx SpinIdx ℚ) : Prop :=
  ∀ η c, Evec η c ᵥ* M = sgn (boolZ (f η c).1) • Evec (f η c).2.1 (f η c).2.2

theorem Evec_vecMul_prod : ∀ {fs : List (Bool → ℕ → Bool × Bool × ℕ)}
    {ms : List (Matrix SpinIdx SpinIdx ℚ)}, List.Forall₂ RowOK fs ms → ∀ η c,
      Evec η c ᵥ* ms.prod = sgn (boolZ (Native.Sp8.rowChain fs η c).1) •
        Evec (Native.Sp8.rowChain fs η c).2.1 (Native.Sp8.rowChain fs η c).2.2
  | _, _, .nil, η, c => by
    rw [List.prod_nil, vecMul_one, Native.Sp8.rowChain, boolZ_false,
      show sgn (0 : ZMod 2) = 1 from rfl, one_smul]
  | f :: fs, M :: ms, .cons hM h, η, c => by
    rw [List.prod_cons, ← vecMul_vecMul, hM, smul_vecMul, Evec_vecMul_prod h, smul_smul,
      ← Census.sgn_boolZ_xor]
    rfl

theorem rowOK_Ymat (a : ℕ) : RowOK (Model.eYN a) (Ymat ⟨toC a, 0⟩) := Evec_vecMul_Ymat a

theorem rowOK_qmatR (q : Model.Pauli) :
    RowOK (Model.ePauliN q) (qmatR ℚ (boolZ q.s) (toC q.a) (toD q.d)) := Evec_vecMul_qmatR q

theorem rowOK_smat (p : AutPerm) {arr : Array ℕ} (hp : RepPerm p arr) :
    RowOK (Model.ePermN arr) (smat p) := Evec_vecMul_smat p hp

theorem rowChainEq_spec {fs gs : List (Bool → ℕ → Bool × Bool × ℕ)}
    (h : Native.Sp8.rowChainEq fs gs = true) {η : Bool} {c : ℕ} (hc : c < 4096) :
    Native.Sp8.rowChain fs η c = Native.Sp8.rowChain gs η c := by
  simp only [Native.Sp8.rowChainEq, List.all_eq_true, List.mem_range, List.mem_cons,
    List.not_mem_nil, or_false, beq_iff_eq] at h
  exact h c hc η (by cases η <;> simp)

theorem slPair_mul_eq_of_rows {h : Pvis} {fs : List (Bool → ℕ → Bool × Bool × ℕ)}
    {ms : List (Matrix SpinIdx SpinIdx ℚ)}
    (hms : (((h : GL SpinIdx ℚ × latticeO).1 : GL SpinIdx ℚ) : Matrix SpinIdx SpinIdx ℚ) =
      ms.prod) (hf : List.Forall₂ RowOK fs ms) (q : Model.Pauli)
    (hrows : Native.Sp8.rowChainEq (Model.eYN 3 :: fs) (fs ++ [Model.ePauliN q, Model.eYN 3]) =
      true)
    (hlat : gO (toC 3) * (h : GL SpinIdx ℚ × latticeO).2 =
      (h : GL SpinIdx ℚ × latticeO).2 * gO (toC 3)) :
    slPair * h = h * rhoPair (pauliQ q) * slPair := by
  refine pvis_eq ?_ ?_
  · have hL : (((slPair * h : Pvis) : GL SpinIdx ℚ × latticeO).1 : Matrix SpinIdx SpinIdx ℚ) =
        (Ymat ⟨toC 3, 0⟩ :: ms).prod := by
      rw [pvis_fst_mul, slPair_fst, hms, List.prod_cons]
    have hR : (((h * rhoPair (pauliQ q) * slPair : Pvis) : GL SpinIdx ℚ × latticeO).1 :
        Matrix SpinIdx SpinIdx ℚ) =
          (ms ++ [qmatR ℚ (boolZ q.s) (toC q.a) (toD q.d), Ymat ⟨toC 3, 0⟩]).prod := by
      rw [pvis_fst_mul, pvis_fst_mul, rhoPair_fst, slPair_fst, hms, qmatR_toSC_eq,
        List.prod_append, List.prod_cons, List.prod_cons, List.prod_nil, mul_one, mul_assoc]
    rw [hL, hR]
    refine Census.matrix_eq_of_Evec fun η c hc => ?_
    rw [Evec_vecMul_prod (.cons (rowOK_Ymat 3) hf),
      Evec_vecMul_prod (List.rel_append hf (.cons (rowOK_qmatR q) (.cons (rowOK_Ymat 3) .nil))),
      rowChainEq_spec hrows hc]
  · rw [pvis_snd_mul, pvis_snd_mul, pvis_snd_mul, rhoPair_snd, slPair_snd, mul_one, hlat]

theorem permCN_three : ∀ j < 9, Model.permCN fPerms[j]! 3 = 3 := by decide

def epsQ (j : ℕ) : Model.Pauli := (false, 0, epsDual j)

theorem signProd_fst (as : List ℕ) :
    (((signProd as : Pvis) : GL SpinIdx ℚ × latticeO).1 : Matrix SpinIdx SpinIdx ℚ) =
      (as.map fun a => Ymat ⟨toC a, 0⟩).prod := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    rw [List.map_cons, List.prod_cons, ← ih]
    rfl

theorem forall₂_signFs (j : ℕ) :
    List.Forall₂ RowOK (signFs Model.eYN j) ((signCodesOf j).map fun a => Ymat ⟨toC a, 0⟩) := by
  rw [signFs]
  induction signCodesOf j with
  | nil => exact .nil
  | cons a as ih => exact .cons (rowOK_Ymat a) ih

theorem col_word3 : ∀ i j : Fin 24, Code.col i = Code.col j →
    (Model.wordN 3).testBit i = (Model.wordN 3).testBit j := by
  decide

theorem gmat3_mul_gXi : gmat (toC 3) * gXi = gXi * gmat (toC 3) := by
  ext i j
  rw [gmat, diagonal_mul, mul_diagonal, gXi_apply]
  split_ifs with h
  · rw [coe_toC_apply, coe_toC_apply, col_word3 i j h, mul_comm]
  · simp

theorem xiSignPair_snd :
    ((xiSignPair : Pvis) : GL SpinIdx ℚ × latticeO).2 = xiO * gO (toC 1) := rfl

theorem gO3_comm_xi : gO (toC 3) * (xiO * gO (toC 1)) = (xiO * gO (toC 1)) * gO (toC 3) := by
  apply mat_injective
  rw [mat_mul, mat_mul, mat_mul, mat_mul, mat_gO, mat_gO]
  change gmat (toC 3) * (gXi * gmat (toC 1)) = gXi * gmat (toC 1) * gmat (toC 3)
  rw [← mul_assoc, gmat3_mul_gXi, mul_assoc, mul_assoc, ← mat_gO, ← mat_gO, ← mat_mul, ← mat_mul,
    gO_comm]

theorem keyValid_of_ne {κ : Model.Key} (h : (κ.1 != 0) = true) : KeyValid κ := by
  intro h0
  rw [h0] at h
  exact absurd h (by decide)

theorem keyVec_eq_interp (κ : Model.Key) : keyVec κ = interp 1 [(κ, 1)] := by
  rw [interp_cons, interp_nil, add_zero]
  norm_num

theorem theta_slPair_key (κ : Model.Key) (hκ : KeyValid κ) :
    theta slPair (keyVec κ) = interp 64 (Model.keyActSign 3 κ) := by
  rw [← thetaEquiv_apply, slPair_eq_signPair]
  exact keyAct_sign_sound 3 (by decide) κ hκ

theorem theta_xi_key (κ : Model.Key) (hκ : KeyValid κ) :
    theta xiSignPair (keyVec κ) = interp 64 (Model.keyActXi κ) := by
  rw [← thetaEquiv_apply]
  exact keyAct_xi_sound κ hκ

theorem theta_rhoPair_key (q : Model.Pauli) (κ : Model.Key) :
    theta (rhoPair (pauliQ q)) (keyVec κ) = interp 64 (Model.keyActPauli q κ) :=
  keyAct_pauli_sound q κ

theorem tensor_cancel {X Y : SpinIdx → ℚ} {u : Fin 24 → ℚ} (hu : u ≠ 0)
    (h : tensor X u = tensor Y u) : X = Y := by
  obtain ⟨j, hj⟩ : ∃ j, u j ≠ 0 := by
    by_contra hc
    exact hu (funext fun j => not_not.1 fun h => hc ⟨j, h⟩)
  funext i
  have := congrFun (congrFun h i) j
  simp only [tensor, vecMulVec_apply] at this
  exact mul_right_cancel₀ hj this

theorem wvec_vecMul_ne_zero (L : latticeO) : wvec ᵥ* mat L ≠ 0 := by
  intro h
  have h1 : wvec ᵥ* (mat L * mat L⁻¹) = wvec := by
    rw [← mat_mul, mul_inv_cancel, mat_one, vecMul_one]
  rw [← vecMul_vecMul, h, zero_vecMul] at h1
  have := congrFun h1 0
  simp [wvec] at this

theorem spin_rows_of_theta {P R : Pvis}
    (hlat : (P : GL SpinIdx ℚ × latticeO).2 = (R : GL SpinIdx ℚ × latticeO).2) (η : Bool) (c : ℕ)
    (h : theta P (keyVec (Model.Key.W η c)) = theta R (keyVec (Model.Key.W η c))) :
    Evec η c ᵥ* (((P : GL SpinIdx ℚ × latticeO).1 : GL SpinIdx ℚ) : Matrix SpinIdx SpinIdx ℚ) =
      Evec η c ᵥ* (((R : GL SpinIdx ℚ × latticeO).1 : GL SpinIdx ℚ) :
        Matrix SpinIdx SpinIdx ℚ) := by
  have hW : Model.Key.W η c = (0 + 2, if η then 1 else 0, c) := by cases η <;> rfl
  have hη : ((if η then 1 else 0 : ℕ) != 0) = η := by cases η <;> rfl
  rw [hW, theta_keyVec_W, theta_keyVec_W, hη, hlat] at h
  exact tensor_cancel (wvec_vecMul_ne_zero _) (congrArg (fun x : SpaceB => x.2.2) h)

end CFSG.Monster.B.TwoA.Sp8
