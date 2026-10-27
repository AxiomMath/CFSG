
module

public import CFSG.Monster.B.TwoA.Sp8.ElemAbBase
public import CFSG.Monster.B.TwoA.Sp8.GenActionData
public import CFSG.Monster.B.Gen.HRecords
public meta import CFSG.Monster.B.Rep4371.Model
public meta import CFSG.Monster.B.TwoA.Sp8.GenActionData
public meta import CFSG.Monster.B.TwoA.Co2Inv.Data
public meta import CFSG.Monster.B.TwoA.Sp8.LiftsBase
public import CFSG.Monster.B.TwoA.Sp8.GenActionLiftsInputs
public import Certificates.Data.CFSGNative.MonsterB.Short
public import Certificates.Data.CFSGNative.Mathieu.M24
public import CFSG.Certificates.Kernel.AxisPlane.Orbit
public import Certificates.Data.Kernel.VisFrame.Gens
public import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public import Certificates.Data.CFSGNative.MonsterB.Co2Matrix
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
  CFSG.Monster.Lifts CFSG.Monster.VisQuot CFSG.Monster.ScalarKernel CFSG.Monster.B.Co2

@[expose] def signProd (as : List ℕ) : Pvis := (as.map signPair).prod

theorem pauliQ_D (d : ℕ) : pauliQ (false, 0, d) = DQ (toD d) := by
  rw [pauliQ, DQ_eq]
  congr 1
  exact SpinCoord.ext rfl toC_zero rfl

theorem dualN_one : Model.dualN 1 = 62 := by decide

theorem e0Cls_eq : e0Cls = toD 62 := by
  rw [e0Cls, ← dualN_one, ← mk_bvec_eq_toD]
  congr 1
  exact (bvec_two_pow 0).symm

theorem conjQ_signProd (as : List ℕ) (y : Model.Pauli) :
    conjQ (signProd as) (pauliQ y) = pauliQ (as.foldl (fun x a => Model.conjYN a x) y) := by
  induction as generalizing y with
  | nil =>
    rw [signProd, List.map_nil, List.prod_nil, List.foldl_nil]
    exact conjQ_one _
  | cons a as ih =>
    have e : signProd (a :: as) = signPair a * signProd as := by
      rw [signProd, signProd, List.map_cons, List.prod_cons]
    have h1 : conjQ (signPair a) (pauliQ y) = pauliQ (Model.conjYN a y) := conjQ_sign_toQ a y
    have h2 : pauliQ ((a :: as).foldl (fun x a => Model.conjYN a x) y) =
        pauliQ (as.foldl (fun x a => Model.conjYN a x) (Model.conjYN a y)) :=
      congrArg pauliQ List.foldl_cons
    refine (congrArg (fun P => conjQ P (pauliQ y)) e).trans ?_
    refine (conjQ_mul _ _ _).trans ?_
    exact ((congrArg (conjQ (signProd as)) h1).trans (ih _)).trans h2.symm

theorem h1ConjN_pauli {k : ℕ} (h : k < 23) (y : Model.Pauli) :
    h1ConjN k y = Model.conjPauliN (pauliGen k) y := by
  rw [h1ConjN, ite_eq_left h]

theorem h1ConjN_perm {k : ℕ} (h1 : 23 ≤ k) (h2 : k < 32) (y : Model.Pauli) :
    h1ConjN k y =
      Model.conjPauliN (false, 0, epsDual (k - 23)) (Model.conjPermN fPerms[k - 23]! y) := by
  rw [h1ConjN, ite_eq_right (by omega), ite_eq_left h2]

theorem h1ConjN_sign {k : ℕ} (h1 : 32 ≤ k) (h2 : k < 43) (y : Model.Pauli) :
    h1ConjN k y = (signCodesOf (k - 32)).foldl (fun x a => Model.conjYN a x) y := by
  rw [h1ConjN, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left h2]

theorem h1ConjN_xi {k : ℕ} (h : 43 ≤ k) (y : Model.Pauli) :
    h1ConjN k y = Model.conjYN 1 (Model.conjXiN y) := by
  rw [h1ConjN, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]

theorem conjQ_congr {P P' : Pvis} (h : P = P') (r : Q) : conjQ P r = conjQ P' r :=
  congrArg (fun X => conjQ X r) h

theorem coe_jhatToKv0_pair {p : Pvis} (hJ : thetaEquiv p ∈ Jstar)
    (hD : iotaD (kappa ⟨thetaEquiv p, Jstar_le_Cgen hJ⟩) ∈ Jhat) :
    ((jhatToKv0 ⟨_, hD⟩ : Kstab v0) : OLq) = (QuotientGroup.mk p.1.2)⁻¹ := by
  have he : (⟨iotaD (kappa ⟨thetaEquiv p, Jstar_le_Cgen hJ⟩), hD⟩ : Jhat) =
      jhatEquiv ⟨kappa ⟨thetaEquiv p, Jstar_le_Cgen hJ⟩, kappa_mem_Jbar hJ⟩ :=
    Subtype.ext rfl
  rw [he, jhatToKv0_jhatEquiv, coe_jbarToKv_kappa hJ rfl]

theorem signProd_snd (as : List ℕ) :
    ((signProd as : Pvis) : GL SpinIdx ℚ × latticeO).2 =
      gO (toC (as.foldl (fun x a => x ^^^ a) 0)) := by
  suffices h : ∀ b : ℕ, gO (toC b) * ((signProd as : Pvis) : GL SpinIdx ℚ × latticeO).2 =
      gO (toC (as.foldl (fun x a => x ^^^ a) b)) by
    have := h 0
    rwa [toC_zero, gO_zero, one_mul] at this
  induction as with
  | nil =>
    intro b
    rw [signProd, List.map_nil, List.prod_nil, List.foldl_nil]
    exact mul_one _
  | cons a as ih =>
    intro b
    rw [signProd, List.map_cons, List.prod_cons, Subgroup.coe_mul, Prod.snd_mul, List.foldl_cons,
      ← ih (b ^^^ a), toC_xor, gO_add, mul_assoc]
    rfl

theorem signCodesOf_xor : ∀ j < 11, (signCodesOf j).foldl (fun x a => x ^^^ a) 0 =
    [3, 5, 9, 17, 33, 64, 129, 256, 512, 1024, 2048][j]! := by
  decide

theorem mk_signProd (j : ℕ) (hj : j < 11) :
    (QuotientGroup.mk ((signProd (signCodesOf j) : Pvis) : GL SpinIdx ℚ × latticeO).2 : OLq) =
      Co2.alpha ⟨12 + j, by omega⟩ := by
  have h := mk_hPair_snd ⟨12 + j, by omega⟩
  rw [hPair_of_codeSign (by simp) (by simp; omega), recCode_eq (by simp) (by simp; omega)] at h
  rw [signProd_snd, signCodesOf_xor j hj]
  refine Eq.trans ?_ h
  congr 3
  simp

theorem pauliGen_comm : ∀ k < 23, Model.Pauli.mul (pauliGen k) (false, 0, 191) =
    Model.Pauli.mul (false, 0, 191) (pauliGen k) := by
  decide

theorem pauliQ_pauliGen_mem (k : ℕ) (hk : k < 23) :
    pauliQ (pauliGen k) ∈ Subgroup.centralizer {rStar} := by
  rw [Subgroup.mem_centralizer_singleton_iff, B.rStar_eq, ← pauliQ_mul, ← pauliQ_mul,
    pauliGen_comm k hk]

end CFSG.Monster.B.TwoA.Sp8
