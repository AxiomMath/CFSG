module

public import CFSG.Monster.B.Classical.PlaneData
public import CFSG.Monster.B.Cbar.Octads
public import CFSG.Monster.CodeAut.Perm
public import CFSG.LinearAlgebra.LinearGroups.FourElementFieldTransport
public import Mathlib.GroupTheory.SemidirectProduct
import all CFSG.Fischer.F4
public import Mathlib.LinearAlgebra.Projectivization.Action
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.Monster.B.Classical.ThreePlane

open CFSG.Fischer CFSG.Monster.B.Classical.Plane CFSG.LinearGroups
open scoped LinearAlgebra.Projectivization MatrixGroups Matrix Pointwise

@[expose] def P : Subgroup (Equiv.Perm (Fin 24)) :=
  CFSG.Monster.Code.AutPerm ⊓ MulAction.stabilizer (Equiv.Perm (Fin 24)) ({0, 1} : Set (Fin 24))

@[expose] def P₂ : Subgroup (Equiv.Perm (Fin 24)) :=
  P ⊓ MulAction.stabilizer (Equiv.Perm (Fin 24)) (2 : Fin 24)

theorem mem_P {p : Equiv.Perm (Fin 24)} :
    p ∈ P ↔ p ∈ CFSG.Monster.Code.AutPerm ∧ p '' {0, 1} = {0, 1} := by
  rw [P, Subgroup.mem_inf, MulAction.mem_stabilizer_iff, ← Set.image_smul]
  rfl

theorem mem_P₂ {p : Equiv.Perm (Fin 24)} : p ∈ P₂ ↔ p ∈ P ∧ p 2 = 2 := by
  rw [P₂, Subgroup.mem_inf, MulAction.mem_stabilizer_iff]
  rfl

abbrev PlanePoint : Type := ℙ F4 (Fin 3 → F4)

@[expose] def scalarSL : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F4) where
  carrier := {A | ∃ c : F4ˣ, (A : Matrix (Fin 3) (Fin 3) F4) = (c : F4) • 1}
  mul_mem' := by
    rintro A B ⟨c, hc⟩ ⟨d, hd⟩
    refine ⟨c * d, ?_⟩
    rw [Matrix.SpecialLinearGroup.coe_mul, hc, hd, smul_mul_smul_comm, Matrix.one_mul,
      Units.val_mul]
  one_mem' := ⟨1, by simp⟩
  inv_mem' := by
    rintro A ⟨c, hc⟩
    refine ⟨c⁻¹, ?_⟩
    rw [Matrix.SpecialLinearGroup.coe_inv, hc, Matrix.adjugate_smul, Matrix.adjugate_one,
      Fintype.card_fin]
    have h : ∀ a : F4, a ≠ 0 → a ^ (3 - 1) = a⁻¹ := by decide
    rw [h _ c.ne_zero, Units.val_inv_eq_inv_val]

theorem cube_eq_one : ∀ a : F4, a ≠ 0 → a ^ 3 = 1 := by decide

theorem scalarSL_eq_center :
    scalarSL = Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F4) := by
  ext A
  rw [Matrix.SpecialLinearGroup.mem_center_iff, Fintype.card_fin]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, cube_eq_one c c.ne_zero, ?_⟩
    rw [hc]
    ext i j
    simp [Matrix.scalar_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.diagonal_apply]
  · rintro ⟨r, hr, hA⟩
    have hr0 : r ≠ 0 := by rintro rfl; simp at hr
    refine ⟨Units.mk0 r hr0, ?_⟩
    rw [← hA]
    ext i j
    simp [Matrix.scalar_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.diagonal_apply]

theorem sq_add_F4 : ∀ a b : F4, (a + b) ^ 2 = a ^ 2 + b ^ 2 := by decide

theorem sq_mul_F4 : ∀ a b : F4, (a * b) ^ 2 = a ^ 2 * b ^ 2 := by decide

theorem eq_of_sq_eq_sq_F4 : ∀ a b : F4, a ^ 2 = b ^ 2 → a = b := by decide

theorem coe_frobeniusF4 : ⇑frobeniusF4 = fun x : F4 => x ^ 2 := funext frobeniusF4_apply

@[expose] noncomputable def frobSL :
    Matrix.SpecialLinearGroup (Fin 3) F4 →* Matrix.SpecialLinearGroup (Fin 3) F4 :=
  Matrix.SpecialLinearGroup.map frobeniusF4.toRingHom

theorem frobSL_apply (A : Matrix.SpecialLinearGroup (Fin 3) F4) (i j : Fin 3) :
    (frobSL A : Matrix (Fin 3) (Fin 3) F4) i j = (A : Matrix (Fin 3) (Fin 3) F4) i j ^ 2 := by
  change frobeniusF4 ((A : Matrix (Fin 3) (Fin 3) F4) i j) = _
  exact frobeniusF4_apply _

theorem frobSL_coe (A : Matrix.SpecialLinearGroup (Fin 3) F4) :
    (frobSL A : Matrix (Fin 3) (Fin 3) F4) =
      (A : Matrix (Fin 3) (Fin 3) F4).map fun a => a ^ 2 := by
  ext i j
  exact frobSL_apply A i j

theorem frobSL_frobSL (A : Matrix.SpecialLinearGroup (Fin 3) F4) : frobSL (frobSL A) = A := by
  ext i j
  rw [frobSL_apply, frobSL_apply, F4.sq_sq]

theorem frobSL_center :
    Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F4) ≤
      (Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F4)).comap frobSL := by
  intro A hA
  rw [Subgroup.mem_comap, Subgroup.mem_center_iff]
  intro B
  have h := Subgroup.mem_center_iff.1 hA (frobSL B)
  have := congrArg frobSL h
  rwa [map_mul, map_mul, frobSL_frobSL] at this

@[expose] noncomputable def frobPSL : MulAut PSL(3, F4) where
  toFun := QuotientGroup.map _ _ frobSL frobSL_center
  invFun := QuotientGroup.map _ _ frobSL frobSL_center
  left_inv x := by
    induction x using QuotientGroup.induction_on with
    | H A => simp [QuotientGroup.map_mk, frobSL_frobSL]
  right_inv x := by
    induction x using QuotientGroup.induction_on with
    | H A => simp [QuotientGroup.map_mk, frobSL_frobSL]
  map_mul' := map_mul _

theorem frobPSL_mk (A : Matrix.SpecialLinearGroup (Fin 3) F4) :
    frobPSL (A : PSL(3, F4)) = (frobSL A : PSL(3, F4)) := rfl

theorem frobPSL_mul_self : frobPSL * frobPSL = 1 := by
  ext x
  induction x using QuotientGroup.induction_on with
  | H A => simp [MulAut.mul_apply, frobPSL_mk, frobSL_frobSL]

@[expose] noncomputable def frobPow (ε : ZMod 2) : MulAut PSL(3, F4) :=
  if ε = 0 then 1 else frobPSL

theorem zmod2_cases : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide

theorem frobPow_zero : frobPow 0 = 1 := ite_eq_left rfl

theorem frobPow_one : frobPow 1 = frobPSL := ite_eq_right (by decide)

theorem frobPow_add (x y : ZMod 2) : frobPow (x + y) = frobPow x * frobPow y := by
  rcases zmod2_cases x with rfl | rfl <;> rcases zmod2_cases y with rfl | rfl
  · rw [add_zero, frobPow_zero, mul_one]
  · rw [zero_add, frobPow_zero, one_mul]
  · rw [add_zero, frobPow_zero, mul_one]
  · rw [show (1 : ZMod 2) + 1 = 0 from rfl, frobPow_zero, frobPow_one, frobPSL_mul_self]

@[expose] noncomputable def frobHom : Multiplicative (ZMod 2) →* MulAut PSL(3, F4) where
  toFun ε := frobPow (Multiplicative.toAdd ε)
  map_one' := frobPow_zero
  map_mul' _ _ := frobPow_add _ _

theorem frobHom_apply (ε : Multiplicative (ZMod 2)) :
    frobHom ε = frobPow (Multiplicative.toAdd ε) := rfl

abbrev SigmaL3 : Type := PSL(3, F4) ⋊[frobHom] Multiplicative (ZMod 2)

@[expose] def barPow (ε : ZMod 2) (v : Fin 3 → F4) : Fin 3 → F4 :=
  if ε = 0 then v else fun i => v i ^ 2

@[expose] noncomputable def frobLin : (Fin 3 → F4) →ₛₗ[frobeniusF4.toRingHom] (Fin 3 → F4) where
  toFun v i := v i ^ 2
  map_add' v w := funext fun i => sq_add_F4 (v i) (w i)
  map_smul' c v := funext fun i => by
    change (c * v i) ^ 2 = frobeniusF4 c * v i ^ 2
    rw [frobeniusF4_apply, sq_mul_F4]

theorem frobLin_apply (v : Fin 3 → F4) (i : Fin 3) : frobLin v i = v i ^ 2 := rfl

theorem frobLin_injective : Function.Injective frobLin := fun _ _ h =>
  funext fun i => eq_of_sq_eq_sq_F4 _ _ (congrFun h i)

theorem frobLin_ne_zero {v : Fin 3 → F4} (hv : v ≠ 0) : frobLin v ≠ 0 := fun h =>
  hv (frobLin_injective (h.trans (map_zero frobLin).symm))

theorem barPow_ne_zero (ε : ZMod 2) {v : Fin 3 → F4} (hv : v ≠ 0) : barPow ε v ≠ 0 := by
  by_cases hε : ε = 0
  · rwa [barPow, ite_eq_left hε]
  · rw [barPow, ite_eq_right hε]
    exact frobLin_ne_zero hv

theorem mk_eq_mk_of_eq {v w : Fin 3 → F4} (hv : v ≠ 0) (hw : w ≠ 0) (h : v = w) :
    Projectivization.mk F4 v hv = Projectivization.mk F4 w hw := by
  subst h
  rfl

@[expose] noncomputable def frobP : PlanePoint → PlanePoint :=
  Projectivization.map frobLin frobLin_injective

@[expose] noncomputable def barPowP (ε : ZMod 2) : PlanePoint → PlanePoint :=
  if ε = 0 then id else frobP

theorem frobP_mk (v : Fin 3 → F4) (hv : v ≠ 0) :
    frobP (Projectivization.mk F4 v hv) =
      Projectivization.mk F4 (frobLin v) (frobLin_ne_zero hv) := by
  rw [frobP, Projectivization.map_mk]

theorem barPowP_mk (ε : ZMod 2) (v : Fin 3 → F4) (hv : v ≠ 0) :
    barPowP ε (Projectivization.mk F4 v hv) =
      Projectivization.mk F4 (barPow ε v) (barPow_ne_zero ε hv) := by
  by_cases hε : ε = 0
  · have h1 : barPowP ε (Projectivization.mk F4 v hv) = Projectivization.mk F4 v hv := by
      rw [barPowP, ite_eq_left hε]
      rfl
    rw [h1]
    exact mk_eq_mk_of_eq _ _ (by rw [barPow, ite_eq_left hε])
  · have h1 : barPowP ε (Projectivization.mk F4 v hv) = frobP (Projectivization.mk F4 v hv) := by
      rw [barPowP, ite_eq_right hε]
    rw [h1, frobP_mk]
    exact mk_eq_mk_of_eq _ _ (by rw [barPow, ite_eq_right hε]; rfl)

theorem frobP_frobP (p : PlanePoint) : frobP (frobP p) = p := by
  induction p using Projectivization.ind with
  | h v hv =>
    rw [frobP_mk, frobP_mk]
    exact mk_eq_mk_of_eq _ _ (funext fun i => F4.sq_sq (v i))

theorem frobLin_mulVec (A : Matrix (Fin 3) (Fin 3) F4) (v : Fin 3 → F4) :
    frobLin (A *ᵥ v) = (A.map fun a => a ^ 2) *ᵥ frobLin v := by
  funext i
  have := RingHom.map_mulVec frobeniusF4.toRingHom A v i
  have h2 : (⇑frobeniusF4.toRingHom : F4 → F4) = fun x => x ^ 2 :=
    funext fun x => frobeniusF4_apply x
  rw [h2] at this
  exact this

theorem frobP_smul (g : PSL(3, F4)) (p : PlanePoint) : frobP (g • p) = frobPSL g • frobP p := by
  induction g using QuotientGroup.induction_on with
  | H A =>
    induction p using Projectivization.ind with
    | h v hv =>
      have hl : frobP ((A : PSL(3, F4)) • Projectivization.mk F4 v hv) =
          Projectivization.mk F4 (frobLin (A • v))
            (frobLin_ne_zero ((smul_ne_zero_iff_ne A).mpr hv)) := by
        rw [Matrix.ProjectiveSpecialLinearGroup.smul_proj_mk, Projectivization.smul_mk, frobP_mk]
      have hr : frobPSL (A : PSL(3, F4)) • frobP (Projectivization.mk F4 v hv) =
          Projectivization.mk F4 (frobSL A • frobLin v)
            ((smul_ne_zero_iff_ne (frobSL A)).mpr (frobLin_ne_zero hv)) := by
        rw [frobPSL_mk, Matrix.ProjectiveSpecialLinearGroup.smul_proj_mk, frobP_mk,
          Projectivization.smul_mk]
      rw [hl, hr]
      refine mk_eq_mk_of_eq _ _ ?_
      rw [Matrix.SpecialLinearGroup.smul_def, Matrix.SpecialLinearGroup.smul_def,
        Matrix.smul_eq_mulVec, Matrix.smul_eq_mulVec, frobLin_mulVec, frobSL_coe]

theorem barPowP_add (a b : ZMod 2) (p : PlanePoint) :
    barPowP (a + b) p = barPowP a (barPowP b p) := by
  rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl
  · simp [barPowP]
  · simp [barPowP]
  · simp [barPowP]
  · rw [show (1 : ZMod 2) + 1 = 0 from rfl]
    simp only [barPowP, ite_true, show ¬((1 : ZMod 2) = 0) by decide, ite_false, id]
    exact (frobP_frobP p).symm

theorem barPowP_smul (ε : ZMod 2) (g : PSL(3, F4)) (p : PlanePoint) :
    barPowP ε (g • p) = frobPow ε g • barPowP ε p := by
  by_cases hε : ε = 0
  · simp [barPowP, frobPow, hε]
  · simp only [barPowP, frobPow, hε, ite_false]
    exact frobP_smul g p

@[expose] noncomputable def sigmaAct (x : SigmaL3) (p : PlanePoint) : PlanePoint :=
  x.left • barPowP (Multiplicative.toAdd x.right) p

noncomputable instance : MulAction SigmaL3 PlanePoint where
  smul := sigmaAct
  one_smul p := by
    change sigmaAct 1 p = p
    simp [sigmaAct, barPowP]
  mul_smul x y p := by
    change sigmaAct (x * y) p = sigmaAct x (sigmaAct y p)
    simp only [sigmaAct, SemidirectProduct.mul_left, SemidirectProduct.mul_right, toAdd_mul,
      barPowP_add, barPowP_smul, mul_smul, frobHom_apply]

theorem smul_def (x : SigmaL3) (p : PlanePoint) : x • p = sigmaAct x p := rfl

@[expose] def pairVec (M : Matrix (Fin 3) (Fin 3) F4) (ε : ZMod 2) (v : Fin 3 → F4) :
    Fin 3 → F4 :=
  barPow ε v ᵥ* M

@[expose] def transposeSL (M : Matrix.SpecialLinearGroup (Fin 3) F4) :
    Matrix.SpecialLinearGroup (Fin 3) F4 :=
  ⟨(M : Matrix (Fin 3) (Fin 3) F4).transpose, by rw [Matrix.det_transpose]; exact M.2⟩

@[expose] noncomputable def pairElt (M : Matrix.SpecialLinearGroup (Fin 3) F4) (ε : ZMod 2) :
    SigmaL3 :=
  ⟨(transposeSL M : PSL(3, F4)), Multiplicative.ofAdd ε⟩

theorem pairVec_ne_zero (M : Matrix.SpecialLinearGroup (Fin 3) F4) (ε : ZMod 2)
    {v : Fin 3 → F4} (hv : v ≠ 0) : pairVec M ε v ≠ 0 := by
  intro h
  apply barPow_ne_zero ε hv
  have hM : (M : Matrix (Fin 3) (Fin 3) F4) *
      ((M⁻¹ : Matrix.SpecialLinearGroup (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  have := congrArg (· ᵥ* ((M⁻¹ : Matrix.SpecialLinearGroup (Fin 3) F4) :
    Matrix (Fin 3) (Fin 3) F4)) h
  simp only [pairVec, Matrix.vecMul_vecMul, hM, Matrix.vecMul_one, Matrix.zero_vecMul] at this
  exact this

theorem pairElt_smul_mk (M : Matrix.SpecialLinearGroup (Fin 3) F4) (ε : ZMod 2)
    (v : Fin 3 → F4) (hv : v ≠ 0) :
    pairElt M ε • Projectivization.mk F4 v hv =
      Projectivization.mk F4 (pairVec M ε v) (pairVec_ne_zero M ε hv) := by
  rw [smul_def, sigmaAct, pairElt]
  change (transposeSL M : PSL(3, F4)) • barPowP ε (Projectivization.mk F4 v hv) = _
  rw [barPowP_mk, Matrix.ProjectiveSpecialLinearGroup.smul_proj_mk, Projectivization.smul_mk]
  refine mk_eq_mk_of_eq _ _ ?_
  rw [Matrix.SpecialLinearGroup.smul_def, Matrix.smul_eq_mulVec, pairVec, transposeSL,
    Matrix.mulVec_transpose]

abbrev NativeCoord : Type := {i : Fin 24 // 3 ≤ (i : ℕ)}

@[expose] def jIdxTbl : Fin 21 → Fin 21 :=
  ![5, 1, 9, 13, 17, 0, 6, 7, 8, 20, 15, 10, 2, 11, 16, 3, 18, 14, 4, 12, 19]

@[expose] def jIdx (i : NativeCoord) : Fin 21 := jIdxTbl ⟨(i : ℕ) - 3, by omega⟩

@[expose] def jVec (i : NativeCoord) : Fin 3 → F4 := Ω (jIdx i)

@[expose] noncomputable def j (i : NativeCoord) : PlanePoint := Ωproj (jIdx i)

@[expose] def nativeGenFn : Fin 6 → Fin 24 → Fin 24 :=
  ![![0, 1, 2, 3, 4, 6, 7, 5, 18, 17, 19, 16, 10, 9, 11, 8, 14, 13, 15, 12, 22, 21, 23, 20],
    ![0, 1, 2, 3, 5, 6, 4, 7, 10, 8, 9, 11, 21, 23, 22, 20, 15, 13, 12, 14, 16, 18, 19, 17],
    ![0, 1, 2, 3, 5, 7, 6, 4, 10, 9, 11, 8, 16, 19, 17, 18, 21, 22, 20, 23, 15, 12, 14, 13],
    ![0, 1, 2, 3, 8, 9, 10, 11, 16, 18, 19, 17, 20, 23, 21, 22, 12, 13, 14, 15, 4, 5, 6, 7],
    ![0, 1, 2, 4, 3, 6, 5, 7, 8, 18, 21, 15, 12, 22, 17, 11, 20, 14, 9, 19, 16, 10, 13, 23],
    ![1, 0, 2, 3, 4, 5, 7, 6, 9, 8, 10, 11, 12, 13, 15, 14, 23, 22, 20, 21, 18, 19, 17, 16]]

@[expose] def nativeGenInvFn : Fin 6 → Fin 24 → Fin 24 :=
  ![![0, 1, 2, 3, 4, 7, 5, 6, 15, 13, 12, 14, 19, 17, 16, 18, 11, 9, 8, 10, 23, 21, 20, 22],
    ![0, 1, 2, 3, 6, 4, 5, 7, 9, 10, 8, 11, 18, 17, 19, 16, 20, 23, 21, 22, 15, 12, 14, 13],
    ![0, 1, 2, 3, 7, 4, 6, 5, 11, 9, 8, 10, 21, 23, 22, 20, 12, 14, 15, 13, 18, 16, 17, 19],
    ![0, 1, 2, 3, 20, 21, 22, 23, 4, 5, 6, 7, 16, 17, 18, 19, 8, 11, 9, 10, 12, 14, 15, 13],
    ![0, 1, 2, 4, 3, 6, 5, 7, 8, 18, 21, 15, 12, 22, 17, 11, 20, 14, 9, 19, 16, 10, 13, 23],
    ![1, 0, 2, 3, 4, 5, 7, 6, 9, 8, 10, 11, 12, 13, 15, 14, 23, 22, 20, 21, 18, 19, 17, 16]]

theorem nativeGen_left_inv : ∀ k x, nativeGenInvFn k (nativeGenFn k x) = x := by decide

theorem nativeGen_right_inv : ∀ k x, nativeGenFn k (nativeGenInvFn k x) = x := by decide

@[expose] def nativeGen (k : Fin 6) : Equiv.Perm (Fin 24) where
  toFun := nativeGenFn k
  invFun := nativeGenInvFn k
  left_inv := nativeGen_left_inv k
  right_inv := nativeGen_right_inv k

@[expose] def ω3 : F4 := ⟨3⟩

@[expose] def genMat : Fin 6 → Matrix (Fin 3) (Fin 3) F4 :=
  ![!![1, 0, 0; 0, F4.ω, 0; 0, F4.ω, ω3], !![1, 0, 0; ω3, ω3, 0; 1, 0, F4.ω],
    !![1, 0, 0; F4.ω, F4.ω, 0; F4.ω, 0, ω3], !![1, 0, 0; 0, 0, 1; 1, 1, F4.ω],
    !![0, ω3, 0; F4.ω, 0, 0; 0, 0, 1], !![ω3, 0, 0; 0, ω3, 0; ω3, 0, ω3]]

@[expose] def genFrob : Fin 6 → ZMod 2 := ![0, 0, 0, 0, 0, 1]

@[expose] noncomputable def nativeLines : Finset (Finset (Fin 24)) :=
  (CFSG.Monster.Code.octads.filter fun d => ({0, 1, 2} : Finset (Fin 24)) ⊆ d).image
    fun d => d \ {0, 1, 2}

end CFSG.Monster.B.Classical.ThreePlane
