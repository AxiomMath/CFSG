module

public import CFSG.LocalAnalysis.StandardType.FF81.CentAModelDefs
import CFSG.LinearAlgebra.SqrtDiag
import CFSG.LocalAnalysis.ComponentInitial.FourGroupEvenCanonical

public section

namespace CFSG.StandardType.FF81.CentA

open Matrix RootFusionLin
open CFSG.LocalAnalysis.ComponentInitial.FourGroupEvenCanonical
open CFSG.LinearAlgebra

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem caSymp_zmod2_eq_zero_or_one (x : ZMod 2) : x = 0 ∨ x = 1 := by
  revert x
  decide

private theorem caSymp_zmod2_sq (x : ZMod 2) : x ^ 2 = x := by
  revert x
  decide

private theorem caSymp_antiDiag_mul_self (m : ℕ) :
    (antiDiag m : GL (BlkIdx 1 m) (ZMod 2)) * antiDiag m = 1 := by
  have h := mul_inv_cancel (antiDiag m : GL (BlkIdx 1 m) (ZMod 2))
  rwa [antiDiag_inv] at h

private theorem caSymp_antiDiag_mul_self_mat (m : ℕ) :
    ((antiDiag m : GL (BlkIdx 1 m) (ZMod 2)) :
        Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) *
      ((antiDiag m : GL (BlkIdx 1 m) (ZMod 2)) :
        Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) = 1 := by
  simpa using congrArg (fun x : GL (BlkIdx 1 m) (ZMod 2) =>
    (x : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2))) (caSymp_antiDiag_mul_self m)

private theorem caSymp_antiDiag_transpose (m : ℕ) :
    ((antiDiag m : GL (BlkIdx 1 m) (ZMod 2)) :
        Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2))ᵀ =
      ((antiDiag m : GL (BlkIdx 1 m) (ZMod 2)) :
        Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) := by
  have hinv : (antiDiagPerm m)⁻¹ = antiDiagPerm m := antiDiagPerm_inv m
  rw [antiDiag, TauCeti.permutationGL_coe, Matrix.transpose_permMatrix, inv_inv, hinv]

private theorem caSymp_antiDiag_apply_self (m : ℕ) (i : BlkIdx 1 m) :
    ((antiDiag m : GL (BlkIdx 1 m) (ZMod 2)) :
        Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) i i =
      if antiDiagPerm m i = i then 1 else 0 := by
  have hinv : (antiDiagPerm m)⁻¹ = antiDiagPerm m := antiDiagPerm_inv m
  rw [antiDiag, TauCeti.permutationGL_coe, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply,
    Equiv.toPEquiv_apply, hinv]
  simp

private theorem caSymp_sqrtDiag_apply (S : Matrix ι ι (ZMod 2)) (i : ι) :
    sqrtDiag S i = S i i := by
  have h := sqrtDiag_apply_sq S i
  rwa [caSymp_zmod2_sq] at h

private theorem caSymp_matrix_iso_iff (A M : Matrix ι ι (ZMod 2)) (hA2 : A * A = 1)
    (hM : IsUnit M.det) :
    Mᵀ * A * M = A ↔ (Mᵀ)⁻¹ = A * M * A := by
  have hMT : IsUnit (Mᵀ).det := by rwa [Matrix.det_transpose]
  constructor
  · intro h
    have h1 : A * M = (Mᵀ)⁻¹ * A := by
      have h1a : (Mᵀ)⁻¹ * (Mᵀ * A * M) = (Mᵀ)⁻¹ * A := by rw [h]
      simp only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hMT, Matrix.one_mul] at h1a
      exact h1a
    have h2 : M = A * (Mᵀ)⁻¹ * A := by
      have h2a : A * (A * M) = A * ((Mᵀ)⁻¹ * A) := by rw [h1]
      simp only [← Matrix.mul_assoc, hA2, Matrix.one_mul] at h2a
      exact h2a
    calc (Mᵀ)⁻¹ = (A * A) * (Mᵀ)⁻¹ * (A * A) := by rw [hA2, one_mul, mul_one]
      _ = A * (A * (Mᵀ)⁻¹ * A) * A := by noncomm_ring
      _ = A * M * A := by rw [← h2]
  · intro h
    have hmul : Mᵀ * (Mᵀ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hMT
    have h1 : Mᵀ * A * M * A = 1 := by
      rw [← hmul, h]
      noncomm_ring
    calc Mᵀ * A * M = (Mᵀ * A * M * A) * A := by
          rw [show (Mᵀ * A * M * A) * A = (Mᵀ * A * M) * (A * A) from by noncomm_ring,
            hA2, mul_one]
      _ = 1 * A := by rw [h1]
      _ = A := one_mul A

private theorem caSymp_sigmaStd_eq_iff (m : ℕ) (g : GL (BlkIdx 1 m) (ZMod 2)) :
    sigmaStd m g = g ↔
      (g : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2))ᵀ *
        ((antiDiag m : GL (BlkIdx 1 m) (ZMod 2)) :
          Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) *
        (g : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) =
        ((antiDiag m : GL (BlkIdx 1 m) (ZMod 2)) :
          Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) := by
  have ha : (antiDiag m : GL (BlkIdx 1 m) (ZMod 2))⁻¹ = antiDiag m := antiDiag_inv m
  have hA2m : ((antiDiag m : GL (BlkIdx 1 m) (ZMod 2)) :
        Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) *
      ((antiDiag m : GL (BlkIdx 1 m) (ZMod 2)) :
        Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) = 1 :=
    caSymp_antiDiag_mul_self_mat m
  have hkey : sigmaStd m g = g ↔ Matrix.GeneralLinearGroup.inverseTranspose g =
      (antiDiag m)⁻¹ * g * (antiDiag m) := by
    rw [sigmaStd, MulAut.mul_apply, MulAut.conj_apply]
    constructor
    · intro h
      calc Matrix.GeneralLinearGroup.inverseTranspose g
          = (antiDiag m)⁻¹ * ((antiDiag m) * Matrix.GeneralLinearGroup.inverseTranspose g *
              (antiDiag m)⁻¹) * (antiDiag m) := by group
        _ = (antiDiag m)⁻¹ * g * (antiDiag m) := by rw [h]
    · intro h
      calc (antiDiag m) * Matrix.GeneralLinearGroup.inverseTranspose g * (antiDiag m)⁻¹
          = (antiDiag m) * ((antiDiag m)⁻¹ * g * (antiDiag m)) * (antiDiag m)⁻¹ := by rw [h]
        _ = g := by group
  rw [hkey, ha]
  have hMdet : IsUnit ((g : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)).det) :=
    Matrix.isUnits_det_units g
  constructor
  · intro h
    have hm : ((g : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2))ᵀ)⁻¹ =
        ((antiDiag m : GL (BlkIdx 1 m) (ZMod 2)) :
          Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) *
        (g : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) *
        ((antiDiag m : GL (BlkIdx 1 m) (ZMod 2)) :
          Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) := by
      have hval := congrArg (fun x : GL (BlkIdx 1 m) (ZMod 2) =>
        (x : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2))) h
      rw [Units.val_mul, Units.val_mul, Matrix.GeneralLinearGroup.coe_inverseTranspose,
        Matrix.GeneralLinearGroup.coe_inv, Matrix.transpose_nonsing_inv] at hval
      simpa only [Matrix.mul_assoc] using hval
    exact (caSymp_matrix_iso_iff _ _ hA2m hMdet).mpr hm
  · intro h
    have hm : ((g : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2))ᵀ)⁻¹ =
        ((antiDiag m : GL (BlkIdx 1 m) (ZMod 2)) :
          Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) *
        (g : Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) *
        ((antiDiag m : GL (BlkIdx 1 m) (ZMod 2)) :
          Matrix (BlkIdx 1 m) (BlkIdx 1 m) (ZMod 2)) :=
      (caSymp_matrix_iso_iff _ _ hA2m hMdet).mp h
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.coe_inverseTranspose, Matrix.GeneralLinearGroup.coe_inv,
      Matrix.transpose_nonsing_inv, Units.val_mul, Units.val_mul]
    simpa only [Matrix.mul_assoc] using hm

private theorem caSymp_vecMul_eq (M : Matrix ι ι (ZMod 2)) (x : ι → ZMod 2) :
    x ᵥ* M = Mᵀ *ᵥ x := by
  simpa using Matrix.vecMul_transpose (A := Mᵀ) (x := x)

private theorem caSymp_mulVec_dotProduct (M : Matrix ι ι (ZMod 2)) (x z : ι → ZMod 2) :
    (M *ᵥ x) ⬝ᵥ z = x ⬝ᵥ (Mᵀ *ᵥ z) := by
  rw [dotProduct_comm, Matrix.dotProduct_mulVec, caSymp_vecMul_eq, dotProduct_comm]

private theorem caSymp_beta_apply (M A : Matrix ι ι (ZMod 2)) (x y : ι → ZMod 2)
    (h : Mᵀ * A * M = A) :
    (M *ᵥ x) ⬝ᵥ (A *ᵥ (M *ᵥ y)) = x ⬝ᵥ (A *ᵥ y) := by
  rw [caSymp_mulVec_dotProduct, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h]

private theorem caSymp_nondegenerate (A : Matrix ι ι (ZMod 2)) (hAt : Aᵀ = A) (hA2 : A * A = 1)
    {w : ι → ZMod 2} (h : ∀ u, w ⬝ᵥ (A *ᵥ u) = 0) : w = 0 := by
  have h1 : w ᵥ* A = 0 := by
    funext i
    have hu := h (Pi.single i 1)
    rw [Matrix.dotProduct_mulVec] at hu
    rwa [dotProduct_single_one] at hu
  have h3 : (w ᵥ* A) ᵥ* A = 0 := by rw [h1, Matrix.zero_vecMul]
  rw [Matrix.vecMul_vecMul, hA2, Matrix.vecMul_one] at h3
  exact h3

private theorem caSymp_transv_zero (A : Matrix ι ι (ZMod 2)) (hA2 : A * A = 1)
    {v : ι → ZMod 2} (hv : v ⬝ᵥ (A *ᵥ v) = 0) :
    nilMatrix A 1 (A *ᵥ v) * nilMatrix A 1 (A *ᵥ v) = 0 :=
  nilMatrix_mul_nilMatrix_eq_zero A 1 1 (by
    rw [Matrix.mulVec_mulVec, hA2, Matrix.one_mulVec, dotProduct_comm]
    exact hv)

private theorem caSymp_transv_apply (A : Matrix ι ι (ZMod 2)) (hA2 : A * A = 1)
    {v : ι → ZMod 2} (hv : v ⬝ᵥ (A *ᵥ v) = 0) (x : ι → ZMod 2) :
    ((unipotentGL (nilMatrix A 1 (A *ᵥ v)) (caSymp_transv_zero A hA2 hv) :
      GL ι (ZMod 2)) : Matrix ι ι (ZMod 2)) *ᵥ x =
      x + ((A *ᵥ v) ⬝ᵥ x) • v := by
  rw [coe_unipotentGL, nilMatrix, one_smul, Matrix.add_mulVec, Matrix.one_mulVec,
    Matrix.vecMulVec_mulVec, Matrix.mulVec_mulVec, hA2, Matrix.one_mulVec, op_smul_eq_smul]

private theorem caSymp_transv_mem (A : Matrix ι ι (ZMod 2)) (hAt : Aᵀ = A) (hA2 : A * A = 1)
    {v : ι → ZMod 2} (hv : v ⬝ᵥ (A *ᵥ v) = 0) :
    (unipotentGL (nilMatrix A 1 (A *ᵥ v)) (caSymp_transv_zero A hA2 hv) :
      GL ι (ZMod 2)) ∈ matrixIsometryGroup A := by
  have hmem := unipotentGL_mem (C := A) hAt hA2 (u := A *ᵥ v) (c := 1) (by
    rw [Matrix.mulVec_mulVec, hA2, Matrix.one_mulVec, dotProduct_comm]
    exact hv)
  simpa [caSymp_transv_zero] using hmem

private theorem caSymp_fixed_ne (K : Subgroup (GL ι (ZMod 2)))
    (W : Submodule (ZMod 2) (ι → ZMod 2))
    (hKW : ∀ k ∈ K, ∀ w ∈ W, ((k : GL ι (ZMod 2)) : Matrix ι ι (ZMod 2)) *ᵥ w ∈ W)
    (hK2 : IsPGroup 2 K) (hW2 : 2 ∣ Nat.card W) :
    ∃ w ∈ W, w ≠ 0 ∧ ∀ k ∈ K, ((k : GL ι (ZMod 2)) : Matrix ι ι (ZMod 2)) *ᵥ w = w := by
  classical
  let smulF : K → ↥W → ↥W := fun k x =>
    ⟨((k : GL ι (ZMod 2)) : Matrix ι ι (ZMod 2)) *ᵥ (x : ι → ZMod 2), hKW k k.2 x x.2⟩
  let act : MulAction K ↥W :=
    { smul := smulF
      one_smul := fun x => by
        change smulF 1 x = x
        apply Subtype.ext
        show (((1 : ↥K) : GL ι (ZMod 2)) : Matrix ι ι (ZMod 2)) *ᵥ (x : ι → ZMod 2) = x
        rw [Subgroup.coe_one, Units.val_one, Matrix.one_mulVec]
      mul_smul := fun k l x => by
        change smulF (k * l) x = smulF k (smulF l x)
        apply Subtype.ext
        show (((k * l : ↥K) : GL ι (ZMod 2)) : Matrix ι ι (ZMod 2)) *ᵥ (x : ι → ZMod 2) =
          ((k : GL ι (ZMod 2)) : Matrix ι ι (ZMod 2)) *ᵥ
            (((l : GL ι (ZMod 2)) : Matrix ι ι (ZMod 2)) *ᵥ (x : ι → ZMod 2))
        rw [Subgroup.coe_mul, Units.val_mul, Matrix.mulVec_mulVec] }
  letI : SMul K ↥W := act.toSMul
  letI : MulAction K ↥W := act
  have h0 : (⟨0, W.zero_mem⟩ : ↥W) ∈ MulAction.fixedPoints K ↥W := by
    intro k
    change smulF k ⟨0, W.zero_mem⟩ = ⟨0, W.zero_mem⟩
    apply Subtype.ext
    show ((k : GL ι (ZMod 2)) : Matrix ι ι (ZMod 2)) *ᵥ (0 : ι → ZMod 2) = 0
    simp
  have hcard : 2 ∣ Nat.card (MulAction.fixedPoints K ↥W) := by
    have hmod := hK2.card_modEq_card_fixedPoints (α := ↥W)
    have hS2 : Nat.card ↥W ≡ 0 [MOD 2] := Nat.modEq_zero_iff_dvd.2 hW2
    have h := hmod.symm.trans hS2
    exact Nat.modEq_zero_iff_dvd.1 h
  obtain ⟨a, ha, hane⟩ : ∃ a : ↥W, a ∈ MulAction.fixedPoints K ↥W ∧ a ≠ ⟨0, W.zero_mem⟩ := by
    by_contra hcon
    push Not at hcon
    have hsingle : MulAction.fixedPoints K ↥W = {⟨0, W.zero_mem⟩} := by
      ext x
      constructor
      · intro hx
        rw [hcon x hx]
        exact Set.mem_singleton _
      · intro hx
        rw [Set.mem_singleton_iff] at hx
        subst hx
        exact h0
    have h1 : Nat.card (MulAction.fixedPoints K ↥W) = 1 := by rw [hsingle]; simp
    rw [h1] at hcard
    exact absurd hcard (by norm_num)
  refine ⟨(a : ι → ZMod 2), a.2, ?_, ?_⟩
  · intro h
    exact hane (Subtype.ext h)
  · intro k hk
    have hk' := ha ⟨k, hk⟩
    change smulF ⟨k, hk⟩ a = a at hk'
    exact congrArg Subtype.val hk'

private theorem caSymp_core (A : Matrix ι ι (ZMod 2)) (hAt : Aᵀ = A) (hA2 : A * A = 1)
    (W : Submodule (ZMod 2) (ι → ZMod 2))
    (hWalt : ∀ v ∈ W, v ⬝ᵥ (A *ᵥ v) = 0)
    (hWnd : ∀ w ∈ W, (∀ v ∈ W, w ⬝ᵥ (A *ᵥ v) = 0) → w = 0)
    (K : Subgroup (GL ι (ZMod 2)))
    (hKW : ∀ k ∈ K, ∀ w ∈ W, ((k : GL ι (ZMod 2)) : Matrix ι ι (ZMod 2)) *ᵥ w ∈ W)
    (hKiso : ∀ k ∈ K, ((k : GL ι (ZMod 2)) : Matrix ι ι (ZMod 2))ᵀ * A *
      ((k : GL ι (ZMod 2)) : Matrix ι ι (ZMod 2)) = A)
    (hnorm : ∀ k ∈ K, ∀ g : GL ι (ZMod 2),
      ((g : GL ι (ZMod 2)) : Matrix ι ι (ZMod 2))ᵀ * A *
        ((g : GL ι (ZMod 2)) : Matrix ι ι (ZMod 2)) = A → g * k * g⁻¹ ∈ K)
    (hK2 : IsPGroup 2 K) (hW2 : 2 ∣ Nat.card W) :
    ∀ w ∈ W, ∀ k ∈ K, ((k : GL ι (ZMod 2)) : Matrix ι ι (ZMod 2)) *ᵥ w = w := by
  classical
  obtain ⟨w0, hw0W, hw0ne, hw0fix⟩ := caSymp_fixed_ne K W hKW hK2 hW2
  let Cset : Set (ι → ZMod 2) := {w | w ∈ W ∧
    ∀ k ∈ K, ((k : GL ι (ZMod 2)) : Matrix ι ι (ZMod 2)) *ᵥ w = w}
  let C : Submodule (ZMod 2) (ι → ZMod 2) :=
    { carrier := Cset
      zero_mem' := ⟨W.zero_mem, fun k _ => by simp⟩
      add_mem' := by
        rintro a b ⟨haW, haK⟩ ⟨hbW, hbK⟩
        refine ⟨W.add_mem haW hbW, fun k hk => ?_⟩
        rw [Matrix.mulVec_add, haK k hk, hbK k hk]
      smul_mem' := by
        rintro c a ⟨haW, haK⟩
        refine ⟨W.smul_mem c haW, fun k hk => ?_⟩
        rw [Matrix.mulVec_smul, haK k hk] }
  have hw0C : w0 ∈ C := ⟨hw0W, hw0fix⟩
  have hstep : ∀ v ∈ W, w0 ⬝ᵥ (A *ᵥ v) = 1 → v ∈ C := by
    intro v hv h1
    have hT := caSymp_transv_mem A hAt hA2 (hWalt v hv)
    let tv : GL ι (ZMod 2) :=
      unipotentGL (nilMatrix A 1 (A *ᵥ v)) (caSymp_transv_zero A hA2 (hWalt v hv))
    have hTv : ((tv : GL ι (ZMod 2)) : Matrix ι ι (ZMod 2))ᵀ * A *
        ((tv : GL ι (ZMod 2)) : Matrix ι ι (ZMod 2)) = A := hT
    have happ := caSymp_transv_apply A hA2 (hWalt v hv) w0
    have hcomm : ((A *ᵥ v) ⬝ᵥ w0) = 1 := by
      rw [dotProduct_comm]
      exact h1
    have htvw : ((tv : GL ι (ZMod 2)) : Matrix ι ι (ZMod 2)) *ᵥ w0 = w0 + v := by
      rw [show ((tv : GL ι (ZMod 2)) : Matrix ι ι (ZMod 2)) *ᵥ w0 =
        w0 + ((A *ᵥ v) ⬝ᵥ w0) • v from happ, hcomm, one_smul]
    have hsumC : ((tv : GL ι (ZMod 2)) : Matrix ι ι (ZMod 2)) *ᵥ w0 ∈ C := by
      refine ⟨?_, ?_⟩
      · rw [htvw]
        exact W.add_mem hw0W hv
      · intro k hk
        have hinv : ((tv⁻¹ : GL ι (ZMod 2)) : Matrix ι ι (ZMod 2))ᵀ * A *
            ((tv⁻¹ : GL ι (ZMod 2)) : Matrix ι ι (ZMod 2)) = A :=
          (matrixIsometryGroup A).inv_mem hTv
        have hk' : tv⁻¹ * k * tv ∈ K := by
          have := hnorm k hk tv⁻¹ hinv
          simpa [inv_inv] using this
        have hfix := hw0C.2 (tv⁻¹ * k * tv) hk'
        have h1gl : (k : GL ι (ZMod 2)) * tv = tv * (tv⁻¹ * k * tv) := by group
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, h1gl, Units.val_mul,
          ← Matrix.mulVec_mulVec, hfix]
    have hsumC' : w0 + v ∈ C := by
      rw [← htvw]
      exact hsumC
    have hsub : (w0 + v) - w0 ∈ C := C.sub_mem hsumC' hw0C
    rwa [show (w0 + v) - w0 = v from by abel] at hsub
  have hWC : ∀ v ∈ W, v ∈ C := by
    intro v hv
    by_cases h1 : w0 ⬝ᵥ (A *ᵥ v) = 1
    · exact hstep v hv h1
    · have h0 : w0 ⬝ᵥ (A *ᵥ v) = 0 := by
        rcases caSymp_zmod2_eq_zero_or_one (w0 ⬝ᵥ (A *ᵥ v)) with h | h
        · exact h
        · exact absurd h h1
      obtain ⟨v0, hv0W, hv0ne⟩ : ∃ v0 ∈ W, w0 ⬝ᵥ (A *ᵥ v0) ≠ 0 := by
        by_contra hcon
        push Not at hcon
        exact hw0ne (hWnd w0 hw0W fun v hv => hcon v hv)
      have hv0 : w0 ⬝ᵥ (A *ᵥ v0) = 1 := by
        rcases caSymp_zmod2_eq_zero_or_one (w0 ⬝ᵥ (A *ᵥ v0)) with h | h
        · exact absurd h hv0ne
        · exact h
      have hsum1 : w0 ⬝ᵥ (A *ᵥ (v + v0)) = 1 := by
        rw [Matrix.mulVec_add, dotProduct_add, h0, hv0, zero_add]
      have h1C : v + v0 ∈ C := hstep (v + v0) (W.add_mem hv hv0W) hsum1
      have h0C : v0 ∈ C := hstep v0 hv0W hv0
      have hsub : (v + v0) - v0 ∈ C := C.sub_mem h1C h0C
      rwa [show (v + v0) - v0 = v from by abel] at hsub
  intro w hw k hk
  have hwC : w ∈ C := hWC w hw
  exact hwC.2 k hk

private theorem caSymp_two_dvd_card (W : Submodule (ZMod 2) (ι → ZMod 2)) [Nontrivial ↥W] :
    2 ∣ Nat.card ↥W := by
  have hdvd : Nat.card ↥W ∣ Nat.card (ι → ZMod 2) :=
    AddSubgroup.card_addSubgroup_dvd_card W.toAddSubgroup
  rw [Nat.card_fun] at hdvd
  have hZ : Nat.card (ZMod 2) = 2 := by
    rw [Nat.card_eq_fintype_card, ZMod.card]
  rw [hZ] at hdvd
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  haveI : Fintype ↥W := Fintype.ofFinite _
  have h2 : 2 ≤ Nat.card ↥W := by
    have h3 : 1 < Fintype.card ↥W := Fintype.one_lt_card
    rwa [Nat.card_eq_fintype_card]
  have hk0 : k ≠ 0 := by
    intro h0
    rw [h0, pow_zero] at hk'
    omega
  rw [hk']
  exact dvd_pow_self 2 hk0


private def caSymp_B3 : BlkIdx 1 7 := Sum.inr (Sum.inl 3)

private def caSymp_e : BlkIdx 1 7 → ZMod 2 := Pi.single caSymp_B3 1

private theorem caSymp_e_dot (y : BlkIdx 1 7 → ZMod 2) :
    caSymp_e ⬝ᵥ y = y caSymp_B3 := by simp [caSymp_e]

private theorem caSymp_dot_e (y : BlkIdx 1 7 → ZMod 2) :
    y ⬝ᵥ caSymp_e = y caSymp_B3 := by simp [caSymp_e]

private theorem caSymp_e_self : caSymp_e ⬝ᵥ caSymp_e = 1 := by
  rw [caSymp_e_dot]
  simp [caSymp_e]

theorem eq_bot_of_isPGroup_of_normal_sigmaFixed {m : ℕ} (hm : m = 6 ∨ m = 7)
    (K : Subgroup (GL (BlkIdx 1 m) (ZMod 2))) (hK : ∀ k ∈ K, sigmaStd m k = k)
    (hK2 : IsPGroup 2 K) (hn : ∀ g, sigmaStd m g = g → ∀ k ∈ K, g * k * g⁻¹ ∈ K) :
    K = ⊥ := by
  rcases hm with rfl | rfl
  ·
    have hAt : ((antiDiag 6 : GL (BlkIdx 1 6) (ZMod 2)) :
        Matrix (BlkIdx 1 6) (BlkIdx 1 6) (ZMod 2))ᵀ =
        ((antiDiag 6 : GL (BlkIdx 1 6) (ZMod 2)) :
          Matrix (BlkIdx 1 6) (BlkIdx 1 6) (ZMod 2)) := caSymp_antiDiag_transpose 6
    have hA2 : ((antiDiag 6 : GL (BlkIdx 1 6) (ZMod 2)) :
          Matrix (BlkIdx 1 6) (BlkIdx 1 6) (ZMod 2)) *
        ((antiDiag 6 : GL (BlkIdx 1 6) (ZMod 2)) :
          Matrix (BlkIdx 1 6) (BlkIdx 1 6) (ZMod 2)) = 1 := caSymp_antiDiag_mul_self_mat 6
    have hsqrt : sqrtDiag (((antiDiag 6 : GL (BlkIdx 1 6) (ZMod 2)) :
        Matrix (BlkIdx 1 6) (BlkIdx 1 6) (ZMod 2))) = 0 := by
      funext i
      rw [caSymp_sqrtDiag_apply, caSymp_antiDiag_apply_self]
      have h : antiDiagPerm 6 i ≠ i := by
        revert i
        decide
      simp [h]
    have hWalt : ∀ v ∈ (⊤ : Submodule (ZMod 2) (BlkIdx 1 6 → ZMod 2)),
        v ⬝ᵥ (((antiDiag 6 : GL (BlkIdx 1 6) (ZMod 2)) :
          Matrix (BlkIdx 1 6) (BlkIdx 1 6) (ZMod 2)) *ᵥ v) = 0 := by
      intro v _
      rw [dotProduct_mulVec_self_eq_sq hAt, hsqrt]
      simp
    have hWnd : ∀ w ∈ (⊤ : Submodule (ZMod 2) (BlkIdx 1 6 → ZMod 2)),
        (∀ v ∈ (⊤ : Submodule (ZMod 2) (BlkIdx 1 6 → ZMod 2)),
          w ⬝ᵥ (((antiDiag 6 : GL (BlkIdx 1 6) (ZMod 2)) :
            Matrix (BlkIdx 1 6) (BlkIdx 1 6) (ZMod 2)) *ᵥ v) = 0) → w = 0 := by
      intro w _ h
      exact caSymp_nondegenerate _ hAt hA2 (fun u => h u Submodule.mem_top)
    have hKW : ∀ k ∈ K, ∀ w ∈ (⊤ : Submodule (ZMod 2) (BlkIdx 1 6 → ZMod 2)),
        ((k : GL (BlkIdx 1 6) (ZMod 2)) : Matrix (BlkIdx 1 6) (BlkIdx 1 6) (ZMod 2)) *ᵥ w ∈
          (⊤ : Submodule (ZMod 2) (BlkIdx 1 6 → ZMod 2)) :=
      fun _ _ _ _ => Submodule.mem_top
    have hKiso : ∀ k ∈ K, ((k : GL (BlkIdx 1 6) (ZMod 2)) :
          Matrix (BlkIdx 1 6) (BlkIdx 1 6) (ZMod 2))ᵀ *
        ((antiDiag 6 : GL (BlkIdx 1 6) (ZMod 2)) :
          Matrix (BlkIdx 1 6) (BlkIdx 1 6) (ZMod 2)) *
        ((k : GL (BlkIdx 1 6) (ZMod 2)) :
          Matrix (BlkIdx 1 6) (BlkIdx 1 6) (ZMod 2)) =
        ((antiDiag 6 : GL (BlkIdx 1 6) (ZMod 2)) :
          Matrix (BlkIdx 1 6) (BlkIdx 1 6) (ZMod 2)) :=
      fun k hk => (caSymp_sigmaStd_eq_iff 6 k).mp (hK k hk)
    have hnorm : ∀ k ∈ K, ∀ g : GL (BlkIdx 1 6) (ZMod 2),
        ((g : GL (BlkIdx 1 6) (ZMod 2)) :
          Matrix (BlkIdx 1 6) (BlkIdx 1 6) (ZMod 2))ᵀ *
        ((antiDiag 6 : GL (BlkIdx 1 6) (ZMod 2)) :
          Matrix (BlkIdx 1 6) (BlkIdx 1 6) (ZMod 2)) *
        ((g : GL (BlkIdx 1 6) (ZMod 2)) :
          Matrix (BlkIdx 1 6) (BlkIdx 1 6) (ZMod 2)) =
        ((antiDiag 6 : GL (BlkIdx 1 6) (ZMod 2)) :
          Matrix (BlkIdx 1 6) (BlkIdx 1 6) (ZMod 2)) → g * k * g⁻¹ ∈ K := by
      intro k hk g hg
      exact hn g ((caSymp_sigmaStd_eq_iff 6 g).mpr hg) k hk
    have hW2 : 2 ∣ Nat.card (⊤ : Submodule (ZMod 2) (BlkIdx 1 6 → ZMod 2)) := by
      haveI : Nontrivial ↥(⊤ : Submodule (ZMod 2) (BlkIdx 1 6 → ZMod 2)) := by
        refine ⟨⟨0, Submodule.mem_top⟩, ⟨Pi.single (Sum.inl 0) 1, Submodule.mem_top⟩, ?_⟩
        intro h
        have := congrArg (fun x : BlkIdx 1 6 → ZMod 2 => x (Sum.inl 0))
          (Subtype.ext_iff.mp h)
        simpa using this
      exact caSymp_two_dvd_card ⊤
    have htriv := caSymp_core _ hAt hA2 ⊤ hWalt hWnd K hKW hKiso hnorm hK2 hW2
    rw [eq_bot_iff]
    intro k hk
    have hmat : ((k : GL (BlkIdx 1 6) (ZMod 2)) :
        Matrix (BlkIdx 1 6) (BlkIdx 1 6) (ZMod 2)) = 1 := by
      apply Matrix.ext_of_mulVec_single
      intro j
      rw [Matrix.one_mulVec]
      exact htriv (Pi.single j 1) Submodule.mem_top k hk
    exact Units.ext hmat
  ·
    let W : Submodule (ZMod 2) (BlkIdx 1 7 → ZMod 2) :=
      LinearMap.ker (LinearMap.proj (φ := fun _ : BlkIdx 1 7 => ZMod 2) caSymp_B3)
    have hAt : ((antiDiag 7 : GL (BlkIdx 1 7) (ZMod 2)) :
        Matrix (BlkIdx 1 7) (BlkIdx 1 7) (ZMod 2))ᵀ =
        ((antiDiag 7 : GL (BlkIdx 1 7) (ZMod 2)) :
          Matrix (BlkIdx 1 7) (BlkIdx 1 7) (ZMod 2)) := caSymp_antiDiag_transpose 7
    have hA2 : ((antiDiag 7 : GL (BlkIdx 1 7) (ZMod 2)) :
          Matrix (BlkIdx 1 7) (BlkIdx 1 7) (ZMod 2)) *
        ((antiDiag 7 : GL (BlkIdx 1 7) (ZMod 2)) :
          Matrix (BlkIdx 1 7) (BlkIdx 1 7) (ZMod 2)) = 1 := caSymp_antiDiag_mul_self_mat 7
    have hsqrt : sqrtDiag (((antiDiag 7 : GL (BlkIdx 1 7) (ZMod 2)) :
        Matrix (BlkIdx 1 7) (BlkIdx 1 7) (ZMod 2))) = caSymp_e := by
      change sqrtDiag (((antiDiag 7 : GL (BlkIdx 1 7) (ZMod 2)) :
        Matrix (BlkIdx 1 7) (BlkIdx 1 7) (ZMod 2))) = Pi.single (Sum.inr (Sum.inl 3)) 1
      have hfix : antiDiagPerm 7 (Sum.inr (Sum.inl 3)) = Sum.inr (Sum.inl 3) := by decide
      have hiff : ∀ i : BlkIdx 1 7, antiDiagPerm 7 i = i ↔ i = Sum.inr (Sum.inl 3) := by
        decide
      funext i
      rw [caSymp_sqrtDiag_apply, caSymp_antiDiag_apply_self]
      by_cases h : i = Sum.inr (Sum.inl 3)
      · subst h
        simp [hfix]
      · have h' : antiDiagPerm 7 i ≠ i := fun hc => h ((hiff i).mp hc)
        simp [h, h']
    have hAe : ((antiDiag 7 : GL (BlkIdx 1 7) (ZMod 2)) :
        Matrix (BlkIdx 1 7) (BlkIdx 1 7) (ZMod 2)) *ᵥ caSymp_e = caSymp_e := by
      have h := sqrtDiag_mul_mul_transpose hAt ((antiDiag 7 : GL (BlkIdx 1 7) (ZMod 2)) :
        Matrix (BlkIdx 1 7) (BlkIdx 1 7) (ZMod 2))
      rw [hA2, Matrix.one_mul, hAt, hsqrt] at h
      exact h.symm
    have hmem_iff : ∀ v : BlkIdx 1 7 → ZMod 2, v ∈ W ↔ v caSymp_B3 = 0 := by
      intro v
      change v ∈ LinearMap.ker (LinearMap.proj (φ := fun _ : BlkIdx 1 7 => ZMod 2) caSymp_B3) ↔ _
      rw [LinearMap.mem_ker, LinearMap.proj_apply]
    have hWalt : ∀ v ∈ W, v ⬝ᵥ (((antiDiag 7 : GL (BlkIdx 1 7) (ZMod 2)) :
        Matrix (BlkIdx 1 7) (BlkIdx 1 7) (ZMod 2)) *ᵥ v) = 0 := by
      intro v hv
      have hv0 : v caSymp_B3 = 0 := (hmem_iff v).mp hv
      rw [dotProduct_mulVec_self_eq_sq hAt, hsqrt]
      rw [caSymp_e_dot, hv0]
      simp
    have hWnd : ∀ w ∈ W, (∀ v ∈ W, w ⬝ᵥ (((antiDiag 7 : GL (BlkIdx 1 7) (ZMod 2)) :
        Matrix (BlkIdx 1 7) (BlkIdx 1 7) (ZMod 2)) *ᵥ v) = 0) → w = 0 := by
      intro w hw h
      apply caSymp_nondegenerate _ hAt hA2
      intro u
      have hwe : w ⬝ᵥ caSymp_e = 0 := by
        rw [caSymp_dot_e]
        exact (hmem_iff w).mp hw
      have huW : u - (u caSymp_B3) • caSymp_e ∈ W := by
        rw [hmem_iff]
        simp [caSymp_e, Pi.single_apply]
      have h1 := h (u - (u caSymp_B3) • caSymp_e) huW
      have hu : u = (u - (u caSymp_B3) • caSymp_e) + (u caSymp_B3) • caSymp_e := by abel
      rw [hu, Matrix.mulVec_add, Matrix.mulVec_smul, hAe]
      rw [dotProduct_add, h1, dotProduct_smul, hwe]
      simp
    have hkte : ∀ k ∈ K, ((k : GL (BlkIdx 1 7) (ZMod 2)) :
        Matrix (BlkIdx 1 7) (BlkIdx 1 7) (ZMod 2))ᵀ *ᵥ caSymp_e = caSymp_e := by
      intro k hk
      have hkiso : ((k : GL (BlkIdx 1 7) (ZMod 2)) :
          Matrix (BlkIdx 1 7) (BlkIdx 1 7) (ZMod 2))ᵀ *
          ((antiDiag 7 : GL (BlkIdx 1 7) (ZMod 2)) :
            Matrix (BlkIdx 1 7) (BlkIdx 1 7) (ZMod 2)) *
          ((k : GL (BlkIdx 1 7) (ZMod 2)) :
            Matrix (BlkIdx 1 7) (BlkIdx 1 7) (ZMod 2)) =
          ((antiDiag 7 : GL (BlkIdx 1 7) (ZMod 2)) :
            Matrix (BlkIdx 1 7) (BlkIdx 1 7) (ZMod 2)) :=
        (caSymp_sigmaStd_eq_iff 7 k).mp (hK k hk)
      have h := sqrtDiag_mul_mul_transpose hAt ((k : GL (BlkIdx 1 7) (ZMod 2)) :
        Matrix (BlkIdx 1 7) (BlkIdx 1 7) (ZMod 2))ᵀ
      rw [Matrix.transpose_transpose, hkiso, hsqrt] at h
      exact h.symm
    have hKW : ∀ k ∈ K, ∀ w ∈ W, ((k : GL (BlkIdx 1 7) (ZMod 2)) :
        Matrix (BlkIdx 1 7) (BlkIdx 1 7) (ZMod 2)) *ᵥ w ∈ W := by
      intro k hk w hw
      have hke := hkte k hk
      rw [hmem_iff]
      calc (((k : GL (BlkIdx 1 7) (ZMod 2)) :
            Matrix (BlkIdx 1 7) (BlkIdx 1 7) (ZMod 2)) *ᵥ w) caSymp_B3
          = caSymp_e ⬝ᵥ (((k : GL (BlkIdx 1 7) (ZMod 2)) :
              Matrix (BlkIdx 1 7) (BlkIdx 1 7) (ZMod 2)) *ᵥ w) := by
            rw [caSymp_e_dot]
        _ = (((k : GL (BlkIdx 1 7) (ZMod 2)) :
              Matrix (BlkIdx 1 7) (BlkIdx 1 7) (ZMod 2))ᵀ *ᵥ caSymp_e) ⬝ᵥ w := by
            rw [Matrix.dotProduct_mulVec, caSymp_vecMul_eq]
        _ = caSymp_e ⬝ᵥ w := by rw [hke]
        _ = w caSymp_B3 := caSymp_e_dot w
        _ = 0 := (hmem_iff w).mp hw
    have hKiso : ∀ k ∈ K, ((k : GL (BlkIdx 1 7) (ZMod 2)) :
          Matrix (BlkIdx 1 7) (BlkIdx 1 7) (ZMod 2))ᵀ *
        ((antiDiag 7 : GL (BlkIdx 1 7) (ZMod 2)) :
          Matrix (BlkIdx 1 7) (BlkIdx 1 7) (ZMod 2)) *
        ((k : GL (BlkIdx 1 7) (ZMod 2)) :
          Matrix (BlkIdx 1 7) (BlkIdx 1 7) (ZMod 2)) =
        ((antiDiag 7 : GL (BlkIdx 1 7) (ZMod 2)) :
          Matrix (BlkIdx 1 7) (BlkIdx 1 7) (ZMod 2)) :=
      fun k hk => (caSymp_sigmaStd_eq_iff 7 k).mp (hK k hk)
    have hnorm : ∀ k ∈ K, ∀ g : GL (BlkIdx 1 7) (ZMod 2),
        ((g : GL (BlkIdx 1 7) (ZMod 2)) :
          Matrix (BlkIdx 1 7) (BlkIdx 1 7) (ZMod 2))ᵀ *
        ((antiDiag 7 : GL (BlkIdx 1 7) (ZMod 2)) :
          Matrix (BlkIdx 1 7) (BlkIdx 1 7) (ZMod 2)) *
        ((g : GL (BlkIdx 1 7) (ZMod 2)) :
          Matrix (BlkIdx 1 7) (BlkIdx 1 7) (ZMod 2)) =
        ((antiDiag 7 : GL (BlkIdx 1 7) (ZMod 2)) :
          Matrix (BlkIdx 1 7) (BlkIdx 1 7) (ZMod 2)) → g * k * g⁻¹ ∈ K := by
      intro k hk g hg
      exact hn g ((caSymp_sigmaStd_eq_iff 7 g).mpr hg) k hk
    have hmemW : (Pi.single (Sum.inl 0) 1 : BlkIdx 1 7 → ZMod 2) ∈ W := by
      rw [hmem_iff, Pi.single_eq_of_ne (by intro h; exact Sum.inl_ne_inr h.symm)]
    have hW2 : 2 ∣ Nat.card W := by
      haveI : Nontrivial ↥W := by
        refine ⟨⟨0, W.zero_mem⟩, ⟨Pi.single (Sum.inl 0) 1, hmemW⟩, ?_⟩
        intro h
        have := congrArg (fun x : BlkIdx 1 7 → ZMod 2 => x (Sum.inl 0))
          (Subtype.ext_iff.mp h)
        simp at this
      exact caSymp_two_dvd_card W
    have htrivW := caSymp_core _ hAt hA2 W hWalt hWnd K hKW hKiso hnorm hK2 hW2
    rw [eq_bot_iff]
    intro k hk
    have hkiso := hKiso k hk
    have hke := hkte k hk
    have hw0W : ((((k : GL (BlkIdx 1 7) (ZMod 2)) :
          Matrix (BlkIdx 1 7) (BlkIdx 1 7) (ZMod 2)) *ᵥ caSymp_e) - caSymp_e) ∈ W := by
      rw [hmem_iff]
      have hB3 : (((k : GL (BlkIdx 1 7) (ZMod 2)) :
          Matrix (BlkIdx 1 7) (BlkIdx 1 7) (ZMod 2)) *ᵥ caSymp_e) caSymp_B3 = 1 := by
        have h1 : (((k : GL (BlkIdx 1 7) (ZMod 2)) :
            Matrix (BlkIdx 1 7) (BlkIdx 1 7) (ZMod 2)) *ᵥ caSymp_e) caSymp_B3 =
            caSymp_e ⬝ᵥ (((k : GL (BlkIdx 1 7) (ZMod 2)) :
              Matrix (BlkIdx 1 7) (BlkIdx 1 7) (ZMod 2)) *ᵥ caSymp_e) := by
          rw [caSymp_e_dot]
        rw [h1, Matrix.dotProduct_mulVec, caSymp_vecMul_eq, hke]
        exact caSymp_e_self
      rw [Pi.sub_apply, hB3]
      simp [caSymp_e]
    have hw0orth : ∀ y ∈ W, ((((k : GL (BlkIdx 1 7) (ZMod 2)) :
          Matrix (BlkIdx 1 7) (BlkIdx 1 7) (ZMod 2)) *ᵥ caSymp_e) - caSymp_e) ⬝ᵥ
        (((antiDiag 7 : GL (BlkIdx 1 7) (ZMod 2)) :
          Matrix (BlkIdx 1 7) (BlkIdx 1 7) (ZMod 2)) *ᵥ y) = 0 := by
      intro y hy
      have hyfix : ((k : GL (BlkIdx 1 7) (ZMod 2)) :
          Matrix (BlkIdx 1 7) (BlkIdx 1 7) (ZMod 2)) *ᵥ y = y := htrivW y hy k hk
      have hAy : caSymp_e ⬝ᵥ (((antiDiag 7 : GL (BlkIdx 1 7) (ZMod 2)) :
          Matrix (BlkIdx 1 7) (BlkIdx 1 7) (ZMod 2)) *ᵥ y) = 0 := by
        rw [Matrix.dotProduct_mulVec, caSymp_vecMul_eq, hAt, hAe, caSymp_e_dot]
        exact (hmem_iff y).mp hy
      rw [sub_dotProduct]
      have h1 : (((k : GL (BlkIdx 1 7) (ZMod 2)) :
            Matrix (BlkIdx 1 7) (BlkIdx 1 7) (ZMod 2)) *ᵥ caSymp_e) ⬝ᵥ
          (((antiDiag 7 : GL (BlkIdx 1 7) (ZMod 2)) :
            Matrix (BlkIdx 1 7) (BlkIdx 1 7) (ZMod 2)) *ᵥ y) = 0 := by
        rw [← hyfix, caSymp_beta_apply _ _ caSymp_e y hkiso]
        exact hAy
      rw [h1, hAy, sub_self]
    have hw0z : (((k : GL (BlkIdx 1 7) (ZMod 2)) :
        Matrix (BlkIdx 1 7) (BlkIdx 1 7) (ZMod 2)) *ᵥ caSymp_e) - caSymp_e = 0 :=
      hWnd _ hw0W hw0orth
    have hke' : ((k : GL (BlkIdx 1 7) (ZMod 2)) :
        Matrix (BlkIdx 1 7) (BlkIdx 1 7) (ZMod 2)) *ᵥ caSymp_e = caSymp_e := sub_eq_zero.mp hw0z
    have hcol : ∀ j : BlkIdx 1 7, ((k : GL (BlkIdx 1 7) (ZMod 2)) :
        Matrix (BlkIdx 1 7) (BlkIdx 1 7) (ZMod 2)) *ᵥ Pi.single j 1 = Pi.single j 1 := by
      intro j
      by_cases hj : j = caSymp_B3
      · subst hj
        simpa [caSymp_e] using hke'
      · have hmemj : (Pi.single j 1 : BlkIdx 1 7 → ZMod 2) ∈ W := by
          rw [hmem_iff, Pi.single_eq_of_ne (by intro h; exact hj h.symm)]
        rw [htrivW _ hmemj k hk]
    have hmat : ((k : GL (BlkIdx 1 7) (ZMod 2)) :
        Matrix (BlkIdx 1 7) (BlkIdx 1 7) (ZMod 2)) = 1 := by
      apply Matrix.ext_of_mulVec_single
      intro j
      rw [Matrix.one_mulVec]
      exact hcol j
    exact Units.ext hmat

end CFSG.StandardType.FF81.CentA

end
