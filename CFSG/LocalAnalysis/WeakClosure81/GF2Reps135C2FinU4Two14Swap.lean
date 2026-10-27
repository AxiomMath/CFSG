module

public import CFSG.HardMathSupport.U4FF.ClassLocCheck

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open scoped MatrixGroups
open Matrix
open CFSG.HardMathSupport.U4FF (FK LocSpec ambDim ambEq ambRepF ambRepF_apply ambRep_apply
  kronDep_apply fsOf)

abbrev FinU4AmbIdx : Type := Fin (ambDim (fsOf true false true))

@[expose] def finU4Fst (x : FinU4AmbIdx) : Fin 4 :=
  (ambEq (fsOf true false true)).symm x ⟨0, by decide⟩

@[expose] def finU4Snd (x : FinU4AmbIdx) : Fin 4 :=
  (ambEq (fsOf true false true)).symm x ⟨1, by decide⟩

@[expose] def finU4Swap (x : FinU4AmbIdx) : FinU4AmbIdx :=
  ⟨(x : ℕ) / 4 + 4 * ((x : ℕ) % 4), by
    have h : ambDim (fsOf true false true) = 16 := by decide +kernel
    have := x.isLt
    omega⟩

@[expose] def finU4SwapMat (R : Type*) [Zero R] [One R] : Matrix FinU4AmbIdx FinU4AmbIdx R :=
  Matrix.of fun x y => if finU4Swap x = y then 1 else 0

theorem finU4Swap_swap (x : FinU4AmbIdx) : finU4Swap (finU4Swap x) = x := by
  revert x
  decide +kernel

theorem finU4Swap_eq_iff {x y : FinU4AmbIdx} : finU4Swap x = y ↔ x = finU4Swap y :=
  ⟨fun h => by rw [← h, finU4Swap_swap], fun h => by rw [h, finU4Swap_swap]⟩

theorem finU4Fst_swap (x : FinU4AmbIdx) : finU4Fst (finU4Swap x) = finU4Snd x := by
  revert x
  decide +kernel

theorem finU4Snd_swap (x : FinU4AmbIdx) : finU4Snd (finU4Swap x) = finU4Fst x := by
  revert x
  decide +kernel

theorem finU4SwapMat_mul_apply {R : Type*} [Semiring R] (A : Matrix FinU4AmbIdx FinU4AmbIdx R)
    (x v : FinU4AmbIdx) : (finU4SwapMat R * A) x v = A (finU4Swap x) v := by
  simp [Matrix.mul_apply, finU4SwapMat]

theorem mul_finU4SwapMat_apply {R : Type*} [Semiring R] (A : Matrix FinU4AmbIdx FinU4AmbIdx R)
    (x y : FinU4AmbIdx) : (A * finU4SwapMat R) x y = A x (finU4Swap y) := by
  simp [Matrix.mul_apply, finU4SwapMat, finU4Swap_eq_iff]

theorem finU4SwapMat_mul_mul {R : Type*} [Semiring R] (A : Matrix FinU4AmbIdx FinU4AmbIdx R)
    (x y : FinU4AmbIdx) :
    (finU4SwapMat R * A * finU4SwapMat R) x y = A (finU4Swap x) (finU4Swap y) := by
  rw [mul_finU4SwapMat_apply, finU4SwapMat_mul_apply]

theorem finU4SwapMat_mul_self (R : Type*) [Semiring R] :
    finU4SwapMat R * finU4SwapMat R = 1 := by
  ext x y
  rw [finU4SwapMat_mul_apply, Matrix.one_apply]
  simp [finU4SwapMat, finU4Swap_swap]

theorem ambRepF_apply_natDual (k : Type*) [Field k] (g : SL(4, k)) (x y : FinU4AmbIdx) :
    ambRepF k (fsOf true false true) g x y =
      (g : Matrix (Fin 4) (Fin 4) k) (finU4Fst x) (finU4Fst y) *
        ((g⁻¹ : SL(4, k)) : Matrix (Fin 4) (Fin 4) k) (finU4Snd y) (finU4Snd x) := by
  rw [ambRepF_apply, Matrix.submatrix_apply, ambRep_apply, kronDep_apply]
  have h2 : ∀ f : Fin (fsOf true false true).length → k, ∏ i, f i = f ⟨0, by decide⟩ *
      f ⟨1, by decide⟩ := fun f => Fin.prod_univ_two f
  rw [h2]
  rfl

theorem inv_transpose_inv_eq {k : Type*} [Field k] (g : SL(4, k)) :
    (Matrix.SpecialLinearGroup.transpose g⁻¹)⁻¹ = Matrix.SpecialLinearGroup.transpose g := by
  refine inv_eq_of_mul_eq_one_right (Subtype.ext ?_)
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_transpose,
    Matrix.SpecialLinearGroup.coe_transpose, ← Matrix.transpose_mul,
    ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one,
    Matrix.transpose_one]

theorem finU4SwapMat_mul_ambRepF_mul (k : Type*) [Field k] (g : SL(4, k)) :
    finU4SwapMat k * ambRepF k (fsOf true false true) g * finU4SwapMat k =
      ambRepF k (fsOf true false true) (Matrix.SpecialLinearGroup.transpose g⁻¹) := by
  ext x y
  rw [finU4SwapMat_mul_mul, ambRepF_apply_natDual, ambRepF_apply_natDual,
    inv_transpose_inv_eq]
  simp only [finU4Fst_swap, finU4Snd_swap, Matrix.SpecialLinearGroup.coe_transpose,
    Matrix.transpose_apply]
  exact mul_comm _ _

theorem ambRepF_natDual_map {k k' : Type*} [Field k] [Field k'] (φ : k →+* k') (g : SL(4, k)) :
    (ambRepF k (fsOf true false true) g).map φ =
      ambRepF k' (fsOf true false true) (Matrix.SpecialLinearGroup.map φ g) := by
  ext x y
  have hinv : ((Matrix.SpecialLinearGroup.map φ g)⁻¹ : SL(4, k')) =
      Matrix.SpecialLinearGroup.map φ g⁻¹ := (map_inv _ g).symm
  rw [Matrix.map_apply, ambRepF_apply_natDual, ambRepF_apply_natDual, hinv, map_mul]
  simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply]

theorem locMat_swap_intertwines {fs : List FK} (S : LocSpec fs) {k : Type*} [Field k] [CharP k 2]
    (τ : Matrix (Fin (ambDim fs)) (Fin (ambDim fs)) k) (hτ : τ * τ = 1)
    (hB : S.Pik k * (τ * S.Bk k) = τ * S.Bk k) (hz : τ *ᵥ S.zk k = S.zk k)
    {g g' : SL(4, k)} (hg : τ * ambRepF k fs g * τ = ambRepF k fs g') :
    (S.Pmk k * τ * S.Bk k) * S.locMat k g = S.locMat k g' * (S.Pmk k * τ * S.Bk k) := by
  have hPz : S.Pmk k *ᵥ S.zk k = 0 := S.Pmk_z k
  have hz' : ambRepF k fs g' *ᵥ S.zk k = S.zk k := (S.Stab_all (k := k) g').2
  have hL : (S.Pmk k * τ * S.Bk k) * S.locMat k g = S.Pmk k * τ * (ambRepF k fs g * S.Bk k) := by
    obtain ⟨w, hw⟩ : ∃ w, ambRepF k fs g * S.Bk k = S.Bk k * S.locMat k g +
        vecMulVec (S.zk k) w := ⟨_, S.amb_B k g⟩
    have hz0 : S.Pmk k * τ * vecMulVec (S.zk k) w = 0 := by
      rw [Matrix.mul_assoc, Matrix.mul_vecMulVec, hz, Matrix.mul_vecMulVec, hPz]
      ext i j
      simp [Matrix.vecMulVec_apply]
    rw [hw, Matrix.mul_add, hz0, add_zero, Matrix.mul_assoc]
  have hτB : τ * S.Bk k = S.Bk k * (S.Pmk k * τ * S.Bk k) +
      vecMulVec (S.zk k) (S.zetak k ᵥ* (τ * S.Bk k)) := by
    calc τ * S.Bk k = S.Pik k * (τ * S.Bk k) := hB.symm
      _ = (S.Bk k * S.Pmk k + vecMulVec (S.zk k) (S.zetak k)) * (τ * S.Bk k) := rfl
      _ = _ := by rw [Matrix.add_mul, Matrix.vecMulVec_mul]; simp only [Matrix.mul_assoc]
  have hR : S.locMat k g' * (S.Pmk k * τ * S.Bk k) =
      S.Pmk k * (ambRepF k fs g' * (τ * S.Bk k)) := by
    have h0 : S.Pmk k * vecMulVec (S.zk k) (S.zetak k ᵥ* (τ * S.Bk k)) = 0 := by
      rw [Matrix.mul_vecMulVec, hPz]
      ext i j
      simp [Matrix.vecMulVec_apply]
    have h1 : S.Pmk k * (ambRepF k fs g' *
        vecMulVec (S.zk k) (S.zetak k ᵥ* (τ * S.Bk k))) = 0 := by
      rw [Matrix.mul_vecMulVec, hz', h0]
    conv_rhs => rw [hτB, Matrix.mul_add, Matrix.mul_add, h1, add_zero]
    unfold LocSpec.locMat
    simp only [Matrix.mul_assoc]
  have hA : ambRepF k fs g' * τ = τ * ambRepF k fs g := by
    rw [← hg, Matrix.mul_assoc (τ * ambRepF k fs g) τ τ, hτ, Matrix.mul_one]
  calc (S.Pmk k * τ * S.Bk k) * S.locMat k g = S.Pmk k * τ * (ambRepF k fs g * S.Bk k) := hL
    _ = S.Pmk k * ((τ * ambRepF k fs g) * S.Bk k) := by simp only [Matrix.mul_assoc]
    _ = S.Pmk k * ((ambRepF k fs g' * τ) * S.Bk k) := by rw [hA]
    _ = S.Pmk k * (ambRepF k fs g' * (τ * S.Bk k)) := by simp only [Matrix.mul_assoc]
    _ = S.locMat k g' * (S.Pmk k * τ * S.Bk k) := hR.symm

end CFSG.LocalAnalysis.WeakClosure81
