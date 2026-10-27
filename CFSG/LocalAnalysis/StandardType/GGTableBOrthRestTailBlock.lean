module

public import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestTailSupp

public section

namespace CFSG.StandardType

open CFSG.Assembly Matrix CFSG.SeitzReduction.OmegaPilot
open scoped Kronecker

namespace OrthRestTail

variable {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]

variable (K) in
@[expose] noncomputable def kronMat : Matrix (Fin 2) (Fin 2) K × Matrix (Fin 2) (Fin 2) K →*
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) K where
  toFun AB := AB.1 ⊗ₖ AB.2
  map_one' := one_kronecker_one
  map_mul' x y := mul_kronecker_mul x.1 y.1 x.2 y.2

variable (K) in
@[expose] noncomputable def kronGL :
    Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K →*
      GL (Fin 2 × Fin 2) K :=
  (Units.map (kronMat K)).comp (MulEquiv.prodUnits.symm.toMonoidHom.comp
    (MonoidHom.prodMap Matrix.SpecialLinearGroup.toGL Matrix.SpecialLinearGroup.toGL))

theorem coe_kronGL
    (AB : Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K) :
    ((kronGL K AB : GL (Fin 2 × Fin 2) K) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) K) =
      (AB.1 : Matrix (Fin 2) (Fin 2) K) ⊗ₖ (AB.2 : Matrix (Fin 2) (Fin 2) K) :=
  rfl

omit [Fintype ι] [DecidableEq ι] in
@[expose] def toMat2 (x : Fin 2 × Fin 2 → K) : Matrix (Fin 2) (Fin 2) K :=
  Matrix.of fun r s => x (r, s)

omit [Fintype ι] [DecidableEq ι] in
theorem toMat2_kronecker_mulVec (A B : Matrix (Fin 2) (Fin 2) K) (x : Fin 2 × Fin 2 → K) :
    toMat2 ((A ⊗ₖ B) *ᵥ x) = A * toMat2 x * Bᵀ := by
  ext r s
  simp only [toMat2, Matrix.of_apply, mulVec, dotProduct, Fintype.sum_prod_type, kronecker_apply,
    Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two]
  ring

structure HypBlock (Q : QuadraticForm K (ι → K)) where
  pos : Fin 2 × Fin 2 ↪ ι
  hyp₀ : IsHypCoord Q (pos (0, 0)) (pos (1, 1))
  hyp₁ : IsHypCoord Q (pos (0, 1)) (pos (1, 0))

namespace HypBlock

variable {Q : QuadraticForm K (ι → K)} (B : HypBlock Q)

@[expose] noncomputable def blkGL :
    Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K →* GL ι K :=
  (posGL B.pos).comp (kronGL K)

theorem blkGL_mulVec
    (AB : Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K)
    (v : ι → K) : ((B.blkGL AB : GL ι K) : Matrix ι ι K) *ᵥ v =
      posLin B.pos ((AB.1 : Matrix (Fin 2) (Fin 2) K) ⊗ₖ (AB.2 : Matrix (Fin 2) (Fin 2) K)) v := by
  rw [blkGL, MonoidHom.comp_apply, posGL_mulVec, coe_kronGL]

theorem blkGL_mem_suppSub
    (AB : Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K) :
    B.blkGL AB ∈ suppSub K (Set.range B.pos) :=
  posGL_mem_suppSub _ _

theorem toMat2_blkGL
    (AB : Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K)
    (v : ι → K) : toMat2 ((((B.blkGL AB : GL ι K) : Matrix ι ι K) *ᵥ v) ∘ B.pos) =
      (AB.1 : Matrix (Fin 2) (Fin 2) K) * toMat2 (v ∘ B.pos) *
        (AB.2 : Matrix (Fin 2) (Fin 2) K)ᵀ := by
  rw [B.blkGL_mulVec AB v, posLin_comp_pos, toMat2_kronecker_mulVec]

omit [Fintype ι] in
@[expose] noncomputable def rest (v : ι → K) : ι → K := Function.extend B.pos 0 v

omit [Fintype ι] in
theorem rest_apply_pos (v : ι → K) (rs : Fin 2 × Fin 2) : B.rest v (B.pos rs) = 0 :=
  B.pos.injective.extend_apply _ _ _

omit [Fintype ι] in
theorem rest_apply_of_not_mem (v : ι → K) {k : ι} (hk : k ∉ Set.range B.pos) :
    B.rest v k = v k :=
  Function.extend_apply' _ _ _ hk

omit [Fintype ι] in
theorem map_eq (v : ι → K) :
    Q v = v (B.pos (0, 0)) * v (B.pos (1, 1)) + v (B.pos (0, 1)) * v (B.pos (1, 0)) +
      Q (B.rest v) := by
  have hv : v = v (B.pos (0, 0)) • Pi.single (B.pos (0, 0)) 1 +
      v (B.pos (1, 1)) • Pi.single (B.pos (1, 1)) 1 +
      (v (B.pos (0, 1)) • Pi.single (B.pos (0, 1)) 1 +
        v (B.pos (1, 0)) • Pi.single (B.pos (1, 0)) 1 + B.rest v) := by
    funext k
    by_cases hk : k ∈ Set.range B.pos
    · obtain ⟨⟨r, s⟩, rfl⟩ := hk
      fin_cases r <;> fin_cases s <;>
        simp [rest_apply_pos, B.pos.injective.eq_iff]
    · have hne : ∀ rs, k ≠ B.pos rs := fun rs h => hk ⟨rs, h.symm⟩
      simp [rest_apply_of_not_mem B v hk, hne]
  have h1 : Q (v (B.pos (0, 1)) • Pi.single (B.pos (0, 1)) 1 +
      v (B.pos (1, 0)) • Pi.single (B.pos (1, 0)) 1 + B.rest v) =
      v (B.pos (0, 1)) * v (B.pos (1, 0)) + Q (B.rest v) :=
    B.hyp₁.map_add_smul _ _ (B.rest_apply_pos v _) (B.rest_apply_pos v _)
  conv_lhs => rw [hv]
  rw [B.hyp₀.map_add_smul _ _ ?_ ?_, h1, add_assoc]
  · simp [rest_apply_pos, B.pos.injective.eq_iff]
  · simp [rest_apply_pos, B.pos.injective.eq_iff]

variable [CharP K 2]

omit [Fintype ι] in
theorem det_toMat2 (v : ι → K) :
    (toMat2 (v ∘ B.pos)).det =
      v (B.pos (0, 0)) * v (B.pos (1, 1)) + v (B.pos (0, 1)) * v (B.pos (1, 0)) := by
  rw [Matrix.det_fin_two, CharTwo.sub_eq_add]
  rfl

theorem map_blkGL
    (AB : Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K)
    (v : ι → K) : Q (((B.blkGL AB : GL ι K) : Matrix ι ι K) *ᵥ v) = Q v := by
  have hrest : B.rest (((B.blkGL AB : GL ι K) : Matrix ι ι K) *ᵥ v) = B.rest v := by
    funext k
    by_cases hk : k ∈ Set.range B.pos
    · obtain ⟨rs, rfl⟩ := hk
      rw [rest_apply_pos, rest_apply_pos]
    · rw [rest_apply_of_not_mem _ _ hk, rest_apply_of_not_mem _ _ hk, blkGL_mulVec,
        posLin_apply_of_not_mem _ _ _ hk]
  rw [B.map_eq (((B.blkGL AB : GL ι K) : Matrix ι ι K) *ᵥ v), B.map_eq v, hrest,
    ← det_toMat2, ← det_toMat2, toMat2_blkGL, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_transpose, Matrix.SpecialLinearGroup.det_coe, Matrix.SpecialLinearGroup.det_coe,
    one_mul, mul_one]

theorem blkGL_mem_orth
    (AB : Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K) :
    B.blkGL AB ∈ LargeEvenOrthGroup ⇑Q :=
  TableBSymp.mem_orthGroup_of_isometry (B.map_blkGL AB)

theorem blkGL_injective : Function.Injective B.blkGL := by
  rw [injective_iff_map_eq_one]
  rintro ⟨A, A'⟩ h
  have hX : ∀ X : Matrix (Fin 2) (Fin 2) K,
      (A : Matrix (Fin 2) (Fin 2) K) * X * (A' : Matrix (Fin 2) (Fin 2) K)ᵀ = X := by
    intro X
    have h1 := B.toMat2_blkGL (A, A') (Function.extend B.pos (fun rs => X rs.1 rs.2) 0)
    rw [h, Units.val_one, one_mulVec] at h1
    have h2 : toMat2 (Function.extend B.pos (fun rs => X rs.1 rs.2) 0 ∘ B.pos) = X := by
      ext r s
      simp only [toMat2, Matrix.of_apply, Function.comp_apply]
      exact B.pos.injective.extend_apply _ _ (r, s)
    rw [h2] at h1
    exact h1.symm
  have hAA : (A : Matrix (Fin 2) (Fin 2) K) * (A' : Matrix (Fin 2) (Fin 2) K)ᵀ = 1 := by
    simpa using hX 1
  have hAA' : (A' : Matrix (Fin 2) (Fin 2) K)ᵀ * (A : Matrix (Fin 2) (Fin 2) K) = 1 :=
    mul_eq_one_comm.mp hAA
  have hcomm : ∀ X : Matrix (Fin 2) (Fin 2) K, Commute X (A : Matrix (Fin 2) (Fin 2) K) := by
    intro X
    calc X * A = A * X * (A' : Matrix (Fin 2) (Fin 2) K)ᵀ * A := by rw [hX X]
      _ = A * X * ((A' : Matrix (Fin 2) (Fin 2) K)ᵀ * A) := by rw [Matrix.mul_assoc]
      _ = A * X := by rw [hAA', Matrix.mul_one]
  obtain ⟨c, hc⟩ := Matrix.mem_range_scalar_of_commute_single
    (M := (A : Matrix (Fin 2) (Fin 2) K)) fun i j _ => hcomm _
  have hc1 : c = 1 := by
    have hdet := Matrix.SpecialLinearGroup.det_coe A
    rw [← hc, Matrix.scalar_apply, Matrix.det_diagonal, Fin.prod_univ_two] at hdet
    have h0 : (c + 1) * (c + 1) = 0 := by
      linear_combination hdet + (c + 1) * (CharTwo.two_eq_zero (R := K))
    have h1 : c + 1 = 0 := mul_self_eq_zero.mp h0
    have h2 := eq_neg_of_add_eq_zero_left h1
    rwa [CharTwo.neg_eq] at h2
  have hA : (A : Matrix (Fin 2) (Fin 2) K) = 1 := by rw [← hc, hc1, map_one]
  have hA' : (A' : Matrix (Fin 2) (Fin 2) K) = 1 := by
    rw [hA, Matrix.one_mul] at hAA
    rw [← Matrix.transpose_transpose (A' : Matrix (Fin 2) (Fin 2) K), hAA, Matrix.transpose_one]
  exact Prod.ext (Matrix.SpecialLinearGroup.ext _ _ fun i j => by rw [hA]; rfl)
    (Matrix.SpecialLinearGroup.ext _ _ fun i j => by rw [hA']; rfl)

end HypBlock

structure HypFrame (Q : QuadraticForm K (ι → K)) (m : ℕ) where
  X : Fin m ↪ ι
  Y : Fin m ↪ ι
  X_ne_Y : ∀ i j, X i ≠ Y j
  hyp : ∀ i, IsHypCoord Q (X i) (Y i)

namespace HypFrame

variable {Q : QuadraticForm K (ι → K)} {m : ℕ} (F : HypFrame Q m)

omit [Fintype ι] in
theorem Y_ne_X (i j : Fin m) : F.Y i ≠ F.X j := (F.X_ne_Y j i).symm

omit [Fintype ι] [DecidableEq ι] in
@[expose] def blockFun (i j : Fin m) (rs : Fin 2 × Fin 2) : ι :=
  ![![F.X i, F.X j], ![F.Y j, F.Y i]] rs.1 rs.2

omit [Fintype ι] in
theorem blockFun_injective {i j : Fin m} (hij : i ≠ j) :
    Function.Injective (F.blockFun i j) := by
  rintro ⟨r, s⟩ ⟨r', s'⟩ h
  fin_cases r <;> fin_cases s <;> fin_cases r' <;> fin_cases s' <;>
    simp_all [blockFun, F.X.injective.eq_iff, F.Y.injective.eq_iff, F.X_ne_Y, F.Y_ne_X,
      Ne.symm hij]

@[expose] def block {i j : Fin m} (hij : i ≠ j) : HypBlock Q where
  pos := ⟨F.blockFun i j, F.blockFun_injective hij⟩
  hyp₀ := F.hyp i
  hyp₁ := F.hyp j

omit [Fintype ι] in
theorem range_block {i j : Fin m} (hij : i ≠ j) :
    Set.range (F.block hij).pos = {F.X i, F.X j, F.Y i, F.Y j} := by
  ext k
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨r, s⟩, rfl⟩
    fin_cases r <;> fin_cases s <;> simp [block, blockFun]
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨(0, 0), rfl⟩
    · exact ⟨(0, 1), rfl⟩
    · exact ⟨(1, 1), rfl⟩
    · exact ⟨(1, 0), rfl⟩

end HypFrame

end OrthRestTail

end CFSG.StandardType
