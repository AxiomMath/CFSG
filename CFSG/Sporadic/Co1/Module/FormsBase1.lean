
module

public import CFSG.Sporadic.Co1.Module.FormsBase

public import CFSG.Sporadic.Co1.Module.OrbitsBase
public import CFSG.Sporadic.Co1.Module.FormsInputs
public import Certificates.Certificate10069
public meta import CFSG.Sporadic.Co1.Module.OrbitsBase
public meta import Certificates.Data.CFSGNative.Co1.Data
public import Certificates.Certificate10069Base

@[expose] public section

namespace CFSG.Sporadic.Co1.Module

open CFSG.Blueprint CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native Matrix

theorem forms_data :
    mulRows 24 (mulRows 24 (transposeRows 24 dat.rowsA) f0Rows) dat.rowsA = f0Rows ∧
    mulRows 24 (mulRows 24 (transposeRows 24 dat.rowsB) f0Rows) dat.rowsB = f0Rows ∧
    mulRows 24 f0Rows f0InvRows = idRows 24 ∧ mulRows 24 f0InvRows f0Rows = idRows 24 ∧
    (∀ i < 24, ((mulRows 24 (mulRows 24 (transposeRows 24 dat.rowsA) qRows)
      dat.rowsA)[i]?.getD 0).testBit i = ((qRows[i]?.getD 0).testBit i)) ∧
    (∀ i < 24, ((mulRows 24 (mulRows 24 (transposeRows 24 dat.rowsB) qRows)
      dat.rowsB)[i]?.getD 0).testBit i = ((qRows[i]?.getD 0).testBit i)) ∧
    vecMulN 24 (transposeRows 24 (wordRows stabWord₁)) 2 = 2 ∧
    vecMulN 24 (transposeRows 24 (wordRows stabWord₂)) 2 = 2 ∧
    addRows (mulRows 24 certC1 (addRows (wordRows stabWord₁) (idRows 24)))
      (mulRows 24 certC2 (addRows (wordRows stabWord₂) (idRows 24))) = projRows ∧
    addRows (mulRows 24 (addRows (wordRows stabWord₁) (idRows 24)) certD1)
      (mulRows 24 (addRows (wordRows stabWord₂) (idRows 24)) certD2) = lamRows ∧
    toVecD 24 (vecMulN 24 dat.rowsA 10379264) ≠ toVecD 24 10379264 ∧
    (qRows[1]?.getD 0).testBit 1 = false ∧ (qRows[12]?.getD 0).testBit 12 = true ∧
    (qRows[0]?.getD 0).testBit 0 = false ∧
    f0Rows = #[8388608, 10379264, 4321280, 1679360, 4710400, 81920, 11182080, 13221888, 16683008,
      9777152, 8183808, 11567104, 975620, 3397214, 11318454, 15105500, 6169276, 16363858,
      14276370, 3626442, 3092234, 14347584, 2590100, 2542531] :=
  Certificates.certificate10069

theorem F₀_invariant_A : matAᵀ * F₀ * matA = F₀ := by
  have h := congrArg (rowsMatrix 24) forms_data.1
  simpa only [rowsMatrix_mulRows, rowsMatrix_transposeRows, rowsMatrix_f0Rows, matA] using h

theorem F₀_invariant_B : matBᵀ * F₀ * matB = F₀ := by
  have h := congrArg (rowsMatrix 24) forms_data.2.1
  simpa only [rowsMatrix_mulRows, rowsMatrix_transposeRows, rowsMatrix_f0Rows, matB] using h

theorem F₀_mul_inv : F₀ * F₀inv = 1 := by
  have h := congrArg (rowsMatrix 24) forms_data.2.2.1
  simpa only [rowsMatrix_mulRows, rowsMatrix_idRows, rowsMatrix_f0Rows, F₀inv] using h

theorem F₀inv_mul : F₀inv * F₀ = 1 := by
  have h := congrArg (rowsMatrix 24) forms_data.2.2.2.1
  simpa only [rowsMatrix_mulRows, rowsMatrix_idRows, rowsMatrix_f0Rows, F₀inv] using h

theorem wordMat₁_mulVec : wordMat stabWord₁ *ᵥ v₂ = v₂ := by
  rw [← rowsMatrix_wordRows, ← toVecD_v₂, rowsMatrix_mulVec, forms_data.2.2.2.2.2.2.1]

theorem wordMat₂_mulVec : wordMat stabWord₂ *ᵥ v₂ = v₂ := by
  rw [← rowsMatrix_wordRows, ← toVecD_v₂, rowsMatrix_mulVec, forms_data.2.2.2.2.2.2.2.1]

theorem cert_C : rowsMatrix 24 certC1 * (wordMat stabWord₁ + 1) +
    rowsMatrix 24 certC2 * (wordMat stabWord₂ + 1) = rowsMatrix 24 projRows := by
  have h := congrArg (rowsMatrix 24) forms_data.2.2.2.2.2.2.2.2.1
  simpa only [rowsMatrix_addRows, rowsMatrix_mulRows, rowsMatrix_idRows, rowsMatrix_wordRows]
    using h

theorem cert_D : (wordMat stabWord₁ + 1) * rowsMatrix 24 certD1 +
    (wordMat stabWord₂ + 1) * rowsMatrix 24 certD2 = rowsMatrix 24 lamRows := by
  have h := congrArg (rowsMatrix 24) forms_data.2.2.2.2.2.2.2.2.2.1
  simpa only [rowsMatrix_addRows, rowsMatrix_mulRows, rowsMatrix_idRows, rowsMatrix_wordRows]
    using h

theorem fixed_col {u : Vec24} (h1 : wordMat stabWord₁ *ᵥ u = u)
    (h2 : wordMat stabWord₂ *ᵥ u = u) : u = u 1 • v₂ := by
  have hz : ∀ M : Matrix (Fin 24) (Fin 24) (ZMod 2), M *ᵥ u = u → (M + 1) *ᵥ u = 0 := by
    intro M hM
    rw [Matrix.add_mulVec, hM, Matrix.one_mulVec]
    exact vec_add_self u
  have key : rowsMatrix 24 projRows *ᵥ u = 0 := by
    rw [← cert_C, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hz _ h1,
      hz _ h2, Matrix.mulVec_zero, Matrix.mulVec_zero, add_zero]
  rw [projRows_mulVec] at key
  funext i
  by_cases hi : i = 1
  · subst hi
    simp [v₂]
  · have := congrFun key i
    simp only [hi, ↓reduceIte, Pi.zero_apply] at this
    simp [v₂, hi, this]

theorem fixed_row {y : Vec24} (h1 : y ᵥ* wordMat stabWord₁ = y)
    (h2 : y ᵥ* wordMat stabWord₂ = y) : y = y 13 • toVecD 24 10379264 := by
  have hz : ∀ M : Matrix (Fin 24) (Fin 24) (ZMod 2), y ᵥ* M = y → y ᵥ* (M + 1) = 0 := by
    intro M hM
    rw [Matrix.vecMul_add, hM, Matrix.vecMul_one]
    exact vec_add_self y
  have key : y ᵥ* rowsMatrix 24 lamRows = 0 := by
    rw [← cert_D, Matrix.vecMul_add, ← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul, hz _ h1,
      hz _ h2, Matrix.zero_vecMul, Matrix.zero_vecMul, add_zero]
  rw [lamRows_vecMul] at key
  funext k
  have := congrFun key k
  simp only [Pi.zero_apply] at this
  rw [Pi.smul_apply, smul_eq_mul]
  have h3 : y k = - (y 13 * toVecD 24 10379264 k) := eq_neg_of_add_eq_zero_left this
  rw [h3]
  exact CharTwo.neg_eq _

section Generic

variable {D : VecData} (hD : BaseFacts D)
include hD

end Generic

theorem lamVec_not_invariant :
    toVecD 24 10379264 ᵥ* matA ≠ toVecD 24 10379264 := by
  intro h
  apply forms_data.2.2.2.2.2.2.2.2.2.2.1
  rw [toVecD_vecMulN]
  exact h

theorem invariant_additive_zero
    {r : Vec24 → ZMod 2} (hadd : ∀ u v, r (u + v) = r u + r v)
    (hA : ∀ v, r (matA *ᵥ v) = r v) (hB : ∀ v, r (matB *ᵥ v) = r v) : r = 0 := by
  set y : Vec24 := fun i => r (Pi.single i 1) with hy
  have hyM : ∀ M : Matrix (Fin 24) (Fin 24) (ZMod 2), (∀ v, r (M *ᵥ v) = r v) → y ᵥ* M = y := by
    intro M hM
    funext i
    have h := additive_expand hadd (M *ᵥ Pi.single i 1)
    rw [hM] at h
    rw [Matrix.vecMul, dotProduct]
    simp only [hy] at h ⊢
    rw [h]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [mul_comm]
  have hyA : y ᵥ* matA = y := hyM _ hA
  have hyB : y ᵥ* matB = y := hyM _ hB
  have hfix := fixed_row (y := y) (vecMul_wordMat hyA hyB stabWord₁)
    (vecMul_wordMat hyA hyB stabWord₂)
  rcases zmod2_cases (y 13) with h13 | h13
  · have hy0 : y = 0 := by rw [hfix, h13, zero_smul]
    funext v
    rw [additive_expand hadd v]
    refine Finset.sum_eq_zero fun j _ => ?_
    have : r (Pi.single j 1) = 0 := congrFun hy0 j
    rw [this, mul_zero]
  · exfalso
    rw [h13, one_smul] at hfix
    apply lamVec_not_invariant
    rw [← hfix]
    exact hyA

theorem diag_A (i : Fin 24) : (matAᵀ * Qm * matA) i i = Qm i i := by
  have hX : rowsMatrix 24 (mulRows 24 (mulRows 24 (transposeRows 24 dat.rowsA) qRows)
      dat.rowsA) = matAᵀ * Qm * matA := by
    rw [rowsMatrix_mulRows, rowsMatrix_mulRows, rowsMatrix_transposeRows]
    rfl
  rw [← hX, rowsMatrix_apply]
  have h := forms_data.2.2.2.2.1 i.val i.isLt
  show toVecD 24 _ i = toVecD 24 (qRows[i.val]?.getD 0) i
  simp only [toVecD_apply, h]

theorem diag_B (i : Fin 24) : (matBᵀ * Qm * matB) i i = Qm i i := by
  have hX : rowsMatrix 24 (mulRows 24 (mulRows 24 (transposeRows 24 dat.rowsB) qRows)
      dat.rowsB) = matBᵀ * Qm * matB := by
    rw [rowsMatrix_mulRows, rowsMatrix_mulRows, rowsMatrix_transposeRows]
    rfl
  rw [← hX, rowsMatrix_apply]
  have h := forms_data.2.2.2.2.2.1 i.val i.isLt
  show toVecD 24 _ i = toVecD 24 (qRows[i.val]?.getD 0) i
  simp only [toVecD_apply, h]

theorem q₀_invariant_A (v : Vec24) : q₀ (matA *ᵥ v) = q₀ v :=
  q₀_invariant_gen F₀_invariant_A diag_A v

theorem q₀_invariant_B (v : Vec24) : q₀ (matB *ᵥ v) = q₀ v :=
  q₀_invariant_gen F₀_invariant_B diag_B v

section Generic

variable {D : VecData} (hD : BaseFacts D)
include hD

end Generic

theorem q₀_smul
    (g : Jmat) (v : Vec24) : q₀ (g • v) = q₀ v :=
  invariant_Jmat q₀_invariant_A q₀_invariant_B g v

theorem q₀_v₂ : q₀ v₂ = 0 := by
  rw [v₂, q₀_single]
  have h := forms_data.2.2.2.2.2.2.2.2.2.2.2.1
  simp [Qm, rowsMatrix_apply, toVecD_apply, h]

theorem q₀_v₃ : q₀ v₃ = 1 := by
  rw [v₃, q₀_single]
  have h := forms_data.2.2.2.2.2.2.2.2.2.2.2.2.1
  simp [Qm, rowsMatrix_apply, toVecD_apply, h]

theorem q₀_v₄ : q₀ v₄ = 0 := by
  rw [v₄, q₀_single]
  have h := forms_data.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  simp [Qm, rowsMatrix_apply, toVecD_apply, h]

theorem q₀_co1Act
    (g : NativeSporadic.Co1) (v : Vec24) : q₀ (co1Act g v) = q₀ v := by
  obtain ⟨h, hh⟩ := exists_mem_Jmat g
  have := q₀_smul h v
  rwa [smul_eq_mulVec, hh] at this

theorem F₀_isUnit : IsUnit F₀ := by
  refine (Matrix.isUnit_iff_isUnit_det F₀).2 ?_
  have h := congrArg Matrix.det F₀_mul_inv
  rw [Matrix.det_mul, Matrix.det_one] at h
  exact IsUnit.of_mul_eq_one _ h

theorem F₀_ne_zero : F₀ ≠ 0 := by
  intro h
  have := F₀_mul_inv
  rw [h, Matrix.zero_mul] at this
  exact zero_ne_one this

theorem F₀_eq_rows :
    F₀ = rowsMatrix 24 #[8388608, 10379264, 4321280, 1679360, 4710400, 81920,
    11182080, 13221888, 16683008, 9777152, 8183808, 11567104, 975620, 3397214, 11318454, 15105500,
    6169276, 16363858, 14276370, 3626442, 3092234, 14347584, 2590100, 2542531] := by
  rw [← forms_data.2.2.2.2.2.2.2.2.2.2.2.2.2.2, rowsMatrix_f0Rows]

theorem q₀_ne_zero : q₀ ≠ 0 := by
  intro h
  have := q₀_v₃
  rw [h] at this
  exact zero_ne_one this

end CFSG.Sporadic.Co1.Module
