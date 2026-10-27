module

public import CFSG.RankThree.Classical2.MatrixFrobeniusLang
public import CFSG.RankThree.Classical2.SLnSemilinearRigidity
public import CFSG.LieType.Chevalley.RankOneGaussian

public noncomputable section

namespace CFSG.RankThree.Chevalley

open Matrix CFSG.RankThree.Classical2 CFSG.LieType.Chevalley
open scoped MatrixGroups

section J

variable {Ω : Type} [Field Ω]

@[expose] def sl2J : Matrix (Fin 2) (Fin 2) Ω := !![0, 1; -1, 0]

@[expose] def sl2Jinv : Matrix (Fin 2) (Fin 2) Ω := !![0, -1; 1, 0]

theorem sl2J_mul_sl2Jinv : (sl2J : Matrix (Fin 2) (Fin 2) Ω) * sl2Jinv = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sl2J, sl2Jinv, Matrix.mul_apply, Fin.sum_univ_two]

theorem sl2Jinv_mul_sl2J : (sl2Jinv : Matrix (Fin 2) (Fin 2) Ω) * sl2J = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sl2J, sl2Jinv, Matrix.mul_apply, Fin.sum_univ_two]

theorem transpose_sl2J : (sl2J : Matrix (Fin 2) (Fin 2) Ω)ᵀ = sl2Jinv := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sl2J, sl2Jinv]

theorem transpose_sl2Jinv : (sl2Jinv : Matrix (Fin 2) (Fin 2) Ω)ᵀ = sl2J := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sl2J, sl2Jinv]

theorem det_sl2J : (sl2J : Matrix (Fin 2) (Fin 2) Ω).det = 1 := by
  simp [sl2J, Matrix.det_fin_two]

theorem sl2Jinv_mul_sl2Jinv : (sl2Jinv : Matrix (Fin 2) (Fin 2) Ω) * sl2Jinv = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sl2Jinv, Matrix.mul_apply, Fin.sum_univ_two]

theorem transpose_mul_sl2J_mul (B : Matrix (Fin 2) (Fin 2) Ω) :
    Bᵀ * sl2J * B = B.det • sl2J := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sl2J, Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two] <;> ring

end J

section Lang

variable {Ω : Type} [Field Ω]

theorem neg_one_pow_char_pow {ℓ : ℕ} [Fact ℓ.Prime] [CharP Ω ℓ] (d : ℕ) :
    (-1 : Ω) ^ (ℓ ^ d) = -1 := by
  have h := map_neg (iterateFrobenius Ω ℓ d) 1
  rwa [map_one, iterateFrobenius_def] at h

theorem map_sl2J {ℓ : ℕ} [Fact ℓ.Prime] [CharP Ω ℓ] (d : ℕ) :
    (sl2J : Matrix (Fin 2) (Fin 2) Ω).map (· ^ (ℓ ^ d)) = sl2J := by
  have h0 : (0 : Ω) ^ (ℓ ^ d) = 0 := zero_pow (pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sl2J, h0, neg_one_pow_char_pow]

theorem map_sl2Jinv {ℓ : ℕ} [Fact ℓ.Prime] [CharP Ω ℓ] (d : ℕ) :
    (sl2Jinv : Matrix (Fin 2) (Fin 2) Ω).map (· ^ (ℓ ^ d)) = sl2Jinv := by
  have h0 : (0 : Ω) ^ (ℓ ^ d) = 0 := zero_pow (pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sl2Jinv, h0, neg_one_pow_char_pow]

theorem coe_WSL_inv : ((WSL⁻¹ : SL(2, Ω)) : Matrix (Fin 2) (Fin 2) Ω) = sl2Jinv := by
  rw [Matrix.SpecialLinearGroup.coe_inv, coe_WSL, Matrix.adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sl2Jinv]

theorem WSL_mul_WSL_commute (B : SL(2, Ω)) : WSL * WSL * B = B * (WSL * WSL) := by
  have h : ((WSL * WSL : SL(2, Ω)) : Matrix (Fin 2) (Fin 2) Ω) = -1 := by
    rw [Matrix.SpecialLinearGroup.coe_mul, coe_WSL]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  refine Subtype.ext ?_
  rw [Matrix.SpecialLinearGroup.coe_mul (WSL * WSL) B, Matrix.SpecialLinearGroup.coe_mul B,
    h, Matrix.neg_mul, Matrix.mul_neg, Matrix.one_mul, Matrix.mul_one]

theorem exists_sl2_conj_unitary {ℓ d : ℕ} (hℓ : ℓ.Prime) (hd : 1 ≤ d) {k : Type} [Field k]
    [CharP k ℓ] (hk : Nat.card k = ℓ ^ d) [Algebra k Ω] [IsAlgClosure k Ω] :
    ∃ C : SL(2, Ω), ∀ A : SL(2, k),
      (((C * Matrix.SpecialLinearGroup.map (algebraMap k Ω) A * C⁻¹ : SL(2, Ω)) :
          Matrix (Fin 2) (Fin 2) Ω).map (· ^ (ℓ ^ d)))ᵀ *
        ((C * Matrix.SpecialLinearGroup.map (algebraMap k Ω) A * C⁻¹ : SL(2, Ω)) :
          Matrix (Fin 2) (Fin 2) Ω) = 1 ∧
      ∀ i j, ((C * Matrix.SpecialLinearGroup.map (algebraMap k Ω) A * C⁻¹ : SL(2, Ω)) :
          Matrix (Fin 2) (Fin 2) Ω) i j ^ (ℓ ^ d) ^ 2 =
        ((C * Matrix.SpecialLinearGroup.map (algebraMap k Ω) A * C⁻¹ : SL(2, Ω)) :
          Matrix (Fin 2) (Fin 2) Ω) i j := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : CharP Ω ℓ := charP_of_injective_algebraMap (algebraMap k Ω).injective ℓ
  have : Finite k := Nat.finite_of_card_ne_zero (by
    rw [hk]
    exact pow_ne_zero _ hℓ.ne_zero)
  have : Fintype k := Fintype.ofFinite k
  set φ : Ω →+* Ω := iterateFrobenius Ω ℓ d with hφ
  have hφapp : ∀ c : Ω, φ c = c ^ (ℓ ^ d) := fun c => by rw [hφ, iterateFrobenius_def]
  set F : SL(2, Ω) →* SL(2, Ω) := Matrix.SpecialLinearGroup.map φ with hF
  have hFcoe : ∀ M : SL(2, Ω), ((F M : SL(2, Ω)) : Matrix (Fin 2) (Fin 2) Ω) =
      (M : Matrix (Fin 2) (Fin 2) Ω).map (· ^ (ℓ ^ d)) := fun M => by
    ext i j
    simp [hF, Matrix.SpecialLinearGroup.map_apply_coe, hφapp]
  set Jg : GL (Fin 2) Ω := Matrix.SpecialLinearGroup.toGL (WSL : SL(2, Ω)) with hJg
  have hJgv : (Jg : Matrix (Fin 2) (Fin 2) Ω) = sl2J := rfl
  obtain ⟨-, hlang⟩ := matrix_frobenius_lang (K := k) (Ω := Ω) (n := 2) hℓ hd hk (by norm_num) Jg
  obtain ⟨H, hHdet, hH⟩ := hlang (by rw [hJgv, det_sl2J])
  rw [hJgv] at hH
  set H' : SL(2, Ω) := ⟨H, hHdet⟩ with hH'
  have e1 : ((H'⁻¹ : SL(2, Ω)) : Matrix (Fin 2) (Fin 2) Ω) = (↑H⁻¹ : Matrix (Fin 2) (Fin 2) Ω) := by
    rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.coe_units_inv, Matrix.inv_def,
      show ((H' : SL(2, Ω)) : Matrix (Fin 2) (Fin 2) Ω) = H from rfl, hHdet, Ring.inverse_one,
      one_smul]
  have hlangSL : WSL = H'⁻¹ * F H' := by
    refine Subtype.ext ?_
    rw [Matrix.SpecialLinearGroup.coe_mul, e1, hFcoe, coe_WSL, ← hH]
    rfl
  have hFH : F H' = H' * WSL := by rw [hlangSL, mul_inv_cancel_left]
  have hFC : F H'⁻¹ = WSL⁻¹ * H'⁻¹ := by rw [map_inv, hFH, _root_.mul_inv_rev]
  have h0 : (0 : Ω) ^ (ℓ ^ d) = 0 := zero_pow (pow_ne_zero _ hℓ.ne_zero)
  have hFW : F WSL = WSL := by
    refine Subtype.ext ?_
    rw [hFcoe, coe_WSL]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h0, neg_one_pow_char_pow]
  refine ⟨H'⁻¹, fun A => ?_⟩
  set A' : SL(2, Ω) := Matrix.SpecialLinearGroup.map (algebraMap k Ω) A with hA'
  have hFA : F A' = A' := by
    refine Subtype.ext ?_
    rw [hFcoe]
    ext i j
    rw [Matrix.map_apply, hA', Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
      Matrix.map_apply, ← map_pow, ← hk, Nat.card_eq_fintype_card, FiniteField.pow_card]
  set B : SL(2, Ω) := H'⁻¹ * A' * H'⁻¹⁻¹ with hB
  have hFB : F B = WSL⁻¹ * B * WSL := by
    rw [hB, inv_inv, map_mul, map_mul, hFC, hFH, hFA]
    group
  have hFFB : F (F B) = B := by
    rw [hFB, map_mul, map_mul, map_inv, hFW, hFB]
    have hc := WSL_mul_WSL_commute B
    calc WSL⁻¹ * (WSL⁻¹ * B * WSL) * WSL = (WSL * WSL)⁻¹ * (B * (WSL * WSL)) := by group
      _ = (WSL * WSL)⁻¹ * (WSL * WSL * B) := by rw [hc]
      _ = B := by group
  refine ⟨?_, fun i j => ?_⟩
  · rw [← hFcoe, hFB, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      coe_WSL_inv, coe_WSL, show (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) Ω) = sl2J from rfl,
      Matrix.transpose_mul, Matrix.transpose_mul, transpose_sl2Jinv, transpose_sl2J,
      Matrix.mul_assoc sl2Jinv, transpose_mul_sl2J_mul, B.2, one_smul, sl2Jinv_mul_sl2J]
  · have h := congrArg (fun M : SL(2, Ω) => (M : Matrix (Fin 2) (Fin 2) Ω) i j) hFFB
    simp only [hFcoe, Matrix.map_apply] at h
    rw [← pow_mul, ← sq] at h
    exact h

end Lang

section Emb

variable {Ω : Type} [Field Ω]

@[expose] def emb12Mat (B : Matrix (Fin 2) (Fin 2) Ω) : Matrix (Fin 3) (Fin 3) Ω :=
  !![B 0 0, B 0 1, 0; B 1 0, B 1 1, 0; 0, 0, 1]

@[expose] def emb23Mat (B : Matrix (Fin 2) (Fin 2) Ω) : Matrix (Fin 3) (Fin 3) Ω :=
  !![1, 0, 0; 0, B 0 0, B 0 1; 0, B 1 0, B 1 1]

theorem emb12Mat_mul (B C : Matrix (Fin 2) (Fin 2) Ω) :
    emb12Mat (B * C) = emb12Mat B * emb12Mat C := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [emb12Mat, Matrix.mul_apply, Fin.sum_univ_succ]

theorem emb23Mat_mul (B C : Matrix (Fin 2) (Fin 2) Ω) :
    emb23Mat (B * C) = emb23Mat B * emb23Mat C := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [emb23Mat, Matrix.mul_apply, Fin.sum_univ_succ]

theorem emb12Mat_one : emb12Mat (1 : Matrix (Fin 2) (Fin 2) Ω) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [emb12Mat]

theorem emb23Mat_one : emb23Mat (1 : Matrix (Fin 2) (Fin 2) Ω) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [emb23Mat]

theorem det_emb12Mat (B : Matrix (Fin 2) (Fin 2) Ω) : (emb12Mat B).det = B.det := by
  simp [emb12Mat, Matrix.det_fin_three, Matrix.det_fin_two]

theorem det_emb23Mat (B : Matrix (Fin 2) (Fin 2) Ω) : (emb23Mat B).det = B.det := by
  simp [emb23Mat, Matrix.det_fin_three, Matrix.det_fin_two]

theorem transpose_emb12Mat (B : Matrix (Fin 2) (Fin 2) Ω) : (emb12Mat B)ᵀ = emb12Mat Bᵀ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [emb12Mat]

theorem transpose_emb23Mat (B : Matrix (Fin 2) (Fin 2) Ω) : (emb23Mat B)ᵀ = emb23Mat Bᵀ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [emb23Mat]

theorem map_emb12Mat {f : Ω → Ω} (h0 : f 0 = 0) (h1 : f 1 = 1) (B : Matrix (Fin 2) (Fin 2) Ω) :
    (emb12Mat B).map f = emb12Mat (B.map f) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [emb12Mat, h0, h1]

theorem map_emb23Mat {f : Ω → Ω} (h0 : f 0 = 0) (h1 : f 1 = 1) (B : Matrix (Fin 2) (Fin 2) Ω) :
    (emb23Mat B).map f = emb23Mat (B.map f) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [emb23Mat, h0, h1]

@[expose] def sl3Emb₁₂ : SL(2, Ω) →* SL(3, Ω) where
  toFun B := ⟨emb12Mat B, by rw [det_emb12Mat, B.2]⟩
  map_one' := Subtype.ext emb12Mat_one
  map_mul' B C := Subtype.ext (emb12Mat_mul _ _)

@[expose] def sl3Emb₂₃ : SL(2, Ω) →* SL(3, Ω) where
  toFun B := ⟨emb23Mat B, by rw [det_emb23Mat, B.2]⟩
  map_one' := Subtype.ext emb23Mat_one
  map_mul' B C := Subtype.ext (emb23Mat_mul _ _)

theorem coe_sl3Emb₁₂ (B : SL(2, Ω)) :
    ((sl3Emb₁₂ B : SL(3, Ω)) : Matrix (Fin 3) (Fin 3) Ω) = emb12Mat B := rfl

theorem coe_sl3Emb₂₃ (B : SL(2, Ω)) :
    ((sl3Emb₂₃ B : SL(3, Ω)) : Matrix (Fin 3) (Fin 3) Ω) = emb23Mat B := rfl

theorem sl3Emb₁₂_uSL (t : Ω) :
    ((sl3Emb₁₂ (uSL t) : SL(3, Ω)) : Matrix (Fin 3) (Fin 3) Ω) = 1 + single 0 1 t := by
  rw [coe_sl3Emb₁₂, coe_uSL]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [emb12Mat]

theorem sl3Emb₁₂_vSL (t : Ω) :
    ((sl3Emb₁₂ (vSL t) : SL(3, Ω)) : Matrix (Fin 3) (Fin 3) Ω) = 1 + single 1 0 t := by
  rw [coe_sl3Emb₁₂, coe_vSL]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [emb12Mat]

theorem sl3Emb₂₃_uSL (t : Ω) :
    ((sl3Emb₂₃ (uSL t) : SL(3, Ω)) : Matrix (Fin 3) (Fin 3) Ω) = 1 + single 1 2 t := by
  rw [coe_sl3Emb₂₃, coe_uSL]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [emb23Mat]

theorem sl3Emb₂₃_vSL (t : Ω) :
    ((sl3Emb₂₃ (vSL t) : SL(3, Ω)) : Matrix (Fin 3) (Fin 3) Ω) = 1 + single 2 1 t := by
  rw [coe_sl3Emb₂₃, coe_vSL]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [emb23Mat]

theorem sl3Emb₁₂_mem_unitarySet {q : ℕ} (hq : 1 ≤ q) {B : SL(2, Ω)}
    (hU : ((B : Matrix (Fin 2) (Fin 2) Ω).map (· ^ q))ᵀ * (B : Matrix (Fin 2) (Fin 2) Ω) = 1)
    (hE : ∀ i j, (B : Matrix (Fin 2) (Fin 2) Ω) i j ^ q ^ 2 = (B : Matrix (Fin 2) (Fin 2) Ω) i j) :
    Matrix.SpecialLinearGroup.toGL (sl3Emb₁₂ B) ∈ unitarySet (Ω := Ω) q 3 := by
  have h0 : (0 : Ω) ^ q = 0 := zero_pow (by omega)
  have h0' : (0 : Ω) ^ q ^ 2 = 0 := zero_pow (by positivity)
  refine ⟨fun i j => ?_, (sl3Emb₁₂ B).2, ?_⟩
  · change (emb12Mat (B : Matrix (Fin 2) (Fin 2) Ω)) i j ^ q ^ 2 = emb12Mat _ i j
    fin_cases i <;> fin_cases j <;> simp [emb12Mat, hE, h0']
  · change ((emb12Mat (B : Matrix (Fin 2) (Fin 2) Ω)).map (· ^ q))ᵀ * emb12Mat _ = 1
    rw [map_emb12Mat (f := fun x : Ω => x ^ q) h0 (one_pow q), transpose_emb12Mat,
      ← emb12Mat_mul, hU, emb12Mat_one]

theorem sl3Emb₂₃_mem_unitarySet {q : ℕ} (hq : 1 ≤ q) {B : SL(2, Ω)}
    (hU : ((B : Matrix (Fin 2) (Fin 2) Ω).map (· ^ q))ᵀ * (B : Matrix (Fin 2) (Fin 2) Ω) = 1)
    (hE : ∀ i j, (B : Matrix (Fin 2) (Fin 2) Ω) i j ^ q ^ 2 = (B : Matrix (Fin 2) (Fin 2) Ω) i j) :
    Matrix.SpecialLinearGroup.toGL (sl3Emb₂₃ B) ∈ unitarySet (Ω := Ω) q 3 := by
  have h0 : (0 : Ω) ^ q = 0 := zero_pow (by omega)
  have h0' : (0 : Ω) ^ q ^ 2 = 0 := zero_pow (by positivity)
  refine ⟨fun i j => ?_, (sl3Emb₂₃ B).2, ?_⟩
  · change (emb23Mat (B : Matrix (Fin 2) (Fin 2) Ω)) i j ^ q ^ 2 = emb23Mat _ i j
    fin_cases i <;> fin_cases j <;> simp [emb23Mat, hE, h0']
  · change ((emb23Mat (B : Matrix (Fin 2) (Fin 2) Ω)).map (· ^ q))ᵀ * emb23Mat _ = 1
    rw [map_emb23Mat (f := fun x : Ω => x ^ q) h0 (one_pow q), transpose_emb23Mat,
      ← emb23Mat_mul, hU, emb23Mat_one]

end Emb

end CFSG.RankThree.Chevalley
