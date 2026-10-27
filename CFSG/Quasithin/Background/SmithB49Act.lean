module

public import CFSG.Quasithin.Background.SmithB51LnModel
public import CFSG.Quasithin.Background.JonesParshallSmallSL
public import CFSG.Quasithin.Background.SmithB49Bits

public section

namespace CFSG.Quasithin.B5.B49

open Matrix CFSG.Quasithin.JonesParshall CFSG.Assembly.LowTwoRank CFSG.Quasithin.B5.Ln
open scoped Kronecker

section Action

variable {n : ℕ}

@[expose] def matHom (n : ℕ) : ↥(StatedSL n (ZMod 2)) →* Matrix (Fin n) (Fin n) (ZMod 2) where
  toFun := mat
  map_one' := mat_one
  map_mul' := mat_mul

@[expose] def dmatHom (n : ℕ) : ↥(StatedSL n (ZMod 2)) →* Matrix (Fin n) (Fin n) (ZMod 2) where
  toFun := dmat
  map_one' := dmat_one
  map_mul' := dmat_mul

theorem matHom_apply (γ : ↥(StatedSL n (ZMod 2))) : matHom n γ = mat γ := rfl

theorem dmatHom_apply (γ : ↥(StatedSL n (ZMod 2))) : dmatHom n γ = dmat γ := rfl

@[expose] def krM (M : ↥(StatedSL n (ZMod 2)) →* Matrix (Fin n) (Fin n) (ZMod 2))
    (γ : ↥(StatedSL n (ZMod 2))) : Matrix (Fin n × Fin n) (Fin n × Fin n) (ZMod 2) :=
  (M γ⁻¹)ᵀ ⊗ₖ mat γ

theorem krM_one (M : ↥(StatedSL n (ZMod 2)) →* Matrix (Fin n) (Fin n) (ZMod 2)) :
    krM M 1 = 1 := by
  rw [krM, inv_one, map_one, transpose_one, mat_one, one_kronecker_one]

theorem krM_mul (M : ↥(StatedSL n (ZMod 2)) →* Matrix (Fin n) (Fin n) (ZMod 2))
    (γ δ : ↥(StatedSL n (ZMod 2))) : krM M (γ * δ) = krM M γ * krM M δ := by
  rw [krM, krM, krM, _root_.mul_inv_rev, map_mul, transpose_mul, mat_mul, mul_kronecker_mul]

@[expose] def muK (M : ↥(StatedSL n (ZMod 2)) →* Matrix (Fin n) (Fin n) (ZMod 2)) :
    ↥(StatedSL n (ZMod 2)) →* AddMonoid.End (Fin n × Fin n → ZMod 2) where
  toFun γ := AddMonoidHom.mk' (fun v => krM M γ *ᵥ v) (fun v w => mulVec_add _ v w)
  map_one' := AddMonoidHom.ext fun v => by
    show krM M 1 *ᵥ v = v
    rw [krM_one, one_mulVec]
  map_mul' γ δ := AddMonoidHom.ext fun v => by
    show krM M (γ * δ) *ᵥ v = krM M γ *ᵥ (krM M δ *ᵥ v)
    rw [krM_mul, mulVec_mulVec]

theorem muK_apply (M : ↥(StatedSL n (ZMod 2)) →* Matrix (Fin n) (Fin n) (ZMod 2))
    (γ : ↥(StatedSL n (ZMod 2))) (v : Fin n × Fin n → ZMod 2) :
    muK M γ v = krM M γ *ᵥ v := rfl

theorem muK_vec (M : ↥(StatedSL n (ZMod 2)) →* Matrix (Fin n) (Fin n) (ZMod 2))
    (γ : ↥(StatedSL n (ZMod 2))) (X : Matrix (Fin n) (Fin n) (ZMod 2)) :
    muK M γ X.vec = (mat γ * X * M γ⁻¹).vec := by
  rw [muK_apply, krM, kronecker_mulVec_vec, transpose_transpose]

theorem mat_inv_eq {γ : ↥(StatedSL n (ZMod 2))} {Y : Matrix (Fin n) (Fin n) (ZMod 2)}
    (h : mat γ * Y = 1) : mat γ⁻¹ = Y := by
  calc mat γ⁻¹ = mat γ⁻¹ * (mat γ * Y) := by rw [h, Matrix.mul_one]
    _ = Y := by rw [← Matrix.mul_assoc, mat_inv_mul, Matrix.one_mul]

theorem krM_mat_of {γ : ↥(StatedSL n (ZMod 2))} {Y : Matrix (Fin n) (Fin n) (ZMod 2)}
    (h : mat γ * Y = 1) : krM (matHom n) γ = Yᵀ ⊗ₖ mat γ := by
  rw [krM, matHom_apply, mat_inv_eq h]

theorem krM_dmat (γ : ↥(StatedSL n (ZMod 2))) : krM (dmatHom n) γ = mat γ ⊗ₖ mat γ := by
  rw [krM, dmatHom_apply, dmat, inv_inv, transpose_transpose]

end Action

section Words

@[expose] def wordEvalB {k : ℕ} (d : ℕ) (A : Fin k → List ℕ) : List (Fin k) → List ℕ
  | [] => bone d
  | i :: w => bmul d (A i) (wordEvalB d A w)

theorem decM_wordEvalB {n k : ℕ} (A : Fin k → List ℕ) (w : List (Fin k)) :
    decM (Equiv.refl (Fin n)) (wordEvalB n A w) =
      wordEvalM (fun i => decM (Equiv.refl (Fin n)) (A i)) w := by
  induction w with
  | nil => exact decM_bone _
  | cons i w ih =>
    show decM _ (bmul n (A i) (wordEvalB n A w)) = _ * _
    rw [decM_bmul, ih]

@[expose] def mats4B : Fin 2 → List ℕ := ![[3, 2, 4, 8], [8, 1, 2, 4]]

@[expose] def mats5B : Fin 2 → List ℕ := ![[3, 2, 4, 8, 16], [16, 1, 2, 4, 8]]

theorem decM_mats4B : (fun i => decM (Equiv.refl (Fin 4)) (mats4B i)) = mats4 := by
  funext i
  fin_cases i <;> decide +kernel

theorem decM_mats5B : (fun i => decM (Equiv.refl (Fin 5)) (mats5B i)) = mats5 := by
  funext i
  fin_cases i <;> decide +kernel

theorem wordEvalM_mats4 (w : List (Fin 2)) :
    wordEvalM mats4 w = decM (Equiv.refl (Fin 4)) (wordEvalB 4 mats4B w) := by
  rw [decM_wordEvalB, decM_mats4B]

theorem wordEvalM_mats5 (w : List (Fin 2)) :
    wordEvalM mats5 w = decM (Equiv.refl (Fin 5)) (wordEvalB 5 mats5B w) := by
  rw [decM_wordEvalB, decM_mats5B]

theorem tw4_bits : ∀ i j : Fin 4, i ≠ j →
    decM (Equiv.refl (Fin 4)) (wordEvalB 4 mats4B (tw4 i j)) = transvection i j 1 := by
  decide +kernel

theorem tw5_bits : ∀ i j : Fin 5, i ≠ j →
    decM (Equiv.refl (Fin 5)) (wordEvalB 5 mats5B (tw5 i j)) = transvection i j 1 := by
  decide +kernel

end Words

section Gens

@[expose] noncomputable def sgen4 (i : Fin 2) : ↥(StatedSL 4 (ZMod 2)) :=
  specialLinearGroupEquivStatedSL 4 (ZMod 2) (gens4 i)

@[expose] noncomputable def sgen5 (i : Fin 2) : ↥(StatedSL 5 (ZMod 2)) :=
  specialLinearGroupEquivStatedSL 5 (ZMod 2) (gens5 i)

theorem mat_sgen4 (i : Fin 2) : mat (sgen4 i) = mats4 i := by
  rw [← gens4_coe]
  rfl

theorem mat_sgen5 (i : Fin 2) : mat (sgen5 i) = mats5 i := by
  rw [← gens5_coe]
  rfl

theorem closure_map_equiv {n : ℕ} {gens : Fin 2 → SpecialLinearGroup (Fin n) (ZMod 2)}
    (h : Subgroup.closure (Set.range gens) = ⊤) :
    Subgroup.closure (Set.range fun i => specialLinearGroupEquivStatedSL n (ZMod 2) (gens i)) =
      ⊤ := by
  set φ := specialLinearGroupEquivStatedSL n (ZMod 2)
  have h1 : (Set.range fun i => φ (gens i)) = (φ : _ →* _) '' Set.range gens := by
    rw [← Set.range_comp]
    rfl
  rw [h1, ← MonoidHom.map_closure, h]
  exact Subgroup.map_top_of_surjective _ φ.surjective

theorem closure_sgen4 : Subgroup.closure (Set.range sgen4) = ⊤ :=
  closure_map_equiv (closure_range_eq_top (gens := gens4) (tw := tw4) (by
    rw [gens4_coe]
    intro i j hij
    rw [wordEvalM_mats4]
    exact tw4_bits i j hij))

theorem closure_sgen5 : Subgroup.closure (Set.range sgen5) = ⊤ :=
  closure_map_equiv (closure_range_eq_top (gens := gens5) (tw := tw5) (by
    rw [gens5_coe]
    intro i j hij
    rw [wordEvalM_mats5]
    exact tw5_bits i j hij))

theorem mat_wordEval {n : ℕ} (gens : Fin 2 → ↥(StatedSL n (ZMod 2))) (w : List (Fin 2)) :
    mat (wordEval gens w) = wordEvalM (fun i => mat (gens i)) w := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    show mat (gens i * wordEval gens w) = mat (gens i) * wordEvalM _ w
    rw [mat_mul, ih]

theorem mat_wordEval_sgen4 (w : List (Fin 2)) :
    mat (wordEval sgen4 w) = decM (Equiv.refl (Fin 4)) (wordEvalB 4 mats4B w) := by
  rw [mat_wordEval, ← wordEvalM_mats4]
  congr 1
  funext i
  exact mat_sgen4 i

theorem mat_wordEval_sgen5 (w : List (Fin 2)) :
    mat (wordEval sgen5 w) = decM (Equiv.refl (Fin 5)) (wordEvalB 5 mats5B w) := by
  rw [mat_wordEval, ← wordEvalM_mats5]
  congr 1
  funext i
  exact mat_sgen5 i

theorem wordEval_sgen4_eq_one {w : List (Fin 2)} (h : wordEvalB 4 mats4B w = bone 4) :
    wordEval sgen4 w = 1 := by
  apply mat_injective
  rw [mat_wordEval_sgen4, h, decM_bone, mat_one]

theorem wordEval_sgen5_eq_one {w : List (Fin 2)} (h : wordEvalB 5 mats5B w = bone 5) :
    wordEval sgen5 w = 1 := by
  apply mat_injective
  rw [mat_wordEval_sgen5, h, decM_bone, mat_one]

@[expose] def mats4inv : Fin 2 → Matrix (Fin 4) (Fin 4) (ZMod 2) := ![mats4 0, (mats4 1)ᵀ]

@[expose] def mats5inv : Fin 2 → Matrix (Fin 5) (Fin 5) (ZMod 2) := ![mats5 0, (mats5 1)ᵀ]

theorem mats4_mul_inv : ∀ i, mats4 i * mats4inv i = 1 := by decide +kernel

theorem mats5_mul_inv : ∀ i, mats5 i * mats5inv i = 1 := by decide +kernel

theorem krM_sgen4_mat (i : Fin 2) : krM (matHom 4) (sgen4 i) = (mats4inv i)ᵀ ⊗ₖ mats4 i := by
  rw [krM_mat_of (Y := mats4inv i) (by rw [mat_sgen4]; exact mats4_mul_inv i), mat_sgen4]

theorem krM_sgen5_mat (i : Fin 2) : krM (matHom 5) (sgen5 i) = (mats5inv i)ᵀ ⊗ₖ mats5 i := by
  rw [krM_mat_of (Y := mats5inv i) (by rw [mat_sgen5]; exact mats5_mul_inv i), mat_sgen5]

theorem krM_sgen4_dmat (i : Fin 2) : krM (dmatHom 4) (sgen4 i) = mats4 i ⊗ₖ mats4 i := by
  rw [krM_dmat, mat_sgen4]

theorem krM_sgen5_dmat (i : Fin 2) : krM (dmatHom 5) (sgen5 i) = mats5 i ⊗ₖ mats5 i := by
  rw [krM_dmat, mat_sgen5]

end Gens

section BitCert

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ℕ}

@[expose] def certL (d : ℕ) (A P F E : Fin 2 → List ℕ) (j l : Fin 2) : List ℕ :=
  badd (badd (if j = l then bone d else []) (bmul d (badd (A j) (bone d)) (P l)))
    (bmul d (F j) (E l))

@[expose] def certR {m : ℕ} (d : ℕ) (A : Fin 2 → List ℕ) (rels : Fin m → List (Fin 2))
    (C : Fin 2 → Fin m → List ℕ) (j l : Fin 2) : List ℕ :=
  bsum (fun r => bmul d (C j r) (foxDB d A (rels r) l)) (List.finRange m)

theorem cert_of_bits {m : ℕ} (e : ι ≃ Fin d) (A P F E : Fin 2 → List ℕ)
    (rels : Fin m → List (Fin 2)) (C : Fin 2 → Fin m → List ℕ)
    (h : ∀ j l, certL d A P F E j l = certR d A rels C j l) (j l : Fin 2) :
    (if j = l then 1 else 0) + (decM e (A j) + 1) * decM e (P l) +
        decM e (F j) * decM e (E l) =
      ∑ r, decM e (C j r) * foxD (fun i => decM e (A i)) (rels r) l := by
  have h1 := congrArg (decM e) (h j l)
  rw [certL, certR, decM_badd, decM_badd, decM_bmul, decM_bmul, decM_badd, decM_bone,
    decM_bsum_finRange] at h1
  simp only [decM_bmul, decM_foxDB] at h1
  rw [← h1]
  congr 2
  by_cases hjl : j = l
  · rw [ite_eq_left hjl, ite_eq_left hjl, decM_bone]
  · rw [ite_eq_right hjl, ite_eq_right hjl, decM_nil]

end BitCert

end CFSG.Quasithin.B5.B49
