module

public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.GH74.Uniqueness.SU.SU5F4
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK429E

namespace U6

open CFSG.GH74.Uniqueness.SU.SU5 (F4c)
open CFSG.GH74.Uniqueness.SU.SU5.F4c (z0 z1 w w2)
open Matrix
open scoped Matrix

@[expose] def Uni {n : ℕ} (X : Matrix (Fin n) (Fin n) F4c) : Prop :=
  (X.map (fun c => c * c))ᵀ * X = 1

instance {n : ℕ} (X : Matrix (Fin n) (Fin n) F4c) : Decidable (Uni X) :=
  inferInstanceAs (Decidable (_ = _))

@[expose] def e0 : Fin 6 → F4c := ![z1, z0, z0, z0, z0, z0]

@[expose] def y7C : Matrix (Fin 6) (Fin 6) F4c :=
  !![w, w2, w, w2, z0, w2; z1, w2, w, w, z1, z0; z0, z1, z0, z0, w, z1; z1, z0, w, w, z1, w2;
    z1, w, w, z1, z0, w; w2, w, w, w, z0, w]

@[expose] def y7Ci : Matrix (Fin 6) (Fin 6) F4c :=
  !![w2, z1, z0, z1, z1, w; w, w, z1, z0, w2, w2; w2, w2, z0, w2, w2, w2; w, w2, z0, w2, z1, w2;
    z0, z1, w2, z1, z0, z0; w, z0, z1, w, w2, w2]

@[expose] def pw7 : Fin 6 → Matrix (Fin 6) (Fin 6) F4c :=
  ![1, y7C,
    !![z1, z0, w, z0, w2, z0; w, z1, w, z0, w, w; z0, w, w2, w, z1, z1; w2, w, w, z0, z1, w2;
      z0, w2, z0, z1, z0, z1; z0, w, w, z1, w2, w],
    !![z1, z0, w2, z0, w2, z0; z1, z0, z1, w, w, w2; w, w, z0, w2, z1, w; z0, w, z1, z1, z1, w2;
      z1, z0, z1, z1, w, z1; z1, z1, w2, z1, z0, w2],
    !![z1, z1, w2, z0, z1, z1; z0, z0, w2, w2, z0, z1; w, z1, z0, z1, z1, w; z0, w2, w, z1, z1, z1;
      w, w2, z1, z1, w2, z0; z0, w, w2, w, z1, w],
    !![z1, w2, z0, w, z0, z0; z0, z1, w2, w2, w, w2; w2, w2, w, w2, z0, w2; z0, z0, w2, z0, z1, z1;
      w, w2, z1, z1, z0, w; z0, w2, z1, w, z1, w2]]

theorem pw7_eq : ∀ j : Fin 6, pw7 j = y7C ^ (j : ℕ) := by decide +kernel

@[expose] def kr7 : Matrix (Fin 6) (Fin 6) F4c := Matrix.of fun i j => (pw7 j *ᵥ e0) i

@[expose] def kr7i : Matrix (Fin 6) (Fin 6) F4c :=
  !![z1, w, z0, w2, w2, z0; z0, z1, z0, w2, z0, z1; z0, w, z0, w2, z0, w; z0, w2, z0, w, z0, w;
    z0, w, z1, z1, w, w; z0, w2, z1, w, z1, z0]

theorem kr7i_mul_kr7 : kr7i * kr7 = 1 := by decide +kernel

@[expose] def Check7 (v : Fin 6 → F4c) : Prop :=
  Uni (∑ j, (kr7i *ᵥ v) j • pw7 j) → (∑ j, (kr7i *ᵥ v) j • pw7 j) ^ 3 = 1 →
    ∃ c : F4c, ∑ j, (kr7i *ᵥ v) j • pw7 j = Matrix.scalar (Fin 6) c

instance (v : Fin 6 → F4c) : Decidable (Check7 v) := by unfold Check7; infer_instance

theorem check7_z0 : ∀ v : Fin 5 → F4c, Check7 (Fin.cons z0 v) := by decide +kernel
theorem check7_z1 : ∀ v : Fin 5 → F4c, Check7 (Fin.cons z1 v) := by decide +kernel
theorem check7_w : ∀ v : Fin 5 → F4c, Check7 (Fin.cons w v) := by decide +kernel
theorem check7_w2 : ∀ v : Fin 5 → F4c, Check7 (Fin.cons w2 v) := by decide +kernel

theorem check7 (v : Fin 6 → F4c) : Check7 v := by
  have key : ∀ (c : F4c) (t : Fin 5 → F4c), Check7 (Fin.cons c t) := by
    intro c t
    cases c
    · exact check7_z0 t
    · exact check7_z1 t
    · exact check7_w t
    · exact check7_w2 t
  have h := key (v 0) (Fin.tail v)
  rwa [Fin.cons_self_tail] at h

theorem y7C_mul_y7Ci : y7C * y7Ci = 1 := by decide +kernel
theorem y7Ci_mul_y7C : y7Ci * y7C = 1 := by decide +kernel
theorem y7C_pow : y7C ^ 7 = 1 := by decide +kernel
theorem y7C_ne_one : y7C ≠ 1 := by decide +kernel
theorem y7C_uni : Uni y7C := by decide +kernel

@[expose] def y11C : Matrix (Fin 6) (Fin 6) F4c :=
  !![z1, w, w2, z0, w, w; z0, w2, z1, w2, z1, z1; z1, w, w2, z1, w, z0; z1, w2, z1, z1, z0, w;
    w, z0, w, z0, w, z0; w2, w, z0, z0, w2, z0]

@[expose] def y11Ci : Matrix (Fin 6) (Fin 6) F4c :=
  !![z1, z0, z1, z1, w2, w; w2, w, w2, w, z0, w2; w, z1, w, z1, w2, z0; z0, w, z1, z1, z0, z0;
    w2, z1, w2, z0, w2, w; w2, z1, z0, w2, z0, z0]

@[expose] def pw11 : Fin 6 → Matrix (Fin 6) (Fin 6) F4c :=
  ![1, y11C,
    !![z0, z1, z0, w, w2, z0; w2, z0, z1, z0, z0, w; z0, z1, z1, w2, w, w; z0, w, w, w, w, w2;
      w2, z0, w2, w, w2, w2; w, z0, z1, z1, w, w2],
    !![w2, w, w, z1, z0, w; w2, z0, z1, z1, w, z1; z0, z0, w, z1, z1, z0; z1, w, w, z1, z0, z1;
      z1, z0, w2, z1, w2, w; w2, w2, z0, z0, z0, z1],
    !![z1, w2, z0, w, z1, z1; w2, w, w2, z0, w2, w2; z1, z0, w, w2, z1, w; z1, z1, z1, w, z0, w;
      w2, w2, z1, w, w2, z0; z0, z1, z1, w, z1, w],
    !![w, w2, z0, z0, z0, w; w2, z0, w2, w, z1, w2; w2, z0, w2, z1, w, w2; w2, z1, w2, z0, z0, z0;
      z1, z0, z1, z1, z1, z1; z0, w2, w, z0, z0, w]]

theorem pw11_eq : ∀ j : Fin 6, pw11 j = y11C ^ (j : ℕ) := by decide +kernel

@[expose] def kr11 : Matrix (Fin 6) (Fin 6) F4c := Matrix.of fun i j => (pw11 j *ᵥ e0) i

@[expose] def kr11i : Matrix (Fin 6) (Fin 6) F4c :=
  !![z1, z0, w2, w2, w, w2; z0, w2, z0, z1, z1, w2; z0, z1, w, z0, w, w; z0, z0, z1, z1, z0, z0;
    z0, w2, w, z1, z0, z1; z0, z0, z1, z0, w, w2]

theorem kr11i_mul_kr11 : kr11i * kr11 = 1 := by decide +kernel

@[expose] def Check11 (v : Fin 6 → F4c) : Prop :=
  Uni (∑ j, (kr11i *ᵥ v) j • pw11 j) →
    (∃ c : F4c, (∑ j, (kr11i *ᵥ v) j • pw11 j) ^ 3 = Matrix.scalar (Fin 6) c) →
    (∀ c : F4c, ∑ j, (kr11i *ᵥ v) j • pw11 j ≠ Matrix.scalar (Fin 6) c) →
      (∑ j, (kr11i *ᵥ v) j • pw11 j).trace ≠ 0

instance (v : Fin 6 → F4c) : Decidable (Check11 v) := by unfold Check11; infer_instance

theorem check11_z0 : ∀ v : Fin 5 → F4c, Check11 (Fin.cons z0 v) := by decide +kernel
theorem check11_z1 : ∀ v : Fin 5 → F4c, Check11 (Fin.cons z1 v) := by decide +kernel
theorem check11_w : ∀ v : Fin 5 → F4c, Check11 (Fin.cons w v) := by decide +kernel
theorem check11_w2 : ∀ v : Fin 5 → F4c, Check11 (Fin.cons w2 v) := by decide +kernel

theorem check11 (v : Fin 6 → F4c) : Check11 v := by
  have key : ∀ (c : F4c) (t : Fin 5 → F4c), Check11 (Fin.cons c t) := by
    intro c t
    cases c
    · exact check11_z0 t
    · exact check11_z1 t
    · exact check11_w t
    · exact check11_w2 t
  have h := key (v 0) (Fin.tail v)
  rwa [Fin.cons_self_tail] at h

theorem y11C_mul_y11Ci : y11C * y11Ci = 1 := by decide +kernel
theorem y11Ci_mul_y11C : y11Ci * y11C = 1 := by decide +kernel
theorem y11C_pow : y11C ^ 11 = 1 := by decide +kernel
theorem y11C_ne_one : y11C ≠ 1 := by decide +kernel
theorem y11C_uni : Uni y11C := by decide +kernel

@[expose] def y5C : Matrix (Fin 6) (Fin 6) F4c :=
  !![w2, z0, w2, w, z0, z0; z1, z1, z1, z0, z0, z0; w2, w2, z0, w, z0, z0; z0, z1, z1, w2, z0, z0;
    z0, z0, z0, z0, z1, z0; z0, z0, z0, z0, z0, z1]

@[expose] def y5Ci : Matrix (Fin 6) (Fin 6) F4c :=
  !![w, z1, w, z0, z0, z0; z0, z1, w, z1, z0, z0; w, z1, z0, z1, z0, z0; w2, z0, w2, w, z0, z0;
    z0, z0, z0, z0, z1, z0; z0, z0, z0, z0, z0, z1]

theorem y5C_mul_y5Ci : y5C * y5Ci = 1 := by decide +kernel
theorem y5Ci_mul_y5C : y5Ci * y5C = 1 := by decide +kernel
theorem y5C_pow : y5C ^ 5 = 1 := by decide +kernel
theorem y5C_ne_one : y5C ≠ 1 := by decide +kernel
theorem y5C_uni : Uni y5C := by decide +kernel

@[expose] def Y4C : Matrix (Fin 4) (Fin 4) F4c :=
  !![w2, z0, w2, w; z1, z1, z1, z0; w2, w2, z0, w; z0, z1, z1, w2]

@[expose] def pw4 : Fin 4 → Matrix (Fin 4) (Fin 4) F4c :=
  ![1, Y4C, !![z0, z0, z0, z1; z1, w, w, z0; z1, z1, w2, z0; w, z1, w, z0],
    !![z0, z1, z1, w2; z0, w2, z1, z1; z0, w2, w, w2; z1, z0, z0, z0]]

theorem pw4_eq : ∀ j : Fin 4, pw4 j = Y4C ^ (j : ℕ) := by decide +kernel

@[expose] def e40 : Fin 4 → F4c := ![z1, z0, z0, z0]

@[expose] def kr4 : Matrix (Fin 4) (Fin 4) F4c := Matrix.of fun i j => (pw4 j *ᵥ e40) i

@[expose] def kr4i : Matrix (Fin 4) (Fin 4) F4c :=
  !![z1, w, w, z0; z0, w2, w2, z0; z0, w, w2, z0; z0, w2, z1, z1]

theorem kr4i_mul_kr4 : kr4i * kr4 = 1 := by decide +kernel

theorem check5a : ∀ v : Fin 4 → F4c, Uni (∑ j, (kr4i *ᵥ v) j • pw4 j) →
    (∃ c : F4c, (∑ j, (kr4i *ᵥ v) j • pw4 j) ^ 3 = Matrix.scalar (Fin 4) c) →
      (∑ j, (kr4i *ᵥ v) j • pw4 j) ^ 3 = 1 := by
  decide +kernel

theorem check5b : ∀ v : Fin 4 → F4c, Uni (∑ j, (kr4i *ᵥ v) j • pw4 j) →
    (∑ j, (kr4i *ᵥ v) j • pw4 j) ^ 3 = 1 →
      ∃ c : F4c, ∑ j, (kr4i *ᵥ v) j • pw4 j = Matrix.scalar (Fin 4) c := by
  decide +kernel

theorem check5c : ∀ v : Fin 4 → F4c, Uni (∑ j, (kr4i *ᵥ v) j • pw4 j) →
    (∑ j, (kr4i *ᵥ v) j • pw4 j) ^ 2 = 1 → ∑ j, (kr4i *ᵥ v) j • pw4 j = 1 := by
  decide +kernel

@[expose] def Check2 (M M' : Matrix (Fin 2) (Fin 2) F4c) : Prop :=
  Uni M → Uni M' → M ^ 3 = 1 → M' ^ 2 = 1 → M' ≠ 1 → M * M' = M' * M →
    ∃ e : F4c, M = Matrix.scalar (Fin 2) e

instance (M M' : Matrix (Fin 2) (Fin 2) F4c) : Decidable (Check2 M M') := by
  unfold Check2; infer_instance

theorem check2' : ∀ M M' : Fin 2 → Fin 2 → F4c, Check2 (Matrix.of M) (Matrix.of M') := by
  decide +kernel

theorem check2 (M M' : Matrix (Fin 2) (Fin 2) F4c) (hM : Uni M) (hM' : Uni M') (h3 : M ^ 3 = 1)
    (h2 : M' ^ 2 = 1) (h1 : M' ≠ 1) (hc : M * M' = M' * M) :
    ∃ e : F4c, M = Matrix.scalar (Fin 2) e :=
  check2' M M' hM hM' h3 h2 h1 hc

abbrev e6 : Fin 6 ≃ Fin 4 ⊕ Fin 2 := (finSumFinEquiv (m := 4) (n := 2)).symm

@[expose] def ext6 (P : Matrix (Fin 4) (Fin 4) F4c) (M : Matrix (Fin 2) (Fin 2) F4c) :
    Matrix (Fin 6) (Fin 6) F4c :=
  Matrix.reindex e6.symm e6.symm (fromBlocks P 0 0 M)

theorem ext6_mul (P P' : Matrix (Fin 4) (Fin 4) F4c) (M M' : Matrix (Fin 2) (Fin 2) F4c) :
    ext6 P M * ext6 P' M' = ext6 (P * P') (M * M') := by
  simp only [ext6, Matrix.reindex_apply, Matrix.submatrix_mul_equiv, fromBlocks_multiply,
    Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]

theorem ext6_one : ext6 1 1 = 1 := by
  simp only [ext6, fromBlocks_one, Matrix.reindex_apply, Matrix.submatrix_one_equiv]

theorem ext6_pow (P : Matrix (Fin 4) (Fin 4) F4c) (M : Matrix (Fin 2) (Fin 2) F4c) (n : ℕ) :
    ext6 P M ^ n = ext6 (P ^ n) (M ^ n) := by
  induction n with
  | zero => rw [pow_zero, pow_zero, pow_zero, ext6_one]
  | succ n ih => rw [pow_succ, ih, ext6_mul, ← pow_succ, ← pow_succ]

theorem ext6_injective {P P' : Matrix (Fin 4) (Fin 4) F4c} {M M' : Matrix (Fin 2) (Fin 2) F4c}
    (h : ext6 P M = ext6 P' M') : P = P' ∧ M = M' := by
  have h' : fromBlocks P 0 0 M = fromBlocks P' 0 0 M' :=
    (Matrix.reindex e6.symm e6.symm).injective h
  exact ⟨(Matrix.fromBlocks_inj.mp h').1, (Matrix.fromBlocks_inj.mp h').2.2.2⟩

theorem ext6_map_sq (P : Matrix (Fin 4) (Fin 4) F4c) (M : Matrix (Fin 2) (Fin 2) F4c) :
    (ext6 P M).map (fun c => c * c) = ext6 (P.map (fun c => c * c)) (M.map (fun c => c * c)) := by
  rw [ext6, ext6, Matrix.reindex_apply, Matrix.reindex_apply, ← Matrix.submatrix_map,
    Matrix.fromBlocks_map, Matrix.map_zero (fun c : F4c => c * c) (by decide),
    Matrix.map_zero (fun c : F4c => c * c) (by decide)]

theorem ext6_transpose (P : Matrix (Fin 4) (Fin 4) F4c) (M : Matrix (Fin 2) (Fin 2) F4c) :
    (ext6 P M)ᵀ = ext6 Pᵀ Mᵀ := by
  simp only [ext6, Matrix.reindex_apply, Matrix.transpose_submatrix, fromBlocks_transpose,
    Matrix.transpose_zero]

theorem uni_ext6 {P : Matrix (Fin 4) (Fin 4) F4c} {M : Matrix (Fin 2) (Fin 2) F4c}
    (h : Uni (ext6 P M)) : Uni P ∧ Uni M := by
  unfold Uni at h ⊢
  rw [ext6_map_sq, ext6_transpose, ext6_mul, ← ext6_one] at h
  exact ext6_injective h

theorem trace_ext6_scalar (a b : F4c) :
    (ext6 (Matrix.scalar (Fin 4) a) (Matrix.scalar (Fin 2) b)).trace = 0 := by
  revert a b
  decide +kernel

theorem scalar_ext6 (c : F4c) :
    Matrix.scalar (Fin 6) c = ext6 (Matrix.scalar (Fin 4) c) (Matrix.scalar (Fin 2) c) := by
  revert c
  decide +kernel

theorem y5C_eq : y5C = ext6 Y4C 1 := by decide +kernel

@[expose] def d6 : Fin 6 → F4c := ![z0, z0, z0, z0, z1, z1]

theorem diagonal_d6_eq : Matrix.diagonal d6 = ∑ i : Fin 5, y5C ^ (i : ℕ) := by decide +kernel

theorem d6_inl : ∀ i : Fin 4, d6 (e6.symm (Sum.inl i)) = 0 := by decide

theorem d6_inr : ∀ k : Fin 2, d6 (e6.symm (Sum.inr k)) = 1 := by decide

theorem eq_ext6_of_commute {X : Matrix (Fin 6) (Fin 6) F4c}
    (hX : X * Matrix.diagonal d6 = Matrix.diagonal d6 * X) :
    X = ext6 (Matrix.toBlocks₁₁ (Matrix.reindex e6 e6 X))
      (Matrix.toBlocks₂₂ (Matrix.reindex e6 e6 X)) := by
  have hij : ∀ i j, X i j * d6 j = d6 i * X i j := by
    intro i j
    have h := congrFun (congrFun hX i) j
    rwa [Matrix.mul_diagonal, Matrix.diagonal_mul] at h
  have h12 : Matrix.toBlocks₁₂ (Matrix.reindex e6 e6 X) = 0 := by
    ext i k
    simp only [Matrix.toBlocks₁₂, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.of_apply,
      Matrix.zero_apply]
    have h := hij (e6.symm (Sum.inl i)) (e6.symm (Sum.inr k))
    rw [d6_inl, d6_inr, mul_one, zero_mul] at h
    exact h
  have h21 : Matrix.toBlocks₂₁ (Matrix.reindex e6 e6 X) = 0 := by
    ext k i
    simp only [Matrix.toBlocks₂₁, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.of_apply,
      Matrix.zero_apply]
    have h := hij (e6.symm (Sum.inr k)) (e6.symm (Sum.inl i))
    rw [d6_inl, d6_inr, mul_zero, one_mul] at h
    exact h.symm
  have hb := Matrix.fromBlocks_toBlocks (Matrix.reindex e6 e6 X)
  rw [h12, h21] at hb
  rw [ext6, hb, Matrix.reindex_apply, Matrix.reindex_apply, Matrix.submatrix_submatrix]
  simp

theorem f4c_pow_five : ∀ c : F4c, c ^ 5 = 1 → c = 1 := by decide
theorem f4c_pow_seven : ∀ c : F4c, c ^ 7 = 1 → c = 1 := by decide
theorem f4c_pow_eleven : ∀ c : F4c, c ^ 11 = 1 → c = 1 := by decide

end U6

end CFSG.RankThree.PartTwo.Sec4.RonanK429E
