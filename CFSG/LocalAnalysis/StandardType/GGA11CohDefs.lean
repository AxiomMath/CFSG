module

public import CFSG.LocalAnalysis.StandardType.GGA11Defs

public section

open CFSG CFSG.Assembly CFSG.StandardType Matrix CFSG.LieType.Universal
  CFSG.LieType.Universal.SpecialLinear

namespace CFSG.StandardType.A11

@[expose] noncomputable def Xe {G : Type} [Group G] (φ₃ : SL 9 →* G) (n : Fin 4 → G) (l : Fin 4) (a b : Fin 12) : G :=
  n l * φ₃ (tvAt l a b) * (n l)⁻¹

@[expose] def Ovl {G : Type} [Group G] (φ₃ : SL 9 →* G) (n : Fin 4 → G) (l m : Fin 4) : Subgroup G :=
  Subgroup.closure {g | ∃ a b : Fin 12, a ≠ b ∧ blk a ≠ l ∧ blk b ≠ l ∧ blk a ≠ m ∧ blk b ≠ m ∧
    g = Xe φ₃ n l a b}

@[expose] def OvlTorus {G : Type} [Group G] (f : Fin 4 → G) (l m : Fin 4) : Subgroup G :=
  Subgroup.closure {g | ∃ k, k ≠ l ∧ k ≠ m ∧ g = f k}

@[expose] noncomputable def Wsub (s : Fin 3) : Subgroup (SL 9) :=
  Subgroup.closure {g | ∃ a b : Fin 12, a ≠ b ∧ a.val < 9 ∧ b.val < 9 ∧ blk a ≠ s.castSucc ∧
    blk b ≠ s.castSucc ∧ g = tv9 a b}

@[expose] def A11WsubInput : Prop :=
  ∀ s : Fin 3, IsComponentOf (Wsub s) (Subgroup.centralizer ({T9 s} : Set (SL 9))) ∧
    Subgroup.center ↥(Wsub s) = ⊥ ∧ ∀ i : Fin 3, i ≠ s → T9 i ∈ Wsub s

@[expose] noncomputable def T6mat (b : Fin 2) : Matrix (Fin 6) (Fin 6) F2 :=
  Matrix.of fun a c =>
    if a.val / 3 = b.val ∧ c.val / 3 = b.val
    then Om ⟨a.val % 3, Nat.mod_lt _ (by norm_num)⟩ ⟨c.val % 3, Nat.mod_lt _ (by norm_num)⟩
    else if a = c then 1 else 0

private def a11t6_sig : Fin 6 ≃ Fin 3 ⊕ Fin 3 := (finSumFinEquiv (m := 3) (n := 3)).symm

@[simp] private lemma a11t6_sig_zero : a11t6_sig (0 : Fin 6) = Sum.inl (0 : Fin 3) := by decide

@[simp] private lemma a11t6_sig_one : a11t6_sig (1 : Fin 6) = Sum.inl (1 : Fin 3) := by decide

@[simp] private lemma a11t6_sig_two : a11t6_sig (2 : Fin 6) = Sum.inl (2 : Fin 3) := by decide

@[simp] private lemma a11t6_sig_three : a11t6_sig (3 : Fin 6) = Sum.inr (0 : Fin 3) := by decide

@[simp] private lemma a11t6_sig_four : a11t6_sig (4 : Fin 6) = Sum.inr (1 : Fin 3) := by decide

@[simp] private lemma a11t6_sig_five : a11t6_sig (5 : Fin 6) = Sum.inr (2 : Fin 3) := by decide

private lemma a11t6_det_Om : Om.det = 1 := by
  rw [Matrix.det_fin_three]
  simp [Om]

private lemma a11t6_T6mat_zero : T6mat 0 =
    (Matrix.fromBlocks Om (0 : Matrix (Fin 3) (Fin 3) F2) 0 1).submatrix a11t6_sig a11t6_sig := by
  ext a c
  fin_cases a <;> fin_cases c <;> simp [T6mat, Matrix.submatrix, Matrix.fromBlocks, Om]

private lemma a11t6_T6mat_one : T6mat 1 =
    (Matrix.fromBlocks (1 : Matrix (Fin 3) (Fin 3) F2) 0 0 Om).submatrix a11t6_sig a11t6_sig := by
  ext a c
  fin_cases a <;> fin_cases c <;> simp [T6mat, Matrix.submatrix, Matrix.fromBlocks, Om]

theorem T6mat_det (b : Fin 2) : (T6mat b).det = 1 := by
  fin_cases b
  · change (T6mat 0).det = 1
    rw [a11t6_T6mat_zero, Matrix.det_submatrix_equiv_self a11t6_sig, Matrix.det_fromBlocks_zero₂₁,
      Matrix.det_one, mul_one, a11t6_det_Om]
  · change (T6mat 1).det = 1
    rw [a11t6_T6mat_one, Matrix.det_submatrix_equiv_self a11t6_sig, Matrix.det_fromBlocks_zero₂₁,
      a11t6_det_Om, Matrix.det_one, mul_one]

@[expose] noncomputable def T6 (b : Fin 2) : SL 6 := ⟨T6mat b, T6mat_det b⟩

end CFSG.StandardType.A11

end
