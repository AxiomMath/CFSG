module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsAlt IsSp4)
open CFSG.Open (StatedSp StatedProj StatedScalars)

private lemma w183b5_permMatrix_conj {ι K : Type*} [Fintype ι] [DecidableEq ι] [Semiring K]
    (J : Matrix ι ι K) (σ : Equiv.Perm ι) :
    σ.permMatrix K * J * (σ⁻¹).permMatrix K = J.submatrix σ σ := by
  rw [Matrix.mul_assoc]
  change σ.toPEquiv.toMatrix * (J * (σ⁻¹).toPEquiv.toMatrix) = J.submatrix σ σ
  rw [PEquiv.mul_toMatrix_toPEquiv, PEquiv.toMatrix_toPEquiv_mul]
  ext i j
  simp only [Matrix.submatrix_apply]
  rw [show (σ⁻¹).symm = σ from rfl]
  simp

private lemma w183b5_permMatrix_conj_apply {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]
    (J : Matrix ι ι K) (σ : Equiv.Perm ι) (a b : ι) :
    (σ.permMatrix K * J * (σ⁻¹).permMatrix K) a b = J (σ a) (σ b) := by
  rw [w183b5_permMatrix_conj, Matrix.submatrix_apply]

private lemma w183b5_permMatrix_pow {ι K : Type*} [Semiring K] [Fintype ι] [DecidableEq ι]
    (σ : Equiv.Perm ι) (n : ℕ) :
    (σ.permMatrix K) ^ n = (σ ^ n).permMatrix K := by
  induction n with
  | zero => simp
  | succ n ih =>
      conv_lhs => rw [pow_succ]
      rw [ih, pow_succ', Matrix.permMatrix_mul]

theorem exists_orderOf_four_of_isAlt_six_or_isSp4 {X : Type} [Group X]
    (hX : IsAlt X 6 ∨ IsSp4 X 2) : ∃ x : X, orderOf x = 4 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases hX with hAlt | hSp
  · obtain ⟨e⟩ := hAlt
    let c : Equiv.Perm (Fin 6) := List.formPerm [0, 1, 2, 3] * List.formPerm [4, 5]
    have hc_mem : c ∈ alternatingGroup (Fin 6) := by
      rw [Equiv.Perm.mem_alternatingGroup]
      decide
    have hc4 : c ^ 4 = 1 := by decide
    have hc2 : c ^ 2 ≠ 1 := by decide
    have hord : orderOf c = 4 := by
      have hnot : ¬ c ^ 2 ^ 1 = 1 := by
        have : (2 : ℕ) ^ 1 = 2 := by norm_num
        rwa [this]
      have hfin : c ^ 2 ^ (1 + 1) = 1 := by
        have : (2 : ℕ) ^ (1 + 1) = 4 := by norm_num
        rwa [this]
      have h := orderOf_eq_prime_pow hnot hfin
      have : (2 : ℕ) ^ (1 + 1) = 4 := by norm_num
      rwa [this] at h
    refine ⟨e.symm ⟨c, hc_mem⟩, ?_⟩
    rw [MulEquiv.orderOf_eq]
    rw [← Subgroup.orderOf_coe]
    exact hord
  · obtain ⟨-, K, hKfield, hKfinite, hKcard, ⟨e⟩⟩ :=
      CFSG.Blueprint.LieModel.statedClassicalModel hSp (by decide)
    letI : Field K := hKfield
    letI : Finite K := hKfinite
    haveI : Fintype K := Fintype.ofFinite K
    haveI : CharP K 2 :=
      charP_of_card_eq_prime_pow (f := 2) (by rw [← Nat.card_eq_fintype_card]; exact hKcard)
    let J : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K := Matrix.fromBlocks 0 1 (-1) 0
    let σ : Equiv.Perm (Fin 2 ⊕ Fin 2) :=
      List.formPerm [Sum.inl 0, Sum.inl 1, Sum.inr 0, Sum.inr 1]
    let M : GL (Fin 2 ⊕ Fin 2) K :=
      (Matrix.permMatrixHom (n := Fin 2 ⊕ Fin 2) (R := K)).toHomUnits σ
    have hMcoe : (M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = (σ⁻¹).permMatrix K := rfl
    have hσ4 : σ ^ 4 = 1 := by decide
    have hσ_inl0 : σ (Sum.inl 0) = Sum.inl 1 := by decide
    have hσ_inl1 : σ (Sum.inl 1) = Sum.inr 0 := by decide
    have hσ_inr0 : σ (Sum.inr 0) = Sum.inr 1 := by decide
    have hσ_inr1 : σ (Sum.inr 1) = Sum.inl 0 := by decide
    have hsig2 : (σ ^ 2) (Sum.inl 0) = Sum.inr 0 := by
      change σ (σ (Sum.inl 0)) = Sum.inr 0
      rw [hσ_inl0, hσ_inl1]
    have hinvsq : (σ ^ 2)⁻¹ = σ ^ 2 := by
      rw [inv_eq_iff_mul_eq_one, ← pow_add, show (2 : ℕ) + 2 = 4 by norm_num, hσ4]
    have hσJ : ∀ a b : Fin 2 ⊕ Fin 2, J (σ a) (σ b) = J a b := by
      intro a b
      rcases a with i | i <;> fin_cases i <;> rcases b with j | j <;> fin_cases j <;>
        simp [hσ_inl0, hσ_inl1, hσ_inr0, hσ_inr1, J, Matrix.fromBlocks_apply₁₁,
          Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
          CharTwo.neg_eq]
    have hM_mem : M ∈ StatedSp 2 K := by
      rw [CFSG.Open.StatedAPI.mem_statedSp_iff]
      ext a b
      rw [hMcoe, Matrix.transpose_permMatrix, inv_inv, w183b5_permMatrix_conj_apply]
      exact hσJ a b
    have hM4 : M ^ 4 = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, Units.val_one, hMcoe, w183b5_permMatrix_pow]
      have hinv4 : ((σ⁻¹ : Equiv.Perm (Fin 2 ⊕ Fin 2)) ^ 4) = 1 := by
        rw [inv_pow, hσ4, inv_one]
      rw [hinv4, Matrix.permMatrix_one]
    have hentry : ((M ^ 2 : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)
        (Sum.inl 0) (Sum.inr 0) = 1 := by
      rw [Units.val_pow_eq_pow_val, hMcoe, w183b5_permMatrix_pow, inv_pow, hinvsq]
      change ((σ ^ 2).toPEquiv.toMatrix) (Sum.inl 0) (Sum.inr 0) = 1
      rw [PEquiv.toMatrix_apply]
      simp [Equiv.toPEquiv_apply, hsig2]
    have hnotscal : M ^ 2 ∉ StatedScalars (Fin 2 ⊕ Fin 2) K := by
      rintro ⟨u, hu⟩
      have hmat : (Matrix.scalar (Fin 2 ⊕ Fin 2) u.1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
          ((M ^ 2 : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) := by
        rw [← Matrix.GeneralLinearGroup.coe_scalar]
        exact congrArg
          (fun x : GL (Fin 2 ⊕ Fin 2) K => (x : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) hu
      have hzero : (Matrix.scalar (Fin 2 ⊕ Fin 2) u.1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)
          (Sum.inl 0) (Sum.inr 0) = 0 := by
        rw [Matrix.scalar_apply, Matrix.diagonal_apply]
        simp [Sum.inl_ne_inr]
      have hcontra : (1 : K) = 0 := by
        have hmat_entry := congrFun (congrFun hmat (Sum.inl 0)) (Sum.inr 0)
        rw [← hentry, ← hmat_entry]
        exact hzero
      exact one_ne_zero hcontra
    let x : StatedProj (StatedSp 2 K) :=
      QuotientGroup.mk (⟨M, hM_mem⟩ : StatedSp 2 K)
    have hx4 : x ^ 4 = 1 := by
      rw [show x = QuotientGroup.mk (⟨M, hM_mem⟩ : StatedSp 2 K) from rfl]
      rw [← QuotientGroup.mk_pow]
      rw [show (⟨M, hM_mem⟩ : StatedSp 2 K) ^ 4 = 1 by
        apply Subtype.ext
        simpa using hM4, QuotientGroup.mk_one]
    have hx2 : x ^ 2 ≠ 1 := by
      intro h
      have h' := h
      rw [show x = QuotientGroup.mk (⟨M, hM_mem⟩ : StatedSp 2 K) from rfl] at h'
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at h'
      have hmem : M ^ 2 ∈ StatedScalars (Fin 2 ⊕ Fin 2) K := by
        have := (Subgroup.mem_subgroupOf).mp h'
        simpa using this
      exact hnotscal hmem
    have hxord : orderOf x = 4 := by
      have hnot : ¬ x ^ 2 ^ 1 = 1 := by
        have : (2 : ℕ) ^ 1 = 2 := by norm_num
        rwa [this]
      have hfin : x ^ 2 ^ (1 + 1) = 1 := by
        have : (2 : ℕ) ^ (1 + 1) = 4 := by norm_num
        rwa [this]
      have h := orderOf_eq_prime_pow hnot hfin
      have : (2 : ℕ) ^ (1 + 1) = 4 := by norm_num
      rwa [this] at h
    refine ⟨e.symm x, ?_⟩
    rw [MulEquiv.orderOf_eq]
    exact hxord

end CFSG.LocalAnalysis.WeakClosure81

end
