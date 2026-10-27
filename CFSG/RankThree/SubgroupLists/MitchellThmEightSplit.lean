module

public import CFSG.RankThree.SubgroupLists.MitchellThmEight
public import CFSG.RankThree.SubgroupLists.MitchellDegenerate
public import CFSG.RankThree.SubgroupLists.SymplecticSkewElations
public import CFSG.RankThree.SubgroupLists.MitchellQOne
public import Certificates.Certificate43

public section

namespace CFSG.RankThree.SubgroupLists

open Matrix CFSG.Assembly.LowTwoRank Module

local notation "V₄" => Fin 2 ⊕ Fin 2

variable {K : Type} [Field K]

@[expose] def pmSwap : Equiv.Perm V₄ := Equiv.swap (Sum.inr 0) (Sum.inl 1)

@[expose] def pmCoord (M : Matrix V₄ V₄ K) : Matrix V₄ V₄ K := M.submatrix pmSwap pmSwap

theorem pmCoord_mul (M N : Matrix V₄ V₄ K) : pmCoord (M * N) = pmCoord M * pmCoord N :=
  (Matrix.submatrix_mul_equiv M N pmSwap pmSwap pmSwap).symm

theorem pmCoord_pmCoord (M : Matrix V₄ V₄ K) : pmCoord (pmCoord M) = M := by
  ext i j
  simp [pmCoord, pmSwap]

theorem pmCoord_one : pmCoord (1 : Matrix V₄ V₄ K) = 1 :=
  Matrix.submatrix_one_equiv pmSwap

theorem pmCoord_add (M N : Matrix V₄ V₄ K) : pmCoord (M + N) = pmCoord M + pmCoord N := rfl

theorem pmCoord_smul (c : K) (M : Matrix V₄ V₄ K) : pmCoord (c • M) = c • pmCoord M := rfl

theorem pmCoord_tStdMat : pmCoord (tStdMat : Matrix V₄ V₄ K) = fromBlocks 1 0 0 (-1) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [pmCoord, pmSwap, tStdMat, stdSign, Matrix.one_apply, Equiv.swap_apply_def]

@[expose] def offBlock' (M : Matrix V₄ V₄ K) : Matrix (Fin 2) (Fin 2) K :=
  !![M (Sum.inl 1) (Sum.inl 0), M (Sum.inl 1) (Sum.inr 0);
    M (Sum.inr 1) (Sum.inl 0), M (Sum.inr 1) (Sum.inr 0)]

theorem pmCoord_of_commute_tStd (h2 : (2 : K) ≠ 0) {M : Matrix V₄ V₄ K}
    (hM : M * tStdMat = tStdMat * M) :
    pmCoord M = fromBlocks (plusBlock M) 0 0 (minusBlock M) := by
  obtain ⟨z1, z2, z3, z4, z5, z6, z7, z8⟩ := cross_zero_of_commute_tStd h2 hM
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [pmCoord, pmSwap, plusBlock, minusBlock, Equiv.swap_apply_def, z1, z2, z3, z4, z5, z6,
      z7, z8]

theorem pmCoord_of_anticommute_tStd (h2 : (2 : K) ≠ 0) {M : Matrix V₄ V₄ K}
    (hM : M * tStdMat = -(tStdMat * M)) :
    pmCoord M = fromBlocks 0 (offBlock M) (offBlock' M) 0 := by
  have hz : ∀ i j : V₄, stdSign i = (stdSign j : K) → M i j = 0 := by
    intro i j hij
    have h := congrFun (congrFun hM i) j
    simp only [tStdMat, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.neg_apply] at h
    rw [hij] at h
    have hs : stdSign j * stdSign j = (1 : K) := stdSign_sq j
    have h' : (2 : K) * M i j = 0 := by linear_combination stdSign j * h - 2 * M i j * hs
    exact (mul_eq_zero.mp h').resolve_left h2
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [pmCoord, pmSwap, offBlock, offBlock', Equiv.swap_apply_def] <;>
    exact hz _ _ (by simp [stdSign])

theorem pmCoord_fromBlocks_diag (a b c d : K) :
    pmCoord (fromBlocks !![a, 0; 0, b] 0 0 !![c, 0; 0, d]) =
      fromBlocks !![a, 0; 0, c] 0 0 !![b, 0; 0, d] := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [pmCoord, pmSwap, Equiv.swap_apply_def]

theorem pmCoord_fromBlocks_scalar (a b c d : K) :
    pmCoord (fromBlocks (a • 1) (b • 1) (c • 1) (d • 1)) =
      fromBlocks !![a, b; c, d] 0 0 !![a, b; c, d] := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [pmCoord, pmSwap, Equiv.swap_apply_def, Matrix.one_apply]

variable [Finite K]

theorem cliffB_tStd_of_thm_eight (p : ℕ) [Fact p.Prime] [CharP K p] (hp2 : p ≠ 2)
    {G : Subgroup (GL V₄ K)} (hU0 : ∀ x ∈ G, IsSqZero x → x = 1)
    {z w : GL V₄ K} (hzG : z ∈ G) (hwG : w ∈ G) (hw : IsNCInv w)
    (hzt : (z : Matrix V₄ V₄ K) * tStdMat = tStdMat * (z : Matrix V₄ V₄ K))
    {eps : K} (heps : eps ≠ 0) (hzm : minusBlock (z : Matrix V₄ V₄ K) = eps • 1)
    {lam lam' : K} {W Wi : Matrix (Fin 2) (Fin 2) K} (hWi : Wi * W = 1) (hWi' : W * Wi = 1)
    (hzW : plusBlock (z : Matrix V₄ V₄ K) * W = W * !![lam, 0; 0, lam'])
    (hord : ∀ k, 1 ≤ k → k < 6 → (lam * eps⁻¹) ^ k ≠ 1) :
    cliffB tStdMat (w : Matrix V₄ V₄ K) = 0 ∨
      cliffB tStdMat (w : Matrix V₄ V₄ K) * cliffB tStdMat (w : Matrix V₄ V₄ K) = 1 := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_charP hp2
  by_contra hcon
  push Not at hcon
  obtain ⟨hβ0, hβ1⟩ := hcon
  set β := cliffB tStdMat (w : Matrix V₄ V₄ K) with hβ
  have htM : (tStdMat : Matrix V₄ V₄ K) ∈ (cliffSpace : Submodule K _) := by
    rw [tStdMat_eq_cliffMat]
    exact cliffMat_mem _ _ _ _ _
  have hwM := (mem_cliffSpace_of_involution h2 hw.1 hw.2.1 hw.2.2.1 hw.2.2.2).1
  have hww : (w : Matrix V₄ V₄ K) * w = 1 := by rw [← Units.val_mul, hw.2.1, Units.val_one]
  have htt : cliffB (tStdMat : Matrix V₄ V₄ K) tStdMat = 1 :=
    cliffB_eq_one_of_mul_self h2 tStdMat_mul_self
  set v : Matrix V₄ V₄ K := (w : Matrix V₄ V₄ K) - β • tStdMat with hv
  have hvM : v ∈ (cliffSpace : Submodule K _) :=
    Submodule.sub_mem _ hwM (Submodule.smul_mem _ _ htM)
  have hvt : cliffB v tStdMat = 0 := by
    rw [hv, cliffB_sub_left, cliffB_smul_left, htt, cliffB_comm, ← hβ]
    ring
  set Q : K := 1 - β * β with hQdef
  have hQ : Q ≠ 0 := fun h => hβ1 (by linear_combination -h)
  have hexp : cliffB v v = cliffB (w : Matrix V₄ V₄ K) w - 2 * β * cliffB tStdMat w +
      β * β * cliffB (tStdMat : Matrix V₄ V₄ K) tStdMat := by
    rw [hv, cliffB_sub_left, cliffB_smul_left,
      cliffB_comm (w : Matrix V₄ V₄ K) ((w : Matrix V₄ V₄ K) - β • tStdMat), cliffB_sub_left,
      cliffB_smul_left, cliffB_comm tStdMat ((w : Matrix V₄ V₄ K) - β • tStdMat),
      cliffB_sub_left, cliffB_smul_left, cliffB_comm (w : Matrix V₄ V₄ K) tStdMat]
    ring
  have hvv : v * v = Q • (1 : Matrix V₄ V₄ K) := by
    rw [mul_self_of_mem h2 hvM, ← cliffB_self h2, hexp, cliffB_eq_one_of_mul_self h2 hww, htt,
      ← hβ, hQdef]
    congr 1
    ring
  have hvanti : v * tStdMat = -(tStdMat * v) := (mul_eq_neg_mul_iff h2 hvM htM).mpr hvt
  set A := offBlock v with hA
  set A' := offBlock' v with hA'
  have hpmv := pmCoord_of_anticommute_tStd h2 hvanti
  have hAA : A * A' = Q • 1 ∧ A' * A = Q • 1 := by
    have h := congrArg pmCoord hvv
    rw [pmCoord_mul, hpmv, pmCoord_smul, pmCoord_one, Matrix.fromBlocks_multiply,
      ← Matrix.fromBlocks_one, Matrix.fromBlocks_smul] at h
    simp only [Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero, smul_zero] at h
    rw [Matrix.fromBlocks_inj] at h
    exact ⟨h.1, h.2.2.2⟩
  set Pm : Matrix V₄ V₄ K := fromBlocks W 0 0 (A' * W) with hPm
  set Pmi : Matrix V₄ V₄ K := fromBlocks Wi 0 0 (Q⁻¹ • (Wi * A)) with hPmi
  have hPP : Pm * Pmi = 1 := by
    rw [hPm, hPmi, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]
    simp only [Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero]
    have h22 : A' * W * (Q⁻¹ • (Wi * A)) = 1 := by
      rw [Matrix.mul_smul, Matrix.mul_assoc A' W, ← Matrix.mul_assoc W Wi A, hWi', Matrix.one_mul,
        hAA.2, smul_smul, inv_mul_cancel₀ hQ, one_smul]
    rw [hWi', h22]
  have hPP' : Pmi * Pm = 1 := by
    rw [hPm, hPmi, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]
    simp only [Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero]
    have h22 : Q⁻¹ • (Wi * A) * (A' * W) = 1 := by
      rw [Matrix.smul_mul, Matrix.mul_assoc Wi A (A' * W), ← Matrix.mul_assoc A A' W, hAA.1,
        Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, hWi, smul_smul, inv_mul_cancel₀ hQ,
        one_smul]
    rw [hWi, h22]
  set P : Matrix V₄ V₄ K := pmCoord Pm with hP
  set Pinv : Matrix V₄ V₄ K := pmCoord Pmi with hPinv
  have hPPinv : P * Pinv = 1 := by rw [hP, hPinv, ← pmCoord_mul, hPP, pmCoord_one]
  have hPinvP : Pinv * P = 1 := by rw [hP, hPinv, ← pmCoord_mul, hPP', pmCoord_one]
  let Pgl : GL V₄ K := ⟨P, Pinv, hPPinv, hPinvP⟩
  set G'' := G.map (MulAut.conj Pgl⁻¹).toMonoidHom
  have hU0'' : ∀ x ∈ G'', IsSqZero x → x = 1 := by
    intro x hx hsq
    rw [mem_map_conj, inv_inv] at hx
    have h1 := hU0 _ hx (isSqZero_conj hsq Pgl)
    calc x = Pgl⁻¹ * (Pgl * x * Pgl⁻¹) * Pgl := by group
      _ = 1 := by rw [h1]; group
  have hconj : ∀ g : GL V₄ K, ((Pgl⁻¹ * g * Pgl : GL V₄ K) : Matrix V₄ V₄ K) =
      Pinv * (g : Matrix V₄ V₄ K) * P := by
    intro g
    rw [Units.val_mul, Units.val_mul]
    rfl
  have hpmconj : ∀ M : Matrix V₄ V₄ K, Pinv * M * P = pmCoord (Pmi * pmCoord M * Pm) := by
    intro M
    rw [← pmCoord_pmCoord (Pinv * M * P)]
    congr 1
    rw [pmCoord_mul, pmCoord_mul, hPinv, hP, pmCoord_pmCoord, pmCoord_pmCoord]
  have hdiag : ∀ c : K, c • (1 : Matrix (Fin 2) (Fin 2) K) = !![c, 0; 0, c] := by
    intro c
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.one_apply]
  have hz'' : ((Pgl⁻¹ * z * Pgl : GL V₄ K) : Matrix V₄ V₄ K) =
      fromBlocks !![lam, 0; 0, eps] 0 0 !![lam', 0; 0, eps] := by
    rw [hconj, hpmconj, pmCoord_of_commute_tStd h2 hzt, hzm, hPmi, hPm,
      Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp only [Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero]
    have e1 : Wi * plusBlock (z : Matrix V₄ V₄ K) * W = !![lam, 0; 0, lam'] := by
      rw [Matrix.mul_assoc, hzW, ← Matrix.mul_assoc, hWi, Matrix.one_mul]
    have e2' : Wi * A * (A' * W) = Q • (1 : Matrix (Fin 2) (Fin 2) K) := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc A, hAA.1, Matrix.smul_mul, Matrix.one_mul,
        Matrix.mul_smul, hWi]
    have e2 : Q⁻¹ • (Wi * A) * (eps • 1) * (A' * W) = !![eps, 0; 0, eps] := by
      simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one]
      rw [e2']
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.one_apply] <;> field_simp
    rw [e1, e2, pmCoord_fromBlocks_diag]
  have hpmw : pmCoord (w : Matrix V₄ V₄ K) =
      fromBlocks (β • 1) A A' (-β • (1 : Matrix (Fin 2) (Fin 2) K)) := by
    have hwv : (w : Matrix V₄ V₄ K) = β • tStdMat + v := by rw [hv]; abel
    rw [hwv, pmCoord_add, pmCoord_smul, pmCoord_tStdMat, hpmv, Matrix.fromBlocks_smul,
      Matrix.fromBlocks_add]
    simp [hA, hA']
  have hw'' : ((Pgl⁻¹ * w * Pgl : GL V₄ K) : Matrix V₄ V₄ K) =
      fromBlocks !![β, Q; 1, -β] 0 0 !![β, Q; 1, -β] := by
    rw [hconj, hpmconj, hpmw, hPmi, hPm, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp only [Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero]
    have e1 : Wi * (β • 1) * W = β • (1 : Matrix (Fin 2) (Fin 2) K) := by
      rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hWi]
    have e2 : Wi * A * (A' * W) = Q • (1 : Matrix (Fin 2) (Fin 2) K) := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc A, hAA.1, Matrix.smul_mul, Matrix.one_mul,
        Matrix.mul_smul, hWi]
    have e3 : Q⁻¹ • (Wi * A) * A' * W = (1 : K) • (1 : Matrix (Fin 2) (Fin 2) K) := by
      rw [Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_assoc Wi A A', hAA.1, Matrix.mul_smul,
        Matrix.mul_one, Matrix.smul_mul, hWi, smul_smul, inv_mul_cancel₀ hQ]
    have e4 : Q⁻¹ • (Wi * A) * (-β • 1) * (A' * W) = -β • (1 : Matrix (Fin 2) (Fin 2) K) := by
      simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one]
      rw [e2]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.one_apply] <;> field_simp
    rw [e1, e2, e3, e4, pmCoord_fromBlocks_scalar]
  have hzG'' : Pgl⁻¹ * z * Pgl ∈ G'' := by
    rw [mem_map_conj, inv_inv]
    simpa [mul_assoc] using hzG
  have hwG'' : Pgl⁻¹ * w * Pgl ∈ G'' := by
    rw [mem_map_conj, inv_inv]
    simpa [mul_assoc] using hwG
  exact false_of_thm_eight_core p hU0'' hzG'' hwG'' hz'' hw'' (by rw [hQdef]; ring) hβ0 hQ heps
    hord

end CFSG.RankThree.SubgroupLists
