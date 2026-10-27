module

public import CFSG.RankThree.PartOne.KF.R5Levi2
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherNormShell

public section

namespace CFSG.RankThree.PartOne.K1320

open Matrix CFSG CFSG.LieType.Universal.Unitary CFSG.RankThree.PartOne.KFU
  CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_involutive unitaryInvolution_apply
  exists_add_unitaryInvolution_eq)
open scoped MatrixGroups

section Lemmas

variable {K : Type} [Field K] (σ : K ≃+* K)

theorem rootMatrix_01 [CharP K 2] (c : K) : rootMatrix σ 0 1 c = blkB σ !![1, c; 0, 1] := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [rootMatrix, blkB, Fin.rev, CharTwo.neg_eq]

theorem rootMatrix_10 [CharP K 2] (c : K) : rootMatrix σ 1 0 c = blkB σ !![1, 0; c, 1] := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [rootMatrix, blkB, Fin.rev, CharTwo.neg_eq]

theorem rootMatrix_23 [CharP K 2] (hσ : ∀ x, σ (σ x) = x) (c : K) :
    rootMatrix σ 2 3 c = blkB σ !![1, σ c; 0, 1] := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [rootMatrix, blkB, Fin.rev, CharTwo.neg_eq, hσ]

theorem rootMatrix_32 [CharP K 2] (hσ : ∀ x, σ (σ x) = x) (c : K) :
    rootMatrix σ 3 2 c = blkB σ !![1, 0; σ c, 1] := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [rootMatrix, blkB, Fin.rev, CharTwo.neg_eq, hσ]

theorem longRootMatrix_0 (c : K) : longRootMatrix 0 c = blk22 !![1, c; 0, 1] := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [longRootMatrix, blk22, Fin.rev]

theorem longRootMatrix_3 (c : K) : longRootMatrix 3 c = blk22 !![1, 0; c, 1] := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [longRootMatrix, blk22, Fin.rev]

theorem conjA_01 (c : K) :
    blk22 !![0, 1; 1, 0] * rootMatrix σ 0 1 c = rootMatrix σ 3 1 c * blk22 !![0, 1; 1, 0] := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [rootMatrix, blk22, Fin.rev, Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply]

theorem conjA_10 (c : K) :
    blk22 !![0, 1; 1, 0] * rootMatrix σ 1 0 c = rootMatrix σ 1 3 c * blk22 !![0, 1; 1, 0] := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [rootMatrix, blk22, Fin.rev, Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply]

theorem conjA_23 (c : K) :
    blk22 !![0, 1; 1, 0] * rootMatrix σ 2 3 c = rootMatrix σ 2 0 c * blk22 !![0, 1; 1, 0] := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [rootMatrix, blk22, Fin.rev, Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply]

theorem conjA_32 (c : K) :
    blk22 !![0, 1; 1, 0] * rootMatrix σ 3 2 c = rootMatrix σ 0 2 c * blk22 !![0, 1; 1, 0] := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [rootMatrix, blk22, Fin.rev, Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply]

theorem conjB_03 (c : K) :
    blkB σ !![0, 1; 1, 0] * longRootMatrix 0 c = longRootMatrix 1 c * blkB σ !![0, 1; 1, 0] := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [longRootMatrix, blkB, Fin.rev, Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply]

theorem conjB_30 (c : K) :
    blkB σ !![0, 1; 1, 0] * longRootMatrix 3 c = longRootMatrix 2 c * blkB σ !![0, 1; 1, 0] := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [longRootMatrix, blkB, Fin.rev, Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply]

def trU {k : Type} [Field k] (c : k) : SL(2, k) :=
  ⟨!![1, c; 0, 1], by rw [Matrix.det_fin_two]; simp⟩

def trL {k : Type} [Field k] (c : k) : SL(2, k) :=
  ⟨!![1, 0; c, 1], by rw [Matrix.det_fin_two]; simp⟩

def wSL (k : Type) [Field k] [CharP k 2] : SL(2, k) :=
  ⟨!![0, 1; 1, 0], by rw [Matrix.det_fin_two]; simp [CharTwo.neg_eq]⟩

theorem liftSL_trU (c : fixF σ) :
    ((liftSL σ (trU c) : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = !![1, (c : K); 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rw [coe_liftSL] <;> simp [trU]

theorem liftSL_trL (c : fixF σ) :
    ((liftSL σ (trL c) : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = !![1, 0; (c : K), 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rw [coe_liftSL] <;> simp [trL]

theorem liftSL_wSL [CharP K 2] :
    ((liftSL σ (wSL (fixF σ)) : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = !![0, 1; 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rw [coe_liftSL] <;> simp [wSL]

end Lemmas

theorem suBlock_sup_suBlockB_eq_top {K : Type} [Field K] [CharP K 2] [Finite K] {f : ℕ}
    (hK : Nat.card K = (2 ^ f) ^ 2) (hf : 1 ≤ f) :
    (suBlock (unitaryInvolution K 2 f)).range ⊔
      (suBlockB (unitaryInvolution K 2 f) (unitaryInvolution_involutive hK)).range = ⊤ := by
  set σ := unitaryInvolution K 2 f with hσdef
  have hσ : ∀ c, σ (σ c) = c := unitaryInvolution_involutive hK
  have hU : UnitaryFieldData 2 f K :=
    ⟨Nat.prime_two, hf, by rw [hK]; ring⟩
  set R := (suBlock σ).range ⊔ (suBlockB σ hσ).range with hR
  have hB : ∀ (X : SL(2, K)) (x : ↥(SU σ 4)), gu x = blkB σ (X : Matrix (Fin 2) (Fin 2) K) →
      x ∈ R := by
    intro X x h
    have hx : x = suBlockB σ hσ X := Subtype.ext (Units.ext h)
    rw [hx]
    exact Subgroup.mem_sup_right ⟨X, rfl⟩
  have hA : ∀ (A : SL(2, fixF σ)) (x : ↥(SU σ 4)),
      gu x = blk22 ((liftSL σ A : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) → x ∈ R := by
    intro A x h
    have hx : x = suBlock σ A := Subtype.ext (Units.ext h)
    rw [hx]
    exact Subgroup.mem_sup_left ⟨A, rfl⟩
  have hconj : ∀ w y x : ↥(SU σ 4), w ∈ R → y ∈ R → gu w * gu y = gu x * gu w → x ∈ R := by
    intro w y x hw hy h
    have hx : x = w * y * w⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq]
      exact Subtype.ext (Units.ext h.symm)
    rw [hx]
    exact R.mul_mem (R.mul_mem hw hy) (R.inv_mem hw)
  have hwA : suBlock σ (wSL (fixF σ)) ∈ R := Subgroup.mem_sup_left ⟨_, rfl⟩
  have hwB : suBlockB σ hσ (wSL K) ∈ R := Subgroup.mem_sup_right ⟨_, rfl⟩
  have hgwA : gu (suBlock σ (wSL (fixF σ))) = blk22 !![0, 1; 1, 0] := by
    rw [gu_suBlock, liftSL_wSL]
  have hgwB : gu (suBlockB σ hσ (wSL K)) = blkB σ !![0, 1; 1, 0] := rfl
  have h01 : ∀ (h1 : (0 : Fin 4) ≠ 1) (h2 : (0 : Fin 4) ≠ Fin.rev 0) (h3 : (1 : Fin 4) ≠ Fin.rev 1)
      (c : Multiplicative K), rootHom σ hσ h1 h2 h3 c ∈ R :=
    fun _ _ _ c => hB (trU c.toAdd) _ (rootMatrix_01 σ _)
  have h10 : ∀ (h1 : (1 : Fin 4) ≠ 0) (h2 : (1 : Fin 4) ≠ Fin.rev 1) (h3 : (0 : Fin 4) ≠ Fin.rev 0)
      (c : Multiplicative K), rootHom σ hσ h1 h2 h3 c ∈ R :=
    fun _ _ _ c => hB (trL c.toAdd) _ (rootMatrix_10 σ _)
  have h23 : ∀ (h1 : (2 : Fin 4) ≠ 3) (h2 : (2 : Fin 4) ≠ Fin.rev 2) (h3 : (3 : Fin 4) ≠ Fin.rev 3)
      (c : Multiplicative K), rootHom σ hσ h1 h2 h3 c ∈ R :=
    fun _ _ _ c => hB (trU (σ c.toAdd)) _ (rootMatrix_23 σ hσ _)
  have h32 : ∀ (h1 : (3 : Fin 4) ≠ 2) (h2 : (3 : Fin 4) ≠ Fin.rev 3) (h3 : (2 : Fin 4) ≠ Fin.rev 2)
      (c : Multiplicative K), rootHom σ hσ h1 h2 h3 c ∈ R :=
    fun _ _ _ c => hB (trL (σ c.toAdd)) _ (rootMatrix_32 σ hσ _)
  have hfixc : ∀ c : Multiplicative (traceZero σ), σ ((c.toAdd : traceZero σ) : K) =
      ((c.toAdd : traceZero σ) : K) := by
    intro c
    have h1 := (mem_traceZero σ).1 c.toAdd.2
    rw [eq_neg_of_add_eq_zero_right h1, CharTwo.neg_eq]
  have hL0 : ∀ (h : (0 : Fin 4) ≠ Fin.rev 0) (c : Multiplicative (traceZero σ)),
      longRootHom σ h c ∈ R := fun _ c =>
    hA (trU (⟨((c.toAdd : traceZero σ) : K), hfixc c⟩ : fixF σ)) _
      (by rw [liftSL_trU]; exact longRootMatrix_0 _)
  have hL3 : ∀ (h : (3 : Fin 4) ≠ Fin.rev 3) (c : Multiplicative (traceZero σ)),
      longRootHom σ h c ∈ R := fun _ c =>
    hA (trL (⟨((c.toAdd : traceZero σ) : K), hfixc c⟩ : fixF σ)) _
      (by rw [liftSL_trL]; exact longRootMatrix_3 _)
  refine eq_top_of_rootElements_le (σ := σ) hσ ⟨1, one_ne_zero, ?_⟩
    (fun x hx => exists_add_unitaryInvolution_eq hK hx) (fun x hx => ?_) (by norm_num) R ?_ ?_ ?_
  · rw [map_one]; exact CharTwo.add_self_eq_zero 1
  · obtain ⟨l, hl⟩ := UnitaryHigher.exists_norm_eq hU (c := x)
      (by rw [UnitaryFieldData.bar_apply, ← unitaryInvolution_apply]; exact hx)
    refine ⟨l, ?_⟩
    rw [UnitaryFieldData.norm, UnitaryFieldData.bar_apply, ← unitaryInvolution_apply,
      mul_comm] at hl
    exact hl
  · intro i j hij hi hj hji c
    fin_cases i <;> fin_cases j <;> simp [Fin.rev] at hij hi hj hji ⊢
    · exact h01 _ _ _ c
    · exact hconj _ _ _ hwA (h32 (by decide) (by decide) (by decide) c)
        (by rw [hgwA]; exact conjA_32 σ c.toAdd)
    · exact h10 _ _ _ c
    · exact hconj _ _ _ hwA (h10 (by decide) (by decide) (by decide) c)
        (by rw [hgwA]; exact conjA_10 σ c.toAdd)
    · exact hconj _ _ _ hwA (h23 (by decide) (by decide) (by decide) c)
        (by rw [hgwA]; exact conjA_23 σ c.toAdd)
    · exact h23 _ _ _ c
    · exact hconj _ _ _ hwA (h01 (by decide) (by decide) (by decide) c)
        (by rw [hgwA]; exact conjA_01 σ c.toAdd)
    · exact h32 _ _ _ c
  · intro i hi c
    fin_cases i <;> simp [Fin.rev] at hi ⊢
    · exact hL0 _ c
    · exact hconj _ _ _ hwB (hL0 (by decide) c) (by rw [hgwB]; exact conjB_03 σ _)
    · exact hconj _ _ _ hwB (hL3 (by decide) c) (by rw [hgwB]; exact conjB_30 σ _)
    · exact hL3 _ c
  · intro i k hi hik hk
    fin_cases k <;> simp [Fin.rev] at hk

end CFSG.RankThree.PartOne.K1320
