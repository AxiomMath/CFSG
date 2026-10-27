module

public import CFSG.LocalAnalysis.StandardType.GGHalfFrameGF2
public import CFSG.LocalAnalysis.StandardType.GGHalfBlockPerm
public import CFSG.LocalAnalysis.StandardType.GGRoundFourSmallATwoBlock

public section

namespace CFSG.StandardType.GGHalf

open CFSG.LieType.Universal.SpecialLinear Matrix

open scoped IsMulCommutative

private theorem card_eq_of_frame {n s r : ℕ}
    (ε : Fin (n + 1) ≃ (Fin 2 × Fin s) ⊕ Fin r) : n + 1 = 2 * s + r := by
  have h := Fintype.card_congr ε
  simpa [Fintype.card_sum, Fintype.card_prod] using h

private theorem one_add_one_f2 : (1 : F2) + 1 = 0 := by
  linear_combination gf2_two

private noncomputable def stdFrameAux {n s r : ℕ}
    (ε : Fin (n + 1) ≃ (Fin 2 × Fin s) ⊕ Fin r) :
    (Fin 2 × Fin s) ⊕ Fin r ≃ Fin (n + 1) := by
  have hcard := card_eq_of_frame ε
  let g : (Fin 2 × Fin s) ⊕ Fin r → Fin (n + 1) :=
    Sum.elim (fun p : Fin 2 × Fin s => (⟨2 * p.2.val + p.1.val, by omega⟩ : Fin (n + 1)))
      (fun i : Fin r => (⟨2 * s + i.val, by omega⟩ : Fin (n + 1)))
  have hg : Function.Bijective g := by
    constructor
    · intro w₁ w₂ h
      have hv : (g w₁).val = (g w₂).val := congrArg Fin.val h
      rcases w₁ with ⟨a₁, j₁⟩ | i₁ <;> rcases w₂ with ⟨a₂, j₂⟩ | i₂
      · simp only [g, Sum.elim_inl] at hv
        have ha : a₁ = a₂ := by have h1 := a₁.isLt; have h2 := a₂.isLt; omega
        have hj : j₁ = j₂ := by have h1 := j₁.isLt; have h2 := j₂.isLt; omega
        cases ha; cases hj; rfl
      · exfalso
        simp only [g, Sum.elim_inl, Sum.elim_inr] at hv
        have h1 := j₁.isLt; have h2 := a₁.isLt; have h3 := i₂.isLt; omega
      · exfalso
        simp only [g, Sum.elim_inl, Sum.elim_inr] at hv
        have h1 := j₂.isLt; have h2 := a₂.isLt; have h3 := i₁.isLt; omega
      · simp only [g, Sum.elim_inr] at hv
        have hi : i₁ = i₂ := by have h1 := i₁.isLt; have h2 := i₂.isLt; omega
        cases hi; rfl
    · intro x
      have hx := x.isLt
      by_cases hxs : x.val < 2 * s
      · refine ⟨Sum.inl ((⟨x.val % 2, Nat.mod_lt _ (by norm_num)⟩ : Fin 2),
          (⟨x.val / 2, Nat.div_lt_of_lt_mul (by omega)⟩ : Fin s)), ?_⟩
        apply Fin.ext
        simp only [g, Sum.elim_inl]
        exact Nat.div_add_mod x.val 2
      · refine ⟨Sum.inr (⟨x.val - 2 * s, by omega⟩ : Fin r), ?_⟩
        apply Fin.ext
        simp only [g, Sum.elim_inr]
        omega
  exact Equiv.ofBijective g hg

private noncomputable def stdFrame {n s r : ℕ}
    (ε : Fin (n + 1) ≃ (Fin 2 × Fin s) ⊕ Fin r) :
    Fin (n + 1) ≃ (Fin 2 × Fin s) ⊕ Fin r :=
  (stdFrameAux ε).symm

private theorem stdFrame_symm_inl_val {n s r : ℕ}
    (ε : Fin (n + 1) ≃ (Fin 2 × Fin s) ⊕ Fin r) (a : Fin 2) (j : Fin s) :
    (((stdFrame ε).symm (Sum.inl (a, j)) : Fin (n + 1))).val = 2 * j.val + a.val := by
  change (stdFrameAux ε (Sum.inl (a, j))).val = 2 * j.val + a.val
  rfl

private theorem stdFrame_symm_inr_val {n s r : ℕ}
    (ε : Fin (n + 1) ≃ (Fin 2 × Fin s) ⊕ Fin r) (i : Fin r) :
    (((stdFrame ε).symm (Sum.inr i) : Fin (n + 1))).val = 2 * s + i.val := by
  change (stdFrameAux ε (Sum.inr i)).val = 2 * s + i.val
  rfl

private noncomputable def pairIdx {n s r : ℕ}
    (ε : Fin (n + 1) ≃ (Fin 2 × Fin s) ⊕ Fin r) (j : Fin s) : Fin n :=
  ⟨2 * j.val, by
    have hcard := card_eq_of_frame ε
    have hj := j.isLt
    omega⟩

private theorem pairIdx_val {n s r : ℕ}
    (ε : Fin (n + 1) ≃ (Fin 2 × Fin s) ⊕ Fin r) (j : Fin s) :
    (pairIdx ε j).val = 2 * j.val := rfl

private theorem pairIdx_castSucc_eq {n s r : ℕ}
    (ε : Fin (n + 1) ≃ (Fin 2 × Fin s) ⊕ Fin r) (j : Fin s) :
    (pairIdx ε j).castSucc = (stdFrame ε).symm (Sum.inl ((0 : Fin 2), j)) := by
  apply Fin.ext
  rw [Fin.val_castSucc, pairIdx_val, stdFrame_symm_inl_val]
  simp

private theorem pairIdx_succ_eq {n s r : ℕ}
    (ε : Fin (n + 1) ≃ (Fin 2 × Fin s) ⊕ Fin r) (j : Fin s) :
    (pairIdx ε j).succ = (stdFrame ε).symm (Sum.inl ((1 : Fin 2), j)) := by
  apply Fin.ext
  rw [Fin.val_succ, pairIdx_val, stdFrame_symm_inl_val]
  simp

private theorem det_rhoM : rhoM.det = 1 := by
  rw [rhoM, Matrix.det_fin_two_of]
  rw [zero_mul, one_mul, zero_sub, neg_eq_iff_add_eq_zero, one_add_one_f2]

private theorem nsMat_std_single_coe {n s r : ℕ}
    (ε : Fin (n + 1) ≃ (Fin 2 × Fin s) ⊕ Fin r) (j : Fin s) :
    SLNS.nsMat (stdFrame ε) rhoM (Pi.single j 1) =
      1 + Matrix.single (pairIdx ε j).castSucc (pairIdx ε j).succ (1 : F2)
        + Matrix.single (pairIdx ε j).succ (pairIdx ε j).castSucc 1
        + Matrix.single (pairIdx ε j).castSucc (pairIdx ε j).castSucc 1 := by
  rw [pairIdx_castSucc_eq ε j, pairIdx_succ_eq ε j]
  ext a b
  obtain ⟨w, rfl⟩ : ∃ w, a = (stdFrame ε).symm w :=
    ⟨(stdFrame ε) a, (Equiv.symm_apply_apply (stdFrame ε) a).symm⟩
  obtain ⟨w', rfl⟩ : ∃ w', b = (stdFrame ε).symm w' :=
    ⟨(stdFrame ε) b, (Equiv.symm_apply_apply (stdFrame ε) b).symm⟩
  rcases w with ⟨x, l⟩ | t <;> rcases w' with ⟨y, l'⟩ | t'
  · by_cases hl : l = l'
    · subst hl
      rw [SLNS.nsMat_block (ε := stdFrame ε) (C := rhoM) (k := Pi.single j 1) (j := l)
        (a := x) (b := y)]
      by_cases hjl : j = l
      · subst hjl
        rw [Pi.single_eq_same, pow_one]
        fin_cases x <;> fin_cases y <;>
          simp [rhoM, Matrix.single_apply, Matrix.one_apply, Equiv.symm_apply_eq,
            Equiv.apply_symm_apply, Sum.inl.injEq, Prod.mk.injEq, gf2_two, one_add_one_f2]
      · rw [Pi.single_eq_of_ne' hjl, pow_zero]
        fin_cases x <;> fin_cases y <;>
          simp [Matrix.single_apply, Matrix.one_apply, Equiv.symm_apply_eq,
            Equiv.apply_symm_apply, Sum.inl.injEq, Prod.mk.injEq, hjl, gf2_two,
            one_add_one_f2]
    · rw [SLNS.nsMat_apply_of_block_ne (stdFrame ε) rhoM (Pi.single j 1) hl x y]
      by_cases hjl : j = l
      · have hjl' : ¬ j = l' := fun h => hl (hjl.symm.trans h)
        fin_cases x <;> fin_cases y <;>
          simp [Matrix.single_apply, Matrix.one_apply, Equiv.symm_apply_eq,
            Equiv.apply_symm_apply, Sum.inl.injEq, Prod.mk.injEq, hjl, hjl', hl, Ne.symm hl, gf2_two,
            one_add_one_f2]
      · by_cases hjl' : j = l'
        · fin_cases x <;> fin_cases y <;>
            simp [Matrix.single_apply, Matrix.one_apply, Equiv.symm_apply_eq,
              Equiv.apply_symm_apply, Sum.inl.injEq, Prod.mk.injEq, hjl, hjl', hl, Ne.symm hl, gf2_two,
              one_add_one_f2]
        · fin_cases x <;> fin_cases y <;>
            simp [Matrix.single_apply, Matrix.one_apply, Equiv.symm_apply_eq,
              Equiv.apply_symm_apply, Sum.inl.injEq, Prod.mk.injEq, hjl, hjl', hl, Ne.symm hl, gf2_two,
              one_add_one_f2]
  · rw [SLNS.nsMat, Matrix.submatrix_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply,
        SLNS.nsCore, Matrix.fromBlocks_apply₁₂]
    simp only [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply,
      Equiv.symm_apply_eq, Equiv.apply_symm_apply]
    simp
  · rw [SLNS.nsMat, Matrix.submatrix_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply,
        SLNS.nsCore, Matrix.fromBlocks_apply₂₁]
    simp only [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply,
      Equiv.symm_apply_eq, Equiv.apply_symm_apply]
    simp
  · rw [SLNS.nsMat, Matrix.submatrix_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply,
        SLNS.nsCore, Matrix.fromBlocks_apply₂₂]
    simp only [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply,
      Equiv.symm_apply_eq, Equiv.apply_symm_apply]
    simp

private theorem transvection_prod_coe {N : ℕ} {i j : Fin N} (hij : i ≠ j) :
    ((SpecialLinearGroup.transvection hij (1 : F2) *
        SpecialLinearGroup.transvection hij.symm 1 : SpecialLinearGroup (Fin N) F2) :
        Matrix (Fin N) (Fin N) F2) =
      1 + Matrix.single i j (1 : F2) + Matrix.single j i 1 + Matrix.single i i 1 := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.transvection_coe,
      Matrix.SpecialLinearGroup.transvection_coe]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.one_mul, Matrix.mul_one]
  rw [Matrix.single_mul_single_same, mul_one]
  abel

private theorem transvection_self_mul' {N : ℕ} {i j : Fin N} (hij : i ≠ j) :
    SpecialLinearGroup.transvection hij (1 : F2) *
      SpecialLinearGroup.transvection hij 1 = 1 := by
  rw [← SpecialLinearGroup.transvection_add, one_add_one_f2]
  exact SpecialLinearGroup.transvection_coeff_zero hij

private theorem omegaBlock_eq_tv_mul (n : ℕ) (k : Fin n) :
    omegaBlock n k =
      SpecialLinearGroup.transvection
          (show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne (1 : F2) *
        SpecialLinearGroup.transvection
          ((show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne.symm) 1 := by
  rw [omegaBlock, ← slPerm_swap_castSucc_succ gf2_two k,
    slPerm_swap_eq_transvections gf2_two
      (show k.castSucc < k.succ from Fin.castSucc_lt_succ).ne,
    mul_assoc, transvection_self_mul', mul_one]

private theorem nsSL_std_single {n s r : ℕ}
    (ε : Fin (n + 1) ≃ (Fin 2 × Fin s) ⊕ Fin r) (j : Fin s) :
    SLNS.nsSL (stdFrame ε) det_rhoM (Pi.single j 1) = omegaBlock n (pairIdx ε j) := by
  apply Subtype.ext
  change SLNS.nsMat (stdFrame ε) rhoM (Pi.single j 1) =
    ((omegaBlock n (pairIdx ε j) : SpecialLinearGroup (Fin (n + 1)) F2) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) F2)
  rw [nsMat_std_single_coe ε j, omegaBlock_eq_tv_mul, transvection_prod_coe,
      pairIdx_castSucc_eq ε j, pairIdx_succ_eq ε j]

private theorem pairIdx_mem {n s r : ℕ}
    (ε : Fin (n + 1) ≃ (Fin 2 × Fin s) ⊕ Fin r) (j : Fin s) :
    omegaBlock n (pairIdx ε j) ∈ halfTorus n :=
  Subgroup.subset_closure ⟨pairIdx ε j, by rw [pairIdx_val]; omega, rfl⟩

private theorem slPerm_inv_mul_mul_coe {N : ℕ} (π : Equiv.Perm (Fin N))
    (M : Matrix (Fin N) (Fin N) F2) :
    (((slPerm gf2_two π)⁻¹ : SpecialLinearGroup (Fin N) F2) : Matrix (Fin N) (Fin N) F2) * M *
        (slPerm gf2_two π : Matrix (Fin N) (Fin N) F2) = M.submatrix π π := by
  rw [← map_inv]
  rw [coe_slPerm, coe_slPerm, signedPerm_one_eq_permMatrix, signedPerm_one_eq_permMatrix]
  simp only [inv_inv]
  rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  rw [Matrix.submatrix_submatrix]
  rfl

theorem exists_perm_nsMat_mem_halfTorus {n s r : ℕ}
    (ε : Fin (n + 1) ≃ (Fin 2 × Fin s) ⊕ Fin r) :
    ∃ π : Equiv.Perm (Fin (n + 1)), ∀ (k : Fin s → ℕ) (M : SpecialLinearGroup (Fin (n + 1)) F2),
      (M : Matrix (Fin (n + 1)) (Fin (n + 1)) F2) = SLNS.nsMat ε rhoM k →
        (slPerm gf2_two π)⁻¹ * M * slPerm gf2_two π ∈ halfTorus n := by
  let σ := stdFrame ε
  let π : Equiv.Perm (Fin (n + 1)) := σ.trans ε.symm
  refine ⟨π, fun k M hM => ?_⟩
  have hcomp : ∀ i, ε (π i) = σ i := by
    intro i
    rw [show π i = ε.symm (σ i) from rfl, Equiv.apply_symm_apply]
  have hX : (((slPerm gf2_two π)⁻¹ * M * slPerm gf2_two π : SpecialLinearGroup (Fin (n + 1)) F2) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) F2) = SLNS.nsMat σ rhoM k := by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
    rw [slPerm_inv_mul_mul_coe, hM]
    rw [SLNS.nsMat, SLNS.nsMat, Matrix.submatrix_submatrix]
    rw [show ε ∘ π = σ from funext hcomp]
  have hXeq : (slPerm gf2_two π)⁻¹ * M * slPerm gf2_two π = SLNS.nsSL σ det_rhoM k := by
    apply Subtype.ext
    exact hX
  have hdecomp : k = ∑ j : Fin s, k j • Pi.single j (1 : ℕ) := by
    funext i
    rw [Finset.sum_apply]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      rw [Pi.smul_apply, Pi.single_eq_of_ne' hj, smul_zero]
    · intro hi; exact absurd (Finset.mem_univ i) hi
  haveI hH : IsMulCommutative (halfTorus n) :=
    IsMulCommutative.of_comm fun a b => Subtype.ext (halfTorus_comm a.2 b.2)
  let g : Fin s → halfTorus n := fun j => ⟨omegaBlock n (pairIdx ε j), pairIdx_mem ε j⟩
  have hsingle : ∀ j : Fin s, SLNS.nsSL σ det_rhoM (Pi.single j 1) = (↑(g j) : SpecialLinearGroup (Fin (n + 1)) F2) := by
    intro j
    rw [nsSL_std_single ε j]
  have hgen_prod : ∀ t : Finset (Fin s),
      SLNS.nsSL σ det_rhoM (t.sum fun j => k j • Pi.single j (1 : ℕ)) =
        ↑(t.prod fun j => (g j) ^ (k j)) := by
    intro t
    induction t using Finset.induction_on with
    | empty => simp [SLNS.nsSL_zero]
    | insert j t hj ih =>
        rw [Finset.sum_insert hj, Finset.prod_insert hj, ← SLNS.nsSL_mul, ih,
            ← SLNS.nsSL_pow, hsingle j, ← Subgroup.coe_pow, ← Subgroup.coe_mul]
  have hmain : SLNS.nsSL σ det_rhoM k =
      ↑(Finset.univ.prod fun j => (g j) ^ (k j)) := by
    conv_lhs => rw [hdecomp]
    exact hgen_prod Finset.univ
  rw [hXeq, hmain]
  exact (Finset.univ.prod fun j => (g j) ^ (k j)).2

end CFSG.StandardType.GGHalf

end
