module

public import CFSG.Monster.VisQuot.Monomial
public import CFSG.Monster.VisCert.FrameRows

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.VisQuot

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.SpinLattice CFSG.Monster.ScalarKernel
  CFSG.Monster.Lifts CFSG.Monster.Visible CFSG.Monster.VisCert

theorem ellCls_eq_dec (i : Fin 24) : ellCls i = dec (2 ^ (i : ℕ)) := by
  rw [dec, Finset.sum_eq_single i (fun j _ hj => by
      rw [bvec_apply, Nat.testBit_two_pow]
      simp [Fin.val_ne_of_ne (Ne.symm hj)]) (by simp)]
  simp [bvec_apply]

theorem GLV_ext_ellCls {u v : GLV} (h : ∀ i, u • ellCls i = v • ellCls i) : u = v :=
  Units.ext (ellBasis.ext fun i => by rw [ellBasis_apply]; exact h i)

theorem wordGL_eq_of_rows {w₁ w₂ : List ℕ} (h₁ : ∀ g ∈ w₁, g < 15) (h₂ : ∀ g ∈ w₂, g < 15)
    (h : ∀ i < 24, actWord frameMatrices w₁ (2 ^ i) = actWord frameMatrices w₂ (2 ^ i)) :
    wordGL w₁ = wordGL w₂ :=
  GLV_ext_ellCls fun i => by
    rw [ellCls_eq_dec, wordGL_smul_dec w₁ h₁, wordGL_smul_dec w₂ h₂, h i i.2]

theorem kGenN_of_lt {g : ℕ} (hg : g < 15) : kGenN g = kGen ⟨g, hg⟩ := by
  rw [kGenN, dite_eq_left hg]

private theorem rows_xi_cube :
    ∀ i < 24, actWord frameMatrices [0, 0, 0] (2 ^ i) = actWord frameMatrices [] (2 ^ i) := by
  decide +kernel

private theorem rows_xi_rel :
    ∀ i < 24, actWord frameMatrices [0] (2 ^ i) = actWord frameMatrices [3, 0, 3, 0, 0] (2 ^ i) := by
  decide +kernel

theorem kGen_zero_pow_three : kGen 0 ^ 3 = 1 := by
  have h := wordGL_eq_of_rows (by decide) (by decide) rows_xi_cube
  simp only [wordGL, kGenN_of_lt (show 0 < 15 by omega), one_mul] at h
  rw [pow_three']
  exact h

theorem kGen_zero_mul_self : kGen 0 * kGen 0 = (kGen 0)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← pow_three', kGen_zero_pow_three]

theorem kGen_zero_eq : kGen 0 = (kGen 0)⁻¹ * kGen 3 * kGen 0 * kGen 3 := by
  have h := wordGL_eq_of_rows (by decide) (by decide) rows_xi_rel
  simp only [wordGL, kGenN_of_lt (show 0 < 15 by omega), kGenN_of_lt (show 3 < 15 by omega),
    one_mul] at h
  rw [← kGen_zero_mul_self]
  exact h

@[expose] def betaPerm : Equiv.Perm (Fin 24) where
  toFun := ![1, 0, 3, 2, 4, 5, 6, 7, 8, 9, 10, 11, 13, 12, 15, 14, 19, 18, 17, 16, 22, 23, 20, 21]
  invFun := ![1, 0, 3, 2, 4, 5, 6, 7, 8, 9, 10, 11, 13, 12, 15, 14, 19, 18, 17, 16, 22, 23, 20, 21]
  left_inv := by decide
  right_inv := by decide

@[expose] def betaList : List ℕ :=
  [1, 0, 3, 2, 4, 5, 6, 7, 8, 9, 10, 11, 13, 12, 15, 14, 19, 18, 17, 16, 22, 23, 20, 21]

private theorem betaPerm_basis : ∀ i, B i ∘ ⇑betaPerm ∈ C := by decide +kernel

private theorem betaPerm_basis' : ∀ i, B i ∘ ⇑betaPerm⁻¹ ∈ C := by decide +kernel

theorem betaPerm_mem : betaPerm ∈ AutPerm := mem_AutPerm_of_basis betaPerm_basis betaPerm_basis'

@[expose] def betaAut : AutPerm := ⟨betaPerm, betaPerm_mem⟩

theorem betaAut_ne_one : betaAut ≠ 1 := fun h => by
  have h0 := congrArg (fun p : AutPerm => ((p : Equiv.Perm (Fin 24)) 0 : ℕ)) h
  exact absurd h0 (by decide)

theorem betaPerm_inv_apply : ∀ i : Fin 24, ((betaPerm⁻¹ i : Fin 24) : ℕ) = betaList.getD i 0 := by
  decide +kernel

theorem comp_betaPerm_inv (U : ℕ → ℤ) :
    (fun i : Fin 24 => U i) ∘ ⇑(betaPerm⁻¹) = fun i : Fin 24 => permN betaList U i := by
  funext i
  simp only [Function.comp, permN, betaPerm_inv_apply]

@[expose] def betaRows : Array ℕ :=
  #[12408, 123, 125, 1781873, 3522665, 3063897, 64, 651449, 5316912, 12177960, 4858928, 12990488,
    8192, 4096, 32768, 16384, 65536, 131072, 262144, 524288, 1048576, 2097152, 5976064, 11911168]

private theorem betaRowsOK :
    allTo (fun i => rowCheck (permN betaList (ellN i)) betaRows[i]!) 24 = true := by
  decide +kernel

theorem modTwoEnd_PO_betaAut_ellCls (i : Fin 24) :
    modTwoEnd (PO betaAut) (ellCls i) = dec betaRows[(i : ℕ)]! := by
  have hmem : (fun j : Fin 24 => permN betaList (ellN i) j) ∈ codeLattice C :=
    comp_betaPerm_inv (ellN i) ▸ comp_mem_codeLattice (inv_mem betaPerm_mem) (ellN_mem i)
  rw [ellCls_eq, modTwoEnd_PO_cls]
  exact (cls_eq_of_eq _ hmem (comp_betaPerm_inv (ellN i))).trans
    (cls_eq_dec_of_rowCheck hmem (allTo_spec betaRowsOK i.2))

theorem permHom_betaAut_smul_dec (v : ℕ) :
    permHom betaAut • dec v = dec (actRows betaRows v) := by
  show modTwoEnd (PO betaAut) (dec v) = _
  rw [dec_actRows, dec, map_sum]
  simp only [map_smul, modTwoEnd_PO_betaAut_ellCls]

private theorem rows_beta :
    ∀ i < 24, actWord frameMatrices [0, 0, 9, 0] (2 ^ i) = actRows betaRows (2 ^ i) := by
  decide +kernel

theorem conj_kGen_nine : kGen 0 * kGen 9 * (kGen 0)⁻¹ = permHom betaAut := by
  have h : wordGL [0, 0, 9, 0] = permHom betaAut := GLV_ext_ellCls fun i => by
    rw [ellCls_eq_dec, wordGL_smul_dec _ (by decide), permHom_betaAut_smul_dec, rows_beta i i.2]
  simp only [wordGL, kGenN_of_lt (show 0 < 15 by omega), kGenN_of_lt (show 9 < 15 by omega),
    one_mul] at h
  rw [← kGen_zero_mul_self, ← mul_assoc]
  exact h

theorem kGen_nine_eq : kGen 9 = modTwoUnit (gO (bC 6)) := by
  rw [kGen_of_three_le (by decide)]
  rfl

theorem kGen_three_eq : kGen 3 = modTwoUnit (gO (bC 0)) := by
  rw [kGen_of_three_le (by decide)]
  rfl

end CFSG.Monster.VisQuot
