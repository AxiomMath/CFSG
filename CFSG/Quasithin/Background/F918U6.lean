module

public import CFSG.Quasithin.Background.F918U4
public import CFSG.Quasithin.Background.F918U5

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique
open CFSG.Quasithin.B5.Ln (mat dmat)
open scoped Matrix

private theorem upPos_row_lt_col : ∀ p < 10, D35Chk.upI p < D35Chk.upJ p := by decide

private theorem exists_upPos_of_between : ∀ p < 10, ∀ k : Fin 5, D35Chk.upI p < k → k < D35Chk.upJ p →
    ∃ q < 10, p < q ∧ D35Chk.upI q = k ∧ D35Chk.upJ q = D35Chk.upJ p := by decide

private theorem zmod2_decide_add (a b : ZMod 2) :
    decide (a + b = 1) = xor (decide (a = 1)) (decide (b = 1)) := by
  revert a b; decide

private theorem zmod2_eq_zero_of_decide (a : ZMod 2) (h : decide (a = 1) = false) : a = 0 := by
  revert a; decide

private theorem mat5_add_self (M : Matrix (Fin 5) (Fin 5) (ZMod 2)) : M + M = 0 := by
  ext i j
  rw [Matrix.add_apply, Matrix.zero_apply]
  generalize M i j = a
  revert a; decide

private theorem mul_apply_of_upper {A B : Matrix (Fin 5) (Fin 5) (ZMod 2)} {i j : Fin 5} (hij : i < j)
    (hA : ∀ k, k < i → A i k = 0) (hB : ∀ k, j < k → B k j = 0) (hAd : A i i = 1) (hBd : B j j = 1)
    (hmid : ∀ k, i < k → k < j → B k j = 0) : (A * B) i j = A i j + B i j := by
  rw [Matrix.mul_apply, Finset.sum_eq_add_of_mem i j (Finset.mem_univ _) (Finset.mem_univ _) hij.ne,
    hAd, hBd, one_mul, mul_one, add_comm]
  rintro k - ⟨hki, hkj⟩
  rcases lt_trichotomy k i with h | h | h
  · rw [hA k h, zero_mul]
  · exact absurd h hki
  · rcases lt_trichotomy k j with h' | h' | h'
    · rw [hmid k h h', mul_zero]
    · exact absurd h' hkj
    · rw [hB k h', mul_zero]

private theorem testBit_codeOf_mul {g x : ↥(StatedSL 5 (ZMod 2))} (hg : g ∈ unitri5) (hx : x ∈ unitri5)
    {p : ℕ} (hp : p < 10) (hhigh : ∀ q, p < q → (codeOf x).testBit q = false) :
    (codeOf (g * x)).testBit p = xor ((codeOf g).testBit p) ((codeOf x).testBit p) := by
  have hmid : ∀ k, D35Chk.upI p < k → k < D35Chk.upJ p → mat x k (D35Chk.upJ p) = 0 := by
    intro k hk1 hk2
    obtain ⟨q, hq10, hpq, hqi, hqj⟩ := exists_upPos_of_between p hp k hk1 hk2
    have hb := hhigh q hpq
    rw [codeOf, testBit_codeOfMat _ hq10, hqi, hqj] at hb
    exact zmod2_eq_zero_of_decide _ hb
  simp only [codeOf]
  rw [testBit_codeOfMat _ hp, testBit_codeOfMat _ hp, testBit_codeOfMat _ hp, B5.Ln.mat_mul,
    mul_apply_of_upper (upPos_row_lt_col p hp) (fun k hk => mem_unitri5.1 hg _ _ hk)
      (fun k hk => mem_unitri5.1 hx _ _ hk) (mat_diag_of_mem_unitri5 hg _) (mat_diag_of_mem_unitri5 hx _) hmid]
  exact zmod2_decide_add _ _

theorem codeOf_mul_lt {g x : ↥(StatedSL 5 (ZMod 2))} (hg : g ∈ unitri5) (hx : x ∈ unitri5)
    (hx1 : x ≠ 1) (hbit : (codeOf g).testBit (Nat.log2 (codeOf x)) = true) :
    codeOf (g * x) < codeOf g := by
  have hc0 : codeOf x ≠ 0 := fun h => hx1 (eq_one_of_codeOf_eq_zero hx h)
  have ht10 : Nat.log2 (codeOf x) < 10 := (Nat.log2_lt hc0).2 ((codeOf_lt x).trans_eq (by decide))
  have hhigh : ∀ q, Nat.log2 (codeOf x) < q → (codeOf x).testBit q = false := fun q hq =>
    Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le Nat.lt_log2_self (Nat.pow_le_pow_right (by decide) hq))
  have key : ∀ p, Nat.log2 (codeOf x) ≤ p → p < 10 →
      (codeOf (g * x)).testBit p = xor ((codeOf g).testBit p) ((codeOf x).testBit p) :=
    fun p hp hp10 => testBit_codeOf_mul hg hx hp10 fun q hq => hhigh q (Nat.lt_of_le_of_lt hp hq)
  refine Nat.lt_of_testBit (Nat.log2 (codeOf x)) ?_ hbit fun j hj => ?_
  · rw [key _ (Nat.le_refl _) ht10, hbit, Nat.testBit_log2 hc0, Bool.xor_self]
  · by_cases hj10 : j < 10
    · rw [key j (Nat.le_of_lt hj) hj10, hhigh j hj, Bool.xor_false]
    · have h1024 : 1024 ≤ 2 ^ j :=
        (show 1024 = 2 ^ 10 by decide).trans_le (Nat.pow_le_pow_right (by decide) (Nat.le_of_not_lt hj10))
      rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (codeOf_lt _) h1024),
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (codeOf_lt _) h1024)]

private theorem kerMask_testBit_of_colSum_eq_zero {col : ℕ → ℕ} {c : ℕ} (hc : c < 1024)
    (h : D35Chk.colSum col c = 0) : (D35Chk.kerMask (D35Chk.packRows col)).testBit c = true :=
  (D35Chk.kerMask_testBit col c).2 ⟨hc, fun u _ => by rw [h, Nat.zero_testBit]⟩

private theorem colSum_eq_zero_of_bm {col : ℕ → ℕ} (hcol : ∀ p, col p < 2 ^ 25) {c : ℕ}
    (h : D35Chk.bm (D35Chk.colSum col c) = 0) : D35Chk.colSum col c = 0 :=
  D35Chk.bm_inj (D35Chk.colSum_lt hcol c) (Nat.two_pow_pos 25) (h.trans D35Chk.bm_zero.symm)

theorem testBit_commCol {g h : ↥(StatedSL 5 (ZMod 2))} (hg : g ∈ unitri5) (hh : h ∈ unitri5)
    (hc : g * h = h * g) :
    (D35Chk.kerMask (D35Chk.packRows (D35Chk.commCol (codeOf g)))).testBit (codeOf h) = true := by
  refine kerMask_testBit_of_colSum_eq_zero (codeOf_lt h) (colSum_eq_zero_of_bm (fun p => ?_) ?_)
  · unfold D35Chk.commCol
    rw [Nat.xor_eq]
    exact Nat.xor_lt_two_pow (D35Chk.bmul_lt _ _) (D35Chk.bmul_lt _ _)
  · have hH : mat h = 1 + D35Chk.bm (D35Chk.upSum (codeOf h)) := by
      rw [← bm_unitri_codeOf hh, D35Chk.bm_unitri]
    have hc' : mat g * mat h = mat h * mat g := by rw [← B5.Ln.mat_mul, hc, B5.Ln.mat_mul]
    rw [hH, mul_add, add_mul, mul_one, one_mul] at hc'
    rw [D35Chk.bm_colSum_commCol, bm_unitri_codeOf hg, add_left_cancel hc']
    exact mat5_add_self _

theorem testBit_fixCol {g : ↥(StatedSL 5 (ZMod 2))} (hg : g ∈ unitri5) {B : ↥(altMat 5)}
    (hfix : mat g * (B : Matrix (Fin 5) (Fin 5) (ZMod 2)) * (mat g)ᵀ = B) :
    (D35Chk.kerMask (D35Chk.packRows (D35Chk.fixCol (codeOf g)))).testBit
      (D35Chk.codeOfMat (B : Matrix (Fin 5) (Fin 5) (ZMod 2))) = true := by
  refine kerMask_testBit_of_colSum_eq_zero (codeOfMat_lt _) (colSum_eq_zero_of_bm (fun p => ?_) ?_)
  · unfold D35Chk.fixCol
    rw [Nat.xor_eq]
    exact Nat.xor_lt_two_pow (D35Chk.bmul_lt _ _) (D35Chk.altE_lt p)
  · rw [D35Chk.bm_colSum_fixCol, bm_unitri_codeOf hg, bm_altSum_codeOfMat B.2, hfix]
    exact mat5_add_self _

theorem testBit_fixColD {g : ↥(StatedSL 5 (ZMod 2))} (hg : g ∈ unitri5) (hsq : g * g = 1)
    {B : ↥(altMat 5)}
    (hfix : dmat g * (B : Matrix (Fin 5) (Fin 5) (ZMod 2)) * (dmat g)ᵀ = B) :
    (D35Chk.kerMask (D35Chk.packRows (D35Chk.fixColD (codeOf g)))).testBit
      (D35Chk.codeOfMat (B : Matrix (Fin 5) (Fin 5) (ZMod 2))) = true := by
  have hd : dmat g = (mat g)ᵀ := by rw [dmat, inv_eq_of_mul_eq_one_right hsq]
  rw [hd, Matrix.transpose_transpose] at hfix
  refine kerMask_testBit_of_colSum_eq_zero (codeOfMat_lt _) (colSum_eq_zero_of_bm (fun p => ?_) ?_)
  · unfold D35Chk.fixColD
    rw [Nat.xor_eq]
    exact Nat.xor_lt_two_pow (D35Chk.bmul_lt _ _) (D35Chk.altE_lt p)
  · rw [D35Chk.bm_colSum_fixColD, bm_unitri_codeOf hg, bm_altSum_codeOfMat B.2, hfix]
    exact mat5_add_self _

end CFSG.Quasithin
