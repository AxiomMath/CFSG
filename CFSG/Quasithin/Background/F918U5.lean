module

public import CFSG.Quasithin.Background.F918T6
public import CFSG.Quasithin.Background.F918U3

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open scoped Matrix

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique
open CFSG.Quasithin.B5.Ln (mat dmat)

@[expose] def codeOf (g : ↥(StatedSL 5 (ZMod 2))) : ℕ := D35Chk.codeOfMat (mat g)

private theorem foldr_digits_lt (n : ℕ) :
    ∀ b : ℕ → ℕ, (∀ p, b p ≤ 1) → (List.range n).foldr (fun p acc => 2 * acc + b p) 0 < 2 ^ n := by
  induction n with
  | zero => intro b _; simp
  | succ n ih =>
    intro b hb
    simp only [List.range_succ_eq_map, List.foldr_cons, List.foldr_map, Nat.succ_eq_add_one]
    have h1 : (List.range n).foldr (fun x y => 2 * y + b (x + 1)) 0 < 2 ^ n :=
      ih (fun p => b (p + 1)) (fun p => hb (p + 1))
    have h0 := hb 0
    rw [Nat.pow_succ]
    omega

private theorem testBit_foldr_digits (n : ℕ) :
    ∀ b : ℕ → ℕ, (∀ p, b p ≤ 1) → ∀ k < n,
      ((List.range n).foldr (fun p acc => 2 * acc + b p) 0).testBit k = decide (b k = 1) := by
  induction n with
  | zero => intro b _ k hk; exact absurd hk (Nat.not_lt_zero k)
  | succ n ih =>
    intro b hb k hk
    simp only [List.range_succ_eq_map, List.foldr_cons, List.foldr_map, Nat.succ_eq_add_one]
    have h0 := hb 0
    cases k with
    | zero =>
      rw [Nat.testBit_zero, decide_eq_decide]
      omega
    | succ k =>
      rw [Nat.testBit_add_one]
      have e : (2 * (List.range n).foldr (fun x y => 2 * y + b (x + 1)) 0 + b 0) / 2 =
          (List.range n).foldr (fun x y => 2 * y + b (x + 1)) 0 := by omega
      rw [e]
      exact ih (fun p => b (p + 1)) (fun p => hb (p + 1)) k (by omega)

private theorem chkBit_eq_ite (a k : ℕ) : D35Chk.bit a k = if a.testBit k then 1 else 0 := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  simp only [D35Chk.bit, Nat.land_eq, Nat.shiftRight_eq', Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]
  rcases Nat.mod_two_eq_zero_or_one (a / 2 ^ k) with h | h <;> simp [h]

private theorem upI_lt_upJ : ∀ p < 10, D35Chk.upI p < D35Chk.upJ p := by decide

private theorem exists_upI_upJ :
    ∀ i j : Fin 5, i < j → ∃ p < 10, D35Chk.upI p = i ∧ D35Chk.upJ p = j := by decide

private theorem not_upper_of_le {i j : Fin 5} (h : j ≤ i) :
    ∀ p < 10, ¬ (i = D35Chk.upI p ∧ j = D35Chk.upJ p) := by
  rintro p hp ⟨rfl, rfl⟩
  exact absurd (upI_lt_upJ p hp) (not_lt.2 h)

theorem testBit_codeOfMat (A : Matrix (Fin 5) (Fin 5) (ZMod 2)) {p : ℕ} (hp : p < 10) :
    (D35Chk.codeOfMat A).testBit p = decide (A (D35Chk.upI p) (D35Chk.upJ p) = 1) := by
  have hb : ∀ q, (A (D35Chk.upI q) (D35Chk.upJ q)).val ≤ 1 := fun q => Nat.le_of_lt_succ (ZMod.val_lt _)
  refine (testBit_foldr_digits 10 _ hb p hp).trans ?_
  show decide ((A (D35Chk.upI p) (D35Chk.upJ p)).val = 1) = decide (A (D35Chk.upI p) (D35Chk.upJ p) = 1)
  generalize A (D35Chk.upI p) (D35Chk.upJ p) = x
  revert x
  decide

theorem codeOfMat_lt (A : Matrix (Fin 5) (Fin 5) (ZMod 2)) : D35Chk.codeOfMat A < 1024 :=
  foldr_digits_lt 10 _ fun _ => Nat.le_of_lt_succ (ZMod.val_lt _)

private theorem cast_bit_codeOfMat (A : Matrix (Fin 5) (Fin 5) (ZMod 2)) {p : ℕ} (hp : p < 10) :
    ((D35Chk.bit (D35Chk.codeOfMat A) p : ℕ) : ZMod 2) = A (D35Chk.upI p) (D35Chk.upJ p) := by
  rw [chkBit_eq_ite, testBit_codeOfMat A hp]
  generalize A (D35Chk.upI p) (D35Chk.upJ p) = x
  revert x
  decide

theorem mat_diag_of_mem_unitri5 {g : ↥(StatedSL 5 (ZMod 2))} (hg : g ∈ unitri5) (i : Fin 5) :
    mat g i i = 1 := by
  have hT : (mat g).IsUpperTriangular := fun i j hji => hg i j hji
  have hdet : (mat g).det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det (B5.Ln.mat_mul_inv g)
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this
  rw [Matrix.det_of_isUpperTriangular hT] at hdet
  have hi : mat g i i ≠ 0 := Finset.prod_ne_zero_iff.1 hdet i (Finset.mem_univ i)
  have h01 : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by decide
  exact h01 _ hi

theorem bm_unitri_codeOfMat {A : Matrix (Fin 5) (Fin 5) (ZMod 2)} (hd : ∀ i, A i i = 1)
    (hl : ∀ i j, j < i → A i j = 0) : D35Chk.bm (D35Chk.unitri (D35Chk.codeOfMat A)) = A := by
  rw [D35Chk.bm_unitri]
  ext i j
  rw [Matrix.add_apply]
  rcases lt_trichotomy i j with h | rfl | h
  · obtain ⟨p, hp, rfl, rfl⟩ := exists_upI_upJ i j h
    rw [D35Chk.bm_upSum_upper _ hp, cast_bit_codeOfMat A hp, Matrix.one_apply_ne (ne_of_lt h), zero_add]
  · rw [D35Chk.bm_upSum_eq_zero _ (not_upper_of_le le_rfl), Matrix.one_apply_eq, add_zero, hd]
  · rw [D35Chk.bm_upSum_eq_zero _ (not_upper_of_le h.le), Matrix.one_apply_ne (ne_of_gt h), add_zero,
      hl i j h]

theorem bm_unitri_codeOf {g : ↥(StatedSL 5 (ZMod 2))} (hg : g ∈ unitri5) :
    D35Chk.bm (D35Chk.unitri (codeOf g)) = mat g :=
  bm_unitri_codeOfMat (mat_diag_of_mem_unitri5 hg) (mem_unitri5.1 hg)

theorem codeOf_lt (g : ↥(StatedSL 5 (ZMod 2))) : codeOf g < 1024 :=
  codeOfMat_lt (mat g)

theorem codeOf_inj {g h : ↥(StatedSL 5 (ZMod 2))} (hg : g ∈ unitri5) (hh : h ∈ unitri5)
    (e : codeOf g = codeOf h) : g = h := by
  apply B5.Ln.mat_injective
  rw [← bm_unitri_codeOf hg, ← bm_unitri_codeOf hh, e]

private theorem chkUnitri_zero : D35Chk.unitri 0 = D35Chk.idm := by decide

theorem eq_one_of_codeOf_eq_zero {g : ↥(StatedSL 5 (ZMod 2))} (hg : g ∈ unitri5)
    (h : codeOf g = 0) : g = 1 := by
  apply B5.Ln.mat_injective
  rw [← bm_unitri_codeOf hg, h, chkUnitri_zero, D35Chk.bm_idm, B5.Ln.mat_one]

theorem isInv_codeOf {g : ↥(StatedSL 5 (ZMod 2))} (hg : g ∈ unitri5) (hsq : g * g = 1) (h1 : g ≠ 1) :
    D35Chk.isInv (codeOf g) = true := by
  have h0 : codeOf g ≠ 0 := fun h => h1 (eq_one_of_codeOf_eq_zero hg h)
  have hsq' : D35Chk.bmul (D35Chk.unitri (codeOf g)) (D35Chk.unitri (codeOf g)) = D35Chk.idm := by
    apply D35Chk.bm_inj (D35Chk.bmul_lt _ _) D35Chk.idm_lt
    rw [D35Chk.bm_bmul, bm_unitri_codeOf hg, ← B5.Ln.mat_mul, hsq, B5.Ln.mat_one, D35Chk.bm_idm]
  unfold D35Chk.isInv
  rw [hsq', Nat.beq_refl, Bool.and_true]
  cases hb : Nat.beq (codeOf g) 0
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true hb) h0

theorem bm_altSum_codeOfMat {B : Matrix (Fin 5) (Fin 5) (ZMod 2)} (hB : B ∈ altMat 5) :
    D35Chk.bm (D35Chk.altSum (D35Chk.codeOfMat B)) = B := by
  obtain ⟨hT, hdiag⟩ := mem_altMat.1 hB
  ext i j
  rcases lt_trichotomy i j with h | rfl | h
  · obtain ⟨p, hp, rfl, rfl⟩ := exists_upI_upJ i j h
    rw [D35Chk.bm_altSum_upper _ hp, cast_bit_codeOfMat B hp]
  · rw [D35Chk.bm_altSum_diag, hdiag]
  · obtain ⟨p, hp, rfl, rfl⟩ := exists_upI_upJ j i h
    rw [D35Chk.bm_altSum_lower _ hp, cast_bit_codeOfMat B hp]
    have hs := congrFun (congrFun hT (D35Chk.upJ p)) (D35Chk.upI p)
    rw [Matrix.transpose_apply] at hs
    exact hs

end CFSG.Quasithin
