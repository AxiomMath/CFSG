module

public import CFSG.RepresentationTheory.SzMartineau.Expand
public import CFSG.RepresentationTheory.SzMartineau.Weights
public import CFSG.RepresentationTheory.SzMartineau.Linearized

public section

open scoped CharTwo

namespace CFSG.RepresentationTheory.SzMartineau

open CFSG.Open CFSG.RankThree.GF2n.SzExplicit CFSG.CGT.PushingUpLit.SolKNA Matrix

@[expose] def szWtInt (a : ℕ) : Fin 4 → ℤ := ![1 + 2 ^ a, 2 ^ a, -2 ^ a, -(1 + 2 ^ a)]

private lemma int_pow_two_eq_natCast (a : ℕ) : (2 : ℤ) ^ a = ((2 ^ a : ℕ) : ℤ) :=
  (Int.natCast_pow 2 a).symm

private lemma szWtInt_apply (a : ℕ) (i : Fin 4) :
    szWtInt a i = match i with
      | 0 => ((1 + 2 ^ a : ℕ) : ℤ)
      | 1 => ((2 ^ a : ℕ) : ℤ)
      | 2 => -((2 ^ a : ℕ) : ℤ)
      | 3 => -((1 + 2 ^ a : ℕ) : ℤ) := by
  fin_cases i <;>
    simp only [szWtInt, int_pow_two_eq_natCast, Matrix.cons_val_zero',
      Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons]
  all_goals push_cast
  all_goals ring

private lemma torusMat_diag_apply (a : ℕ) (x : (F a)ˣ) (i : Fin 4) :
    torusMat a x i i = (x : F a) ^ szWtInt a i := by
  fin_cases i
  · change torusMat a x 0 0 = (x : F a) ^ szWtInt a 0
    rw [szWtInt_apply, zpow_natCast]
    simp [torusMat]
  · change torusMat a x 1 1 = (x : F a) ^ szWtInt a 1
    rw [szWtInt_apply, zpow_natCast]
    simp [torusMat]
  · change torusMat a x 2 2 = (x : F a) ^ szWtInt a 2
    rw [szWtInt_apply, _root_.zpow_neg, zpow_natCast]
    simp [torusMat]
  · change torusMat a x 3 3 = (x : F a) ^ szWtInt a 3
    rw [szWtInt_apply, _root_.zpow_neg, zpow_natCast]
    simp [torusMat]

private lemma torusMat_eq_diagonal_zpow (a : ℕ) (x : (F a)ˣ) :
    torusMat a x = Matrix.diagonal (fun i => (x : F a) ^ szWtInt a i) := by
  ext i j
  by_cases hij : i = j
  · subst hij
    rw [Matrix.diagonal_apply_eq, torusMat_diag_apply]
  · rw [Matrix.diagonal_apply_ne _ hij]
    fin_cases i <;> fin_cases j <;> simp_all [torusMat]

theorem torusMat_mul_mul_torusMat_inv_apply {a c : ℕ} (x : (F a)ˣ)
    (A : Matrix (Fin 4) (Fin 4) (F a)) (i j : Fin 4) :
    (torusMat a x * A * torusMat a (x ^ 2 ^ c)⁻¹) i j =
      (x : F a) ^ (szWtInt a i - 2 ^ c * szWtInt a j) * A i j := by
  rw [torusMat_eq_diagonal_zpow (x := x),
    torusMat_eq_diagonal_zpow (x := (x ^ 2 ^ c)⁻¹),
    Matrix.mul_diagonal, Matrix.diagonal_mul]
  have h1 : (((x ^ 2 ^ c)⁻¹ : (F a)ˣ) : F a) = (x : F a) ^ (-(2 ^ c : ℤ)) := by
    rw [Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, ← zpow_natCast,
      ← _root_.zpow_neg]
    congr 1
  have hy : (((x ^ 2 ^ c)⁻¹ : (F a)ˣ) : F a) ^ szWtInt a j =
      (x : F a) ^ (-(2 ^ c * szWtInt a j)) := by
    rw [h1, ← _root_.zpow_mul]
    congr 1
    ring
  rw [hy]
  have h : (x : F a) ^ szWtInt a i * (x : F a) ^ (-(2 ^ c * szWtInt a j)) =
      (x : F a) ^ (szWtInt a i - 2 ^ c * szWtInt a j) := by
    rw [← zpow_add₀ (x.ne_zero), sub_eq_add_neg]
  calc (x : F a) ^ szWtInt a i * A i j * (x : F a) ^ (-(2 ^ c * szWtInt a j))
      = ((x : F a) ^ szWtInt a i *
          (x : F a) ^ (-(2 ^ c * szWtInt a j))) * A i j := by ring
    _ = (x : F a) ^ (szWtInt a i - 2 ^ c * szWtInt a j) * A i j := by rw [h]

theorem intCast_szWtInt_sub {a c : ℕ} (i j : Fin 4) :
    ((szWtInt a i - 2 ^ c * szWtInt a j : ℤ) : ZMod (2 ^ (2 * a + 1) - 1)) =
      posWt a c i j := by
  fin_cases i <;> fin_cases j <;>
    simp [szWtInt, szWt, posWt, ← Int.natCast_pow]
  all_goals push_cast
  all_goals ring

private lemma mul_apply_of_level_eq {K : Type*} [CommRing K]
    {U M : Matrix (Fin 4) (Fin 4) K}
    (hU0 : ∀ i j : Fin 4, j < i → U i j = 0) (hU1 : ∀ i : Fin 4, U i i = 1)
    {L : ℤ} (hM : ∀ i j : Fin 4, (j : ℤ) - i < L → M i j = 0)
    {i j : Fin 4} (hij : (j : ℤ) - i = L) : (U * M) i j = M i j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · rw [hU1, one_mul]
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with hki | hik
    · rw [hU0 i k hki, zero_mul]
    · have hkL : (j : ℤ) - k < L := by
        have hik' : (i : ℤ) < (k : ℤ) := by exact_mod_cast hik
        omega
      rw [hM k j hkL, mul_zero]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

private lemma mul_apply_of_level_eq_right {K : Type*} [CommRing K]
    {U M : Matrix (Fin 4) (Fin 4) K}
    (hU0 : ∀ i j : Fin 4, j < i → U i j = 0) (hU1 : ∀ i : Fin 4, U i i = 1)
    {L : ℤ} (hM : ∀ i j : Fin 4, (j : ℤ) - i < L → M i j = 0)
    {i j : Fin 4} (hij : (j : ℤ) - i = L) : (M * U) i j = M i j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single j]
  · rw [hU1, mul_one]
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with hkj | hjk
    · have hkL : (k : ℤ) - i < L := by
        have hkj' : (k : ℤ) < (j : ℤ) := by exact_mod_cast hkj
        omega
      rw [hM i k hkL, zero_mul]
    · rw [hU0 k j hjk, mul_zero]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

private lemma mul_apply_of_level_lt {K : Type*} [CommRing K]
    {U M : Matrix (Fin 4) (Fin 4) K}
    (hU0 : ∀ i j : Fin 4, j < i → U i j = 0) (hU1 : ∀ i : Fin 4, U i i = 1)
    {L : ℤ} (hM : ∀ i j : Fin 4, (j : ℤ) - i < L → M i j = 0)
    {i j : Fin 4} (hij : (j : ℤ) - i < L) : (U * M) i j = 0 := by
  rw [Matrix.mul_apply, Finset.sum_eq_zero]
  intro k _
  rcases le_or_gt i k with hik | hki
  · rcases eq_or_lt_of_le hik with h | h
    · subst k
      rw [hU1, one_mul, hM i j hij]
    · have hkL : (j : ℤ) - k < L := by
        have hik' : (i : ℤ) < (k : ℤ) := by exact_mod_cast h
        omega
      rw [hM k j hkL, mul_zero]
  · rw [hU0 i k hki, zero_mul]

private lemma mul_apply_of_level_lt_right {K : Type*} [CommRing K]
    {U M : Matrix (Fin 4) (Fin 4) K}
    (hU0 : ∀ i j : Fin 4, j < i → U i j = 0) (hU1 : ∀ i : Fin 4, U i i = 1)
    {L : ℤ} (hM : ∀ i j : Fin 4, (j : ℤ) - i < L → M i j = 0)
    {i j : Fin 4} (hij : (j : ℤ) - i < L) : (M * U) i j = 0 := by
  rw [Matrix.mul_apply, Finset.sum_eq_zero]
  intro k _
  rcases le_or_gt k j with hkj | hjk
  · rcases eq_or_lt_of_le hkj with h | h
    · subst k
      rw [hU1, mul_one, hM i j hij]
    · have hkL : (k : ℤ) - i < L := by
        have hkj' : (k : ℤ) < (j : ℤ) := by exact_mod_cast h
        omega
      rw [hM i k hkL, zero_mul]
  · rw [hU0 k j hjk, mul_zero]

private lemma rootMat_upper (a : ℕ) (α β : F a) :
    ∀ i j : Fin 4, j < i → rootMat a α β i j = 0 := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [rootMat]

private lemma rootMat_diag (a : ℕ) (α β : F a) (i : Fin 4) :
    rootMat a α β i i = 1 := by
  fin_cases i <;> simp [rootMat]

private lemma rootMat_one_zero_mul_add_mul_apply_eq_zero {a : ℕ}
    {A : Matrix (Fin 4) (Fin 4) (F a)} {L : ℤ}
    (hA : ∀ i j : Fin 4, (j : ℤ) - i < L → A i j = 0)
    {i j : Fin 4} (hij : (j : ℤ) - i ≤ L) :
    (rootMat a 1 0 * A + A * rootMat a 1 0) i j = 0 := by
  have hU0 := rootMat_upper a 1 0
  have hU1 := rootMat_diag a 1 0
  rcases lt_or_eq_of_le hij with hlt | heq
  · rw [Matrix.add_apply,
        mul_apply_of_level_lt hU0 hU1 hA hlt,
        mul_apply_of_level_lt_right hU0 hU1 hA hlt]
    simp
  · rw [Matrix.add_apply,
        mul_apply_of_level_eq hU0 hU1 hA heq,
        mul_apply_of_level_eq_right hU0 hU1 hA heq]
    exact CharTwo.add_self_eq_zero _

variable {a c : ℕ} {Y : ↥(Sz a) → Matrix (Fin 4) (Fin 4) (F a)}

private lemma apply_rootSz_apply_of_ne_zero (hY : IsTwistedCocycle (natHom a) (twHom a c) Y)
    (hT : ∀ x, Y (torusSz a x) = 0) {x : F a} (hx : x ≠ 0) (i j : Fin 4) :
    Y (rootSz a x 0) i j =
      x ^ (szWtInt a i - 2 ^ c * szWtInt a j) * Y (rootSz a 1 0) i j := by
  have h := hY.apply_rootSz_unit hT (Units.mk0 x hx)
  rw [Units.val_mk0] at h
  have h' := congrFun (congrFun h i) j
  rw [torusMat_mul_mul_torusMat_inv_apply, Units.val_mk0] at h'
  exact h'

private lemma apply_rootSz_apply_eq_zero_of_lt (hY : IsTwistedCocycle (natHom a) (twHom a c) Y)
    (hT : ∀ x, Y (torusSz a x) = 0) {L : ℤ}
    (hL : ∀ i j : Fin 4, (j : ℤ) - i < L → Y (rootSz a 1 0) i j = 0)
    {α : F a} {i j : Fin 4} (hij : (j : ℤ) - i < L) :
    Y (rootSz a α 0) i j = 0 := by
  by_cases hα : α = 0
  · subst hα
    have h00 : rootSz a 0 0 = 1 := Subtype.ext (Units.ext rootMat_zero_zero)
    rw [h00, hY.map_one]
    simp
  · rw [apply_rootSz_apply_of_ne_zero hY hT hα, hL i j hij, mul_zero]

private lemma apply_rootSz_zero_apply_eq_zero_of_le
    (hY : IsTwistedCocycle (natHom a) (twHom a c) Y)
    (hT : ∀ x, Y (torusSz a x) = 0) {L : ℤ}
    (hL : ∀ i j : Fin 4, (j : ℤ) - i < L → Y (rootSz a 1 0) i j = 0)
    {β : F a} {i j : Fin 4} (hij : (j : ℤ) - i ≤ L) :
    Y (rootSz a 0 β) i j = 0 := by
  by_cases hβ : β = 0
  · subst hβ
    have h00 : rootSz a 0 0 = 1 := Subtype.ext (Units.ext rootMat_zero_zero)
    rw [h00, hY.map_one]
    simp
  · obtain ⟨y, hy⟩ := exists_pow_one_add_theta (a := a) β
    have hy0 : y ≠ 0 := by
      rintro rfl
      rw [zero_pow (by positivity : 1 + 2 ^ (a + 1) ≠ 0)] at hy
      exact hβ hy.symm
    have h := hY.apply_rootSz_zero_unit hT (Units.mk0 y hy0)
    rw [Units.val_mk0, hy] at h
    have h01 := hY.apply_rootSz_zero_one
    rw [h, h01, torusMat_mul_mul_torusMat_inv_apply]
    have hz : (rootMat a 1 0 * Y (rootSz a 1 0) +
        Y (rootSz a 1 0) * rootMat a 1 0) i j = 0 :=
      rootMat_one_zero_mul_add_mul_apply_eq_zero hL hij
    rw [hz, mul_zero]

theorem IsTwistedCocycle.apply_rootSz_add_apply (hY : IsTwistedCocycle (natHom a) (twHom a c) Y)
    (hT : ∀ x, Y (torusSz a x) = 0) {L : ℤ}
    (hL : ∀ i j : Fin 4, (j : ℤ) - i < L → Y (rootSz a 1 0) i j = 0)
    {i j : Fin 4} (hij : (j : ℤ) - i = L) (α γ : F a) :
    Y (rootSz a (α + γ) 0) i j = Y (rootSz a α 0) i j + Y (rootSz a γ 0) i j := by
  have hrel := hY.apply_rootSz_add α γ
  have h := congrFun (congrFun hrel i) j
  have h1 : (rootMat a α 0 * Y (rootSz a γ 0)) i j = Y (rootSz a γ 0) i j :=
    mul_apply_of_level_eq (rootMat_upper a α 0) (rootMat_diag a α 0)
      (fun i j hij' => apply_rootSz_apply_eq_zero_of_lt hY hT hL hij') hij
  have h2 : (Y (rootSz a α 0) * rootMat a (γ ^ 2 ^ c) 0) i j = Y (rootSz a α 0) i j :=
    mul_apply_of_level_eq_right (rootMat_upper a (γ ^ 2 ^ c) 0)
      (rootMat_diag a (γ ^ 2 ^ c) 0)
      (fun i j hij' => apply_rootSz_apply_eq_zero_of_lt hY hT hL hij') hij
  have h3 : (rootMat a (α + γ) 0 * Y (rootSz a 0 (α * γ ^ 2 ^ (a + 1)))) i j = 0 := by
    rw [mul_apply_of_level_eq (rootMat_upper a (α + γ) 0) (rootMat_diag a (α + γ) 0)
      (fun i j hij' => apply_rootSz_zero_apply_eq_zero_of_le hY hT hL (le_of_lt hij')) hij]
    exact apply_rootSz_zero_apply_eq_zero_of_le hY hT hL (le_of_eq hij)
  have h4 : (Y (rootSz a (α + γ) 0) *
      rootMat a 0 ((α * γ ^ 2 ^ (a + 1)) ^ 2 ^ c)) i j = Y (rootSz a (α + γ) 0) i j :=
    mul_apply_of_level_eq_right (rootMat_upper a 0 ((α * γ ^ 2 ^ (a + 1)) ^ 2 ^ c))
      (rootMat_diag a 0 ((α * γ ^ 2 ^ (a + 1)) ^ 2 ^ c))
      (fun i j hij' => apply_rootSz_apply_eq_zero_of_lt hY hT hL hij') hij
  rw [Matrix.add_apply, Matrix.add_apply, h1, h2, h3, h4] at h
  have h' : Y (rootSz a (α + γ) 0) i j =
      Y (rootSz a γ 0) i j + Y (rootSz a α 0) i j := by
    simpa using h.symm
  rw [add_comm (Y (rootSz a α 0) i j) (Y (rootSz a γ 0) i j)]
  exact h'

theorem IsTwistedCocycle.isTwoPow_of_lowest (hY : IsTwistedCocycle (natHom a) (twHom a c) Y)
    (hT : ∀ x, Y (torusSz a x) = 0) {L : ℤ}
    (hL : ∀ i j : Fin 4, (j : ℤ) - i < L → Y (rootSz a 1 0) i j = 0)
    {i j : Fin 4} (hij : (j : ℤ) - i = L) (h0 : Y (rootSz a 1 0) i j ≠ 0) :
    IsTwoPow a (posWt a c i j) := by
  let _ : Fintype (F a) := Fintype.ofFinite _
  have hcard : Fintype.card (F a) = 2 ^ (2 * a + 1) := by
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card 2 (2 * a + 1) (by omega)
  have hadd : ∀ x y : F a, x ≠ 0 → y ≠ 0 → x + y ≠ 0 →
      (x + y) ^ (szWtInt a i - 2 ^ c * szWtInt a j) =
        x ^ (szWtInt a i - 2 ^ c * szWtInt a j) +
          y ^ (szWtInt a i - 2 ^ c * szWtInt a j) := by
    intro x y hx hy hxy
    have hxw := apply_rootSz_apply_of_ne_zero hY hT hx i j
    have hyw := apply_rootSz_apply_of_ne_zero hY hT hy i j
    have hxyw := apply_rootSz_apply_of_ne_zero hY hT hxy i j
    have h := hY.apply_rootSz_add_apply hT hL hij x y
    rw [hxw, hyw, hxyw] at h
    have hmul : (x + y) ^ (szWtInt a i - 2 ^ c * szWtInt a j) *
        Y (rootSz a 1 0) i j =
        (x ^ (szWtInt a i - 2 ^ c * szWtInt a j) +
          y ^ (szWtInt a i - 2 ^ c * szWtInt a j)) * Y (rootSz a 1 0) i j := by
      rw [add_mul]
      exact h
    exact mul_right_cancel₀ h0 hmul
  obtain ⟨k, hk⟩ := exists_two_pow_of_zpow_add (K := F a) hcard
    (szWtInt a i - 2 ^ c * szWtInt a j) hadd
  exact ⟨k, by rw [← intCast_szWtInt_sub]; exact hk⟩

private lemma units_pow_two_pow_eq_self {a c : ℕ} (hc : (2 * a + 1) ∣ c)
    (x : (F a)ˣ) : x ^ 2 ^ c = x := by
  let _ : Fintype (F a) := Fintype.ofFinite _
  obtain ⟨k, rfl⟩ := hc
  have hcard : Fintype.card (F a) = 2 ^ (2 * a + 1) := by
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card 2 (2 * a + 1) (by omega)
  ext
  rw [Units.val_pow_eq_pow_val]
  rw [show (2 : ℕ) ^ ((2 * a + 1) * k) = (2 ^ (2 * a + 1)) ^ k from
    pow_mul 2 (2 * a + 1) k]
  rw [← hcard]
  exact FiniteField.pow_card_pow k (x : F a)

private noncomputable def szXFormula (a : ℕ) (X : Matrix (Fin 4) (Fin 4) (F a)) :
    Matrix (Fin 4) (Fin 4) (F a) :=
  !![X 0 3 + X 1 0, X 0 0 + X 0 2 + X 1 1, X 1 2, X 0 1 + X 0 2 + X 1 3;
     X 0 3 + X 1 3, X 0 2 + X 1 0 + X 1 2, X 0 1, X 0 0 + X 1 1 + X 1 2;
     X 0 3, X 0 2 + X 1 3, X 0 1 + X 1 2, X 0 0 + X 1 1 + X 1 2 + X 1 3;
     0, X 0 3, X 0 2, X 0 1 + X 0 2 + X 0 3]

private lemma rootSz_one_zero_eq_szXFormula {a : ℕ}
    {Y : ↥(Sz a) → Matrix (Fin 4) (Fin 4) (F a)}
    {X : Matrix (Fin 4) (Fin 4) (F a)}
    (hXJ : wMat a * X = X * wMat a)
    (hA : Y (rootSz a 1 0) = rootMat a 1 0 * X + X * rootMat a 1 0) :
    Y (rootSz a 1 0) = szXFormula a X := by
  have hx₀ : rootMat a 1 0 = szX₀ := by
    rw [rootMat_one_zero]
    rfl
  have hJ : wMat a = szJ := rfl
  have hXJ' : szJ * X = X * szJ := by
    rw [← hJ]
    exact hXJ
  rw [hA, hx₀]
  exact szX₀_mul_add_mul_szX₀ hXJ'

private lemma level_neg_two_eq_zero {a c : ℕ}
    {Y : ↥(Sz a) → Matrix (Fin 4) (Fin 4) (F a)}
    (ha : 2 ≤ a) (hY : IsTwistedCocycle (natHom a) (twHom a c) Y)
    (hT : ∀ x, Y (torusSz a x) = 0) {X : Matrix (Fin 4) (Fin 4) (F a)}
    (hformula : Y (rootSz a 1 0) = szXFormula a X) :
    X 0 3 = 0 := by
  have hL : ∀ i j : Fin 4, (j : ℤ) - i < -2 → Y (rootSz a 1 0) i j = 0 := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [hformula, szXFormula] at hij ⊢
  have hA20 : Y (rootSz a 1 0) 2 0 = X 0 3 := by
    rw [hformula]
    simp [szXFormula]
  by_contra h3
  have h0 : Y (rootSz a 1 0) 2 0 ≠ 0 := by rwa [hA20]
  have h := hY.isTwoPow_of_lowest hT hL (i := 2) (j := 0) (by norm_num) h0
  exact not_isTwoPow_posWt_two_zero ha c h

private lemma level_neg_one_eq_zero {a c : ℕ}
    {Y : ↥(Sz a) → Matrix (Fin 4) (Fin 4) (F a)}
    (ha : 2 ≤ a) (hY : IsTwistedCocycle (natHom a) (twHom a c) Y)
    (hT : ∀ x, Y (torusSz a x) = 0) {X : Matrix (Fin 4) (Fin 4) (F a)}
    (hformula : Y (rootSz a 1 0) = szXFormula a X) (hp3 : X 0 3 = 0) :
    X 0 2 = 0 ∧ X 1 3 = 0 := by
  have hL : ∀ i j : Fin 4, (j : ℤ) - i < -1 → Y (rootSz a 1 0) i j = 0 := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [hformula, szXFormula, hp3] at hij ⊢
  have hA21 : Y (rootSz a 1 0) 2 1 = X 0 2 + X 1 3 := by
    rw [hformula]
    simp [szXFormula]
  have hp27 : X 0 2 + X 1 3 = 0 := by
    by_contra h
    have h0 : Y (rootSz a 1 0) 2 1 ≠ 0 := by rwa [hA21]
    have hh := hY.isTwoPow_of_lowest hT hL (i := 2) (j := 1) (by norm_num) h0
    exact not_isTwoPow_posWt_two_one ha c hh
  have hA10 : Y (rootSz a 1 0) 1 0 = X 0 3 + X 1 3 := by
    rw [hformula]
    simp [szXFormula]
  have hA32 : Y (rootSz a 1 0) 3 2 = X 0 2 := by
    rw [hformula]
    simp [szXFormula]
  have hp2eq : X 0 2 = X 1 3 := CharTwo.add_eq_zero.mp hp27
  have hp7 : X 1 3 = 0 := by
    by_contra h7
    have hA10' : Y (rootSz a 1 0) 1 0 = X 1 3 := by rw [hA10, hp3, zero_add]
    have hA32' : Y (rootSz a 1 0) 3 2 = X 1 3 := by rw [hA32, hp2eq]
    have h0a : Y (rootSz a 1 0) 1 0 ≠ 0 := by rwa [hA10']
    have h0b : Y (rootSz a 1 0) 3 2 ≠ 0 := by rwa [hA32']
    have hia := hY.isTwoPow_of_lowest hT hL (i := 1) (j := 0) (by norm_num) h0a
    have hib := hY.isTwoPow_of_lowest hT hL (i := 3) (j := 2) (by norm_num) h0b
    exact not_isTwoPow_posWt_one_zero_and_three_two ha c ⟨hia, hib⟩
  exact ⟨by rw [hp2eq, hp7], hp7⟩

private lemma level_zero_diag_data {a c : ℕ}
    {Y : ↥(Sz a) → Matrix (Fin 4) (Fin 4) (F a)}
    (ha : 2 ≤ a) (hY : IsTwistedCocycle (natHom a) (twHom a c) Y)
    (hT : ∀ x, Y (torusSz a x) = 0) {X : Matrix (Fin 4) (Fin 4) (F a)}
    (hformula : Y (rootSz a 1 0) = szXFormula a X)
    (hp2 : X 0 2 = 0) (hp3 : X 0 3 = 0) (hp7 : X 1 3 = 0) :
    (∀ i j : Fin 4, i ≠ j →
      Y (rootSz a 1 0) i i = 0 ∨ Y (rootSz a 1 0) j j = 0) ∧
      Y (rootSz a 1 0) 0 0 = X 1 0 ∧
      Y (rootSz a 1 0) 1 1 = X 1 0 + X 1 2 ∧
      Y (rootSz a 1 0) 2 2 = X 0 1 + X 1 2 ∧
      Y (rootSz a 1 0) 3 3 = X 0 1 := by
  have hL : ∀ i j : Fin 4, (j : ℤ) - i < 0 → Y (rootSz a 1 0) i j = 0 := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [hformula, szXFormula, hp2, hp3, hp7] at hij ⊢
  have hdiag : ∀ i : Fin 4, Y (rootSz a 1 0) i i ≠ 0 → IsTwoPow a (posWt a c i i) := by
    intro i hi
    exact hY.isTwoPow_of_lowest hT hL (i := i) (j := i) (by simp) hi
  have hnon : ∀ i j : Fin 4, i ≠ j →
      Y (rootSz a 1 0) i i = 0 ∨ Y (rootSz a 1 0) j j = 0 := by
    intro i j hij
    by_contra h
    push Not at h
    exact diag_isTwoPow_unique ha c hij (hdiag i h.1) (hdiag j h.2)
  have hA00 : Y (rootSz a 1 0) 0 0 = X 0 3 + X 1 0 := by
    rw [hformula]
    simp [szXFormula]
  have hA11 : Y (rootSz a 1 0) 1 1 = X 0 2 + X 1 0 + X 1 2 := by
    rw [hformula]
    simp [szXFormula]
  have hA22 : Y (rootSz a 1 0) 2 2 = X 0 1 + X 1 2 := by
    rw [hformula]
    simp [szXFormula]
  have hA33 : Y (rootSz a 1 0) 3 3 = X 0 1 + X 0 2 + X 0 3 := by
    rw [hformula]
    simp [szXFormula]
  refine ⟨hnon, ?_, ?_, ?_, ?_⟩
  · rw [hA00, hp3, zero_add]
  · rw [hA11, hp2, zero_add]
  · exact hA22
  · rw [hA33, hp2, add_zero, hp3, add_zero]

private lemma level_zero_eq_zero {a : ℕ}
    {Y : ↥(Sz a) → Matrix (Fin 4) (Fin 4) (F a)}
    {X : Matrix (Fin 4) (Fin 4) (F a)}
    (hnon : ∀ i j : Fin 4, i ≠ j →
      Y (rootSz a 1 0) i i = 0 ∨ Y (rootSz a 1 0) j j = 0)
    (hA00 : Y (rootSz a 1 0) 0 0 = X 1 0)
    (hA11 : Y (rootSz a 1 0) 1 1 = X 1 0 + X 1 2)
    (hA22 : Y (rootSz a 1 0) 2 2 = X 0 1 + X 1 2)
    (hA33 : Y (rootSz a 1 0) 3 3 = X 0 1) :
    X 0 1 = 0 ∧ X 1 0 = 0 ∧ X 1 2 = 0 := by
  have hp4 : X 1 0 = 0 := by
    by_contra h4
    have hA00n : Y (rootSz a 1 0) 0 0 ≠ 0 := by rwa [hA00]
    have h11 : Y (rootSz a 1 0) 1 1 = 0 := (hnon 0 1 (by decide)).resolve_left hA00n
    have h22 : Y (rootSz a 1 0) 2 2 = 0 := (hnon 0 2 (by decide)).resolve_left hA00n
    have h33 : Y (rootSz a 1 0) 3 3 = 0 := (hnon 0 3 (by decide)).resolve_left hA00n
    have hp1 : X 0 1 = 0 := by rw [hA33] at h33; exact h33
    have hp6 : X 1 2 = 0 := by
      have h := h22
      rw [hA22, hp1, zero_add] at h
      exact h
    have hp4' : X 1 0 = 0 := by
      have h := h11
      rw [hA11, hp6, add_zero] at h
      exact h
    exact h4 hp4'
  have hp6 : X 1 2 = 0 := by
    by_contra h6
    have hA11n : Y (rootSz a 1 0) 1 1 ≠ 0 := by rw [hA11, hp4, zero_add]; exact h6
    have h22 : Y (rootSz a 1 0) 2 2 = 0 := (hnon 1 2 (by decide)).resolve_left hA11n
    have h33 : Y (rootSz a 1 0) 3 3 = 0 := (hnon 1 3 (by decide)).resolve_left hA11n
    have hp1 : X 0 1 = 0 := by rw [hA33] at h33; exact h33
    have hp6' : X 1 2 = 0 := by
      have h := h22
      rw [hA22, hp1, zero_add] at h
      exact h
    exact h6 hp6'
  have hp1 : X 0 1 = 0 := by
    by_contra h1
    have hA22n : Y (rootSz a 1 0) 2 2 ≠ 0 := by rw [hA22, hp6, add_zero]; exact h1
    have h33 : Y (rootSz a 1 0) 3 3 = 0 := (hnon 2 3 (by decide)).resolve_left hA22n
    rw [hA33] at h33
    exact h1 h33
  exact ⟨hp1, hp4, hp6⟩

private lemma level_one_eq_zero {a c : ℕ}
    {Y : ↥(Sz a) → Matrix (Fin 4) (Fin 4) (F a)}
    (ha : 2 ≤ a) (hY : IsTwistedCocycle (natHom a) (twHom a c) Y)
    (hT : ∀ x, Y (torusSz a x) = 0) {X : Matrix (Fin 4) (Fin 4) (F a)}
    (hformula : Y (rootSz a 1 0) = szXFormula a X)
    (hp1 : X 0 1 = 0) (hp2 : X 0 2 = 0) (hp3 : X 0 3 = 0)
    (hp4 : X 1 0 = 0) (hp6 : X 1 2 = 0) (hp7 : X 1 3 = 0) :
    c % (2 * a + 1) ≠ 0 → X 0 0 + X 1 1 = 0 := by
  intro hc
  have hL : ∀ i j : Fin 4, (j : ℤ) - i < 1 → Y (rootSz a 1 0) i j = 0 := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp [hformula, szXFormula, hp1, hp2, hp3, hp4, hp6, hp7] at hij ⊢
  by_contra h05
  have hA01 : Y (rootSz a 1 0) 0 1 = X 0 0 + X 0 2 + X 1 1 := by
    rw [hformula]
    simp [szXFormula]
  have hA23 : Y (rootSz a 1 0) 2 3 = X 0 0 + X 1 1 + X 1 2 + X 1 3 := by
    rw [hformula]
    simp [szXFormula]
  have hA01' : Y (rootSz a 1 0) 0 1 = X 0 0 + X 1 1 := by rw [hA01, hp2, add_zero]
  have hA23' : Y (rootSz a 1 0) 2 3 = X 0 0 + X 1 1 := by
    rw [hA23, hp6, hp7, add_zero, add_zero]
  have h0a : Y (rootSz a 1 0) 0 1 ≠ 0 := by rwa [hA01']
  have h0b : Y (rootSz a 1 0) 2 3 ≠ 0 := by rwa [hA23']
  have hia := hY.isTwoPow_of_lowest hT hL (i := 0) (j := 1) (by norm_num) h0a
  have hib := hY.isTwoPow_of_lowest hT hL (i := 2) (j := 3) (by norm_num) h0b
  exact not_isTwoPow_posWt_zero_one_and_two_three ha hc ⟨hia, hib⟩

private lemma exists_diag_of_formula {a c : ℕ}
    {Y : ↥(Sz a) → Matrix (Fin 4) (Fin 4) (F a)}
    {X : Matrix (Fin 4) (Fin 4) (F a)}
    (hformula : Y (rootSz a 1 0) = szXFormula a X)
    (hp1 : X 0 1 = 0) (hp2 : X 0 2 = 0) (hp3 : X 0 3 = 0)
    (hp4 : X 1 0 = 0) (hp6 : X 1 2 = 0) (hp7 : X 1 3 = 0)
    (hp05 : c % (2 * a + 1) ≠ 0 → X 0 0 + X 1 1 = 0) :
    ∃ D : Matrix (Fin 4) (Fin 4) (F a),
      (∀ x : (F a)ˣ, torusMat a x * D = D * torusMat a (x ^ 2 ^ c)) ∧
        wMat a * D = D * wMat a ∧
          Y (rootSz a 1 0) = rootMat a 1 0 * D + D * rootMat a 1 0 := by
  let d : F a := X 0 0 + X 1 1
  let D : Matrix (Fin 4) (Fin 4) (F a) := Matrix.diagonal ![0, d, d, 0]
  refine ⟨D, ?_, ?_, ?_⟩
  · intro x
    by_cases hc : c % (2 * a + 1) = 0
    · have hx : x ^ 2 ^ c = x := units_pow_two_pow_eq_self (Nat.dvd_of_mod_eq_zero hc) x
      rw [show D = Matrix.diagonal ![0, d, d, 0] from rfl, hx,
        torusMat_eq_diagonal_zpow]
      exact Matrix.commute_diagonal _ _
    · have hd : d = 0 := by
        rw [show d = X 0 0 + X 1 1 from rfl]
        exact hp05 hc
      have hDzero : D = 0 := by
        rw [show D = Matrix.diagonal ![0, d, d, 0] from rfl, hd]
        ext i j
        fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]
      rw [hDzero, mul_zero, zero_mul]
  · rw [show D = Matrix.diagonal ![0, d, d, 0] from rfl]
    ext i j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    fin_cases i <;> fin_cases j <;>
      simp [wMat, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
        Matrix.head_cons, Matrix.tail_cons]
  · have hx₀ : rootMat a 1 0 = szX₀ := by
      rw [rootMat_one_zero]
      rfl
    rw [hformula, hx₀]
    rw [show D = Matrix.diagonal ![0, d, d, 0] from rfl]
    ext i j
    rw [Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]
    fin_cases i <;> fin_cases j <;>
      simp [d, szXFormula, szX₀, Matrix.cons_val_zero, Matrix.cons_val_succ,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
        Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons,
        hp1, hp2, hp3, hp4, hp6, hp7]

theorem IsTwistedCocycle.exists_diag_of_two_le (ha : 2 ≤ a)
    (hY : IsTwistedCocycle (natHom a) (twHom a c) Y) (hT : ∀ x, Y (torusSz a x) = 0)
    {X : Matrix (Fin 4) (Fin 4) (F a)} (hXJ : wMat a * X = X * wMat a)
    (hA : Y (rootSz a 1 0) = rootMat a 1 0 * X + X * rootMat a 1 0) :
    ∃ D : Matrix (Fin 4) (Fin 4) (F a),
      (∀ x : (F a)ˣ, torusMat a x * D = D * torusMat a (x ^ 2 ^ c)) ∧
        wMat a * D = D * wMat a ∧
          Y (rootSz a 1 0) = rootMat a 1 0 * D + D * rootMat a 1 0 := by
  have hformula : Y (rootSz a 1 0) = szXFormula a X :=
    rootSz_one_zero_eq_szXFormula hXJ hA
  have hp3 : X 0 3 = 0 := level_neg_two_eq_zero ha hY hT hformula
  obtain ⟨hp2, hp7⟩ := level_neg_one_eq_zero ha hY hT hformula hp3
  obtain ⟨hnon, hA00, hA11, hA22, hA33⟩ :=
    level_zero_diag_data ha hY hT hformula hp2 hp3 hp7
  obtain ⟨hp1, hp4, hp6⟩ := level_zero_eq_zero hnon hA00 hA11 hA22 hA33
  have hp05 : c % (2 * a + 1) ≠ 0 → X 0 0 + X 1 1 = 0 :=
    level_one_eq_zero ha hY hT hformula hp1 hp2 hp3 hp4 hp6 hp7
  exact exists_diag_of_formula hformula hp1 hp2 hp3 hp4 hp6 hp7 hp05

end CFSG.RepresentationTheory.SzMartineau
