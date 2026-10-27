module

public import CFSG.RankThree.PartTwo.Sec21.Hering2119SMat
public import Mathlib.RingTheory.PiTensorProduct
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering2119S

open Matrix

def allMat2 : List Mat2 :=
  [0, 1, 2].flatMap fun a => [0, 1, 2].flatMap fun b => [0, 1, 2].flatMap fun c =>
    [0, 1, 2].map fun d => !![a, b; c, d]

set_option maxRecDepth 100000 in
theorem mem_allMat2 (a : Mat2) : a ∈ allMat2 := by
  obtain ⟨p, q, r, s, rfl⟩ : ∃ p q r s : F3, a = !![p, q; r, s] :=
    ⟨_, _, _, _, Matrix.eta_fin_two a⟩
  revert p q r s
  decide +kernel

@[expose] def Q6 : List Mat2 :=
  [!![0, -1; 1, 0], !![0, 1; -1, 0], !![1, -1; -1, -1], !![-1, 1; 1, 1], !![1, 1; 1, -1],
    !![-1, -1; -1, 1]]

set_option maxRecDepth 100000 in
theorem mem_Q6 (a : Mat2) (h : a * a = -1) : a ∈ Q6 := by
  revert a
  decide +kernel

@[expose] def I2m0 : Mat2 := !![0, -1; 1, 0]

@[expose] def J2m0 : Mat2 := !![1, -1; -1, -1]

@[expose] def nU : Mat2 := !![0, 0; 1, 0]

@[simp] theorem nU_00 : nU 0 0 = 0 := rfl
@[simp] theorem nU_01 : nU 0 1 = 0 := rfl
@[simp] theorem nU_10 : nU 1 0 = 1 := rfl
@[simp] theorem nU_11 : nU 1 1 = 0 := rfl

@[expose] def uU : Mat2 := 1 + nU

@[expose] def pmul (x y : Mat2 × Mat2) : Mat2 × Mat2 := (x.1 * y.1, x.1 * y.2 + x.2 * y.1)

@[expose] def q8g {α : Type*} (m : α → α → α) (e x z : α) : List α :=
  [e, x, m x x, m (m x x) x, z, m x z, m (m x x) z, m (m (m x x) x) z]

@[expose] def q8p (I J : Mat2 × Mat2) : List (Mat2 × Mat2) :=
  [((1 : Mat2), (0 : Mat2)), I, pmul I I, pmul (pmul I I) I, J, pmul I J, pmul (pmul I I) J,
    pmul (pmul (pmul I I) I) J]

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 2000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem classify_dec :
    ∀ a1 ∈ Q6, ∀ b1 ∈ allMat2, a1 * b1 + b1 * a1 = 0 →
    ∀ a2 ∈ Q6, a1 * a2 = -(a2 * a1) → ∀ b2 ∈ allMat2, a2 * b2 + b2 * a2 = 0 →
      a1 * b2 + b1 * a2 = -(a2 * b1 + b2 * a1) →
      (∃ x ∈ q8p (a1, b1) (a2, b2), (uU * a1, uU * b1) = (x.1 * uU, x.2 * uU)) →
      (∃ x ∈ q8p (a1, b1) (a2, b2), (uU * a2, uU * b2) = (x.1 * uU, x.2 * uU)) →
      (b1 = 0 ∧ b2 = 0) ∨ ∃ y : F3, y ≠ 0 ∧ b1 = y • (nU * a1 - a1 * nU) ∧
        b2 = y • (nU * a2 - a2 * nU) := by
  decide +kernel

abbrev Mat4 := Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) F3

@[expose] def kr (u h : Mat2) : Mat4 := Matrix.kroneckerMap (fun x y => x * y) u h

theorem kr_apply (u h : Mat2) (a b i j : Fin 2) : kr u h (a, i) (b, j) = u a b * h i j := rfl

theorem kr_mul (u u' h h' : Mat2) : kr u h * kr u' h' = kr (u * u') (h * h') :=
  (Matrix.mul_kronecker_mul u u' h h').symm

theorem kr_add_left (u u' h : Mat2) : kr (u + u') h = kr u h + kr u' h :=
  Matrix.add_kronecker u u' h

theorem kr_add_right (u h h' : Mat2) : kr u (h + h') = kr u h + kr u h' :=
  Matrix.kronecker_add u h h'

theorem kr_one : kr 1 1 = 1 := Matrix.one_kronecker_one

theorem kr_smul_right (c : F3) (u h : Mat2) : kr u (c • h) = c • kr u h :=
  Matrix.kronecker_smul c u h

theorem kr_zero_left (h : Mat2) : kr 0 h = 0 := Matrix.zero_kronecker h

theorem kr_zero_right (u : Mat2) : kr u 0 = 0 := Matrix.kronecker_zero u

theorem eq_of_comm_nU (X : Mat4) (h : X * kr nU 1 = kr nU 1 * X) :
    ∃ P R : Mat2, X = kr 1 P + kr nU R := by
  refine ⟨Matrix.of fun i j => X (0, i) (0, j), Matrix.of fun i j => X (1, i) (0, j), ?_⟩
  have key : ∀ a i b j : Fin 2, (X * kr nU 1) (a, i) (b, j) = (kr nU 1 * X) (a, i) (b, j) :=
    fun a i b j => by rw [h]
  have e1 : ∀ i j : Fin 2, X (0, i) (1, j) = 0 := by
    intro i j
    have := key 0 i 0 j
    fin_cases j <;>
      simp [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, kr_apply, nU,
        Matrix.one_apply] at this ⊢ <;> exact this
  have e2 : ∀ i j : Fin 2, X (1, i) (1, j) = X (0, i) (0, j) := by
    intro i j
    have := key 1 i 0 j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, kr_apply, nU,
        Matrix.one_apply] at this ⊢ <;> exact this
  ext ⟨a, i⟩ ⟨b, j⟩
  fin_cases a <;> fin_cases b <;>
    simp [kr_apply, Matrix.add_apply, nU, Matrix.one_apply, e1, e2]

def nilp8 : List Mat2 :=
  [!![0, 0; 1, 0], !![0, 0; 2, 0], !![0, 1; 0, 0], !![0, 2; 0, 0], !![1, 1; 2, 2],
    !![1, 2; 1, 2], !![2, 1; 2, 1], !![2, 2; 1, 1]]

set_option maxRecDepth 100000 in
theorem mem_nilp8 (A : Mat2) (h : A * A = 0) (h0 : A ≠ 0) : A ∈ nilp8 := by
  revert A
  decide +kernel

set_option maxRecDepth 100000 in
theorem nilp8_ne : ∀ A ∈ nilp8, A ≠ 0 := by decide +kernel

set_option maxRecDepth 100000 in
theorem nilp8_sq : ∀ A ∈ nilp8, A * A = 0 := by decide +kernel

@[expose] def letter (A : Mat2) (y : F3) (i : ℕ) : Mat4 :=
  if i < 6 then kr 1 (Q6.getD i 0)
  else kr (Q6.getD (i - 6) 0) 1 +
    kr (y • (nU * Q6.getD (i - 6) 0 - Q6.getD (i - 6) 0 * nU)) A

@[expose] def wordVal (A : Mat2) (y : F3) (w : List ℕ) : Mat4 := (w.map (letter A y)).prod

@[expose] def Xof (M : Mat4) : Mat2 := Matrix.of fun i j => M (1, i) (0, j)

def badTable : List (Mat2 × F3 × List ℕ) :=
  [(!![0, 0; 1, 0], 1, [6, 0, 6, 2, 8, 2, 6, 0, 8, 4, 10, 2, 6, 0, 8]),
    (!![0, 0; 1, 0], 2, [6, 0, 8, 2, 10, 4, 6, 0, 8, 2, 6, 2, 8, 0, 9]),
    (!![0, 0; 2, 0], 1, [6, 0, 8, 2, 10, 4, 6, 0, 8, 2, 6, 2, 8, 0, 9]),
    (!![0, 0; 2, 0], 2, [6, 0, 6, 2, 8, 2, 6, 0, 8, 4, 10, 2, 6, 0, 8]),
    (!![0, 1; 0, 0], 1, [6, 2, 6, 0, 8, 0, 6, 2, 8, 4, 10, 0, 6, 2, 9]),
    (!![0, 1; 0, 0], 2, [6, 2, 8, 0, 10, 4, 6, 2, 8, 0, 6, 0, 8, 2, 8]),
    (!![0, 2; 0, 0], 1, [6, 2, 8, 0, 10, 4, 6, 2, 8, 0, 6, 0, 8, 2, 8]),
    (!![0, 2; 0, 0], 2, [6, 2, 6, 0, 8, 0, 6, 2, 8, 4, 10, 0, 6, 2, 9]),
    (!![1, 1; 2, 2], 1, [6, 0, 6, 4, 8, 4, 6, 0, 8, 2, 10, 4, 6, 0, 9]),
    (!![1, 1; 2, 2], 2, [6, 0, 8, 4, 10, 2, 6, 0, 8, 4, 6, 4, 8, 0, 8]),
    (!![1, 2; 1, 2], 1, [6, 0, 8, 2, 10, 4, 6, 0, 8, 2, 6, 2, 8, 0, 9]),
    (!![1, 2; 1, 2], 2, [6, 0, 6, 2, 8, 2, 6, 0, 8, 4, 10, 2, 6, 0, 8]),
    (!![2, 1; 2, 1], 1, [6, 0, 6, 2, 8, 2, 6, 0, 8, 4, 10, 2, 6, 0, 8]),
    (!![2, 1; 2, 1], 2, [6, 0, 8, 2, 10, 4, 6, 0, 8, 2, 6, 2, 8, 0, 9]),
    (!![2, 2; 1, 1], 1, [6, 0, 8, 4, 10, 2, 6, 0, 8, 4, 6, 4, 8, 0, 8]),
    (!![2, 2; 1, 1], 2, [6, 0, 6, 4, 8, 4, 6, 0, 8, 2, 10, 4, 6, 0, 9])]

set_option maxRecDepth 100000 in
theorem badTable_ok : ∀ e ∈ badTable, wordVal e.1 e.2.1 e.2.2 =
      1 + kr nU (Xof (wordVal e.1 e.2.1 e.2.2)) ∧
    ∀ c : F3, Xof (wordVal e.1 e.2.1 e.2.2) ≠ c • 1 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem badTable_complete : ∀ A ∈ nilp8, ∀ y : F3, y ≠ 0 →
    ∃ e ∈ badTable, e.1 = A ∧ e.2.1 = y := by
  decide +kernel

@[expose] def Q8list : List Mat2 :=
  [1, I2m0, I2m0 * I2m0, I2m0 * I2m0 * I2m0, J2m0, I2m0 * J2m0, I2m0 * I2m0 * J2m0,
    I2m0 * I2m0 * I2m0 * J2m0]

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 2000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem classify_g1 : ∀ P ∈ allMat2, ∀ R ∈ allMat2,
    (∃ q ∈ Q8list, P * I2m0 = q * P ∧ R * I2m0 = q * R) →
    (∃ q ∈ Q8list, P * J2m0 = q * P ∧ R * J2m0 = q * R) →
    (P - 1) * (P - 1) = 0 → (P - 1) * R + R * (P - 1) = 0 →
    (∀ c : F3, ¬ (P = 1 ∧ R = c • 1)) → R = 0 ∧ P ≠ 1 := by
  decide +kernel

@[expose] def rhoA (A : Mat2) (x : Mat2 × Mat2) : Mat4 := kr x.1 1 + kr x.2 A

theorem rhoA_mul {A : Mat2} (hA : A * A = 0) (x y : Mat2 × Mat2) :
    rhoA A x * rhoA A y = rhoA A (pmul x y) := by
  simp only [rhoA, pmul, add_mul, mul_add, kr_mul, one_mul, mul_one, hA, kr_zero_right,
    kr_add_left]
  abel

theorem kr_neg_left (u h : Mat2) : kr (-u) h = -kr u h := by
  ext ⟨a, i⟩ ⟨b, j⟩
  simp only [kr_apply, Matrix.neg_apply]
  exact neg_mul _ _

theorem rhoA_neg (A : Mat2) (x : Mat2 × Mat2) : rhoA A (-x) = -rhoA A x := by
  simp only [rhoA, Prod.fst_neg, Prod.snd_neg, kr_neg_left]
  abel

theorem rhoA_one (A : Mat2) : rhoA A ((1 : Mat2), (0 : Mat2)) = 1 := by
  simp [rhoA, kr_zero_left, kr_one]

set_option maxRecDepth 100000 in
theorem comb_zero : ∀ A ∈ nilp8, ∀ x y : F3,
    (∀ i j : Fin 2, x * (1 : Mat2) i j + y * A i j = 0) → x = 0 ∧ y = 0 := by
  decide +kernel

theorem rhoA_inj {A : Mat2} (hA : A ∈ nilp8) : Function.Injective (rhoA A) := by
  intro x y h
  have key : ∀ a b : Fin 2, x.1 a b = y.1 a b ∧ x.2 a b = y.2 a b := by
    intro a b
    have h1 : ∀ i j : Fin 2, (x.1 a b - y.1 a b) * (1 : Mat2) i j + (x.2 a b - y.2 a b) * A i j =
        0 := by
      intro i j
      have := congrFun (congrFun h (a, i)) (b, j)
      simp only [rhoA, Matrix.add_apply, kr_apply] at this
      rw [sub_mul, sub_mul]
      have e : x.1 a b * (1 : Mat2) i j + x.2 a b * A i j =
          y.1 a b * (1 : Mat2) i j + y.2 a b * A i j := this
      linear_combination e
    obtain ⟨h2, h3⟩ := comb_zero A hA _ _ h1
    exact ⟨sub_eq_zero.mp h2, sub_eq_zero.mp h3⟩
  exact Prod.ext (by ext a b; exact (key a b).1) (by ext a b; exact (key a b).2)

set_option maxRecDepth 100000 in
theorem comm_dec : ∀ A ∈ nilp8, ∀ B : Mat2, B * A = A * B → ∃ x y : F3, B = x • 1 + y • A := by
  decide +kernel

theorem mul_kr1A_apply (X : Mat4) (A : Mat2) (a i b j : Fin 2) :
    (X * kr 1 A) (a, i) (b, j) = ∑ k, X (a, i) (b, k) * A k j := by
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, kr_apply, Matrix.one_apply]
  simp [ite_mul, Finset.sum_ite_eq]

theorem kr1A_mul_apply (X : Mat4) (A : Mat2) (a i b j : Fin 2) :
    (kr 1 A * X) (a, i) (b, j) = ∑ k, A i k * X (a, k) (b, j) := by
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, kr_apply, Matrix.one_apply]
  simp [ite_mul, Finset.sum_ite_eq]

theorem exists_rhoA {A : Mat2} (hA : A ∈ nilp8) (X : Mat4) (h : X * kr 1 A = kr 1 A * X) :
    ∃ x : Mat2 × Mat2, X = rhoA A x := by
  classical
  have hblock : ∀ a b : Fin 2, (Matrix.of fun i j => X (a, i) (b, j) : Mat2) * A =
      A * (Matrix.of fun i j => X (a, i) (b, j) : Mat2) := by
    intro a b
    ext i j
    have := congrFun (congrFun h (a, i)) (b, j)
    rw [mul_kr1A_apply, kr1A_mul_apply] at this
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  choose f hf using fun a b => comm_dec A hA _ (hblock a b)
  choose g hg using fun a b => (hf a b)
  refine ⟨(Matrix.of f, Matrix.of g), ?_⟩
  ext ⟨a, i⟩ ⟨b, j⟩
  have := congrFun (congrFun (hg a b) i) j
  simp only [Matrix.of_apply] at this
  refine this.trans ?_
  simp [rhoA, kr_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply]

@[expose] def rhoU (x : Mat2 × Mat2) : Mat4 := kr 1 x.1 + kr nU x.2

theorem nU_mul_nU : nU * nU = 0 := by decide

theorem rhoU_mul (x y : Mat2 × Mat2) : rhoU x * rhoU y = rhoU (pmul x y) := by
  simp only [rhoU, pmul, add_mul, mul_add, kr_mul, one_mul, mul_one, nU_mul_nU, kr_zero_left,
    kr_add_right]
  abel

theorem rhoU_add (x y : Mat2 × Mat2) : rhoU (x + y) = rhoU x + rhoU y := by
  simp only [rhoU, Prod.fst_add, Prod.snd_add, kr_add_right]
  abel

theorem rhoU_one : rhoU ((1 : Mat2), (0 : Mat2)) = 1 := by
  simp [rhoU, kr_zero_right, kr_one]

theorem rhoU_inj : Function.Injective rhoU := by
  intro x y h
  have key : ∀ i j : Fin 2, x.1 i j = y.1 i j ∧ x.2 i j = y.2 i j := by
    intro i j
    have h1 := congrFun (congrFun h (0, i)) (0, j)
    have h2 := congrFun (congrFun h (1, i)) (0, j)
    simp only [rhoU, Matrix.add_apply, kr_apply, Matrix.one_apply] at h1 h2
    simp at h1 h2
    exact ⟨h1, h2⟩
  exact Prod.ext (by ext i j; exact (key i j).1) (by ext i j; exact (key i j).2)

theorem rhoA_neg_one (A : Mat2) : rhoA A (-1, 0) = -1 := by
  simp [rhoA, kr_zero_left]
  ext ⟨a, i⟩ ⟨b, j⟩
  simp [kr_apply, Matrix.one_apply, Matrix.neg_apply]
  by_cases h : a = b <;> by_cases h' : i = j <;> simp [h, h'] <;> decide

theorem Q6_getD : Q6.getD 0 0 = I2m0 ∧ Q6.getD 1 0 = I2m0 * I2m0 * I2m0 ∧ Q6.getD 2 0 = J2m0 ∧
    Q6.getD 3 0 = I2m0 * I2m0 * J2m0 ∧ Q6.getD 4 0 = I2m0 * J2m0 ∧
    Q6.getD 5 0 = I2m0 * I2m0 * I2m0 * J2m0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

theorem badTable_lt : ∀ e ∈ badTable, ∀ i ∈ e.2.2, i < 12 := by decide +kernel

def q8CoverCheck : Bool :=
  Q6.all fun a1 => Q6.all fun a2 =>
    !decide (a1 * a2 = -(a2 * a1)) ||
      Q6.all fun a => (q8g (· * ·) (1 : Mat2) a1 a2).any fun w => decide (w = a)

theorem q8CoverCheck_eq : q8CoverCheck = true := by decide +kernel

theorem q8_cover : ∀ a1 ∈ Q6, ∀ a2 ∈ Q6, a1 * a2 = -(a2 * a1) →
    ∀ a ∈ Q6, ∃ w ∈ q8g (· * ·) (1 : Mat2) a1 a2, w = a := by
  have h := q8CoverCheck_eq
  simp only [q8CoverCheck, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not, List.any_eq_true, decide_eq_true_eq] at h
  intro a1 ha1 a2 ha2 hanti a ha
  rcases h a1 ha1 a2 ha2 with h1 | h1
  · exact absurd hanti h1
  · exact h1 a ha

def badPairsCheck : Bool :=
  Q6.all fun a1 => Q6.all fun a2 => ([0, 1, 2] : List F3).all fun y =>
    (q8g pmul ((1 : Mat2), (0 : Mat2)) (a1, y • (nU * a1 - a1 * nU))
      (a2, y • (nU * a2 - a2 * nU))).all fun w => decide (w.2 = y • (nU * w.1 - w.1 * nU))

theorem badPairsCheck_eq : badPairsCheck = true := by decide +kernel

theorem mem_F3_list (y : F3) : y ∈ ([0, 1, 2] : List F3) := by
  revert y; decide +kernel

theorem bad_pairs : ∀ a1 ∈ Q6, ∀ a2 ∈ Q6, ∀ y : F3,
    ∀ w ∈ q8g pmul ((1 : Mat2), (0 : Mat2)) (a1, y • (nU * a1 - a1 * nU))
      (a2, y • (nU * a2 - a2 * nU)), w.2 = y • (nU * w.1 - w.1 * nU) := by
  have h := badPairsCheck_eq
  simp only [badPairsCheck, List.all_eq_true, decide_eq_true_eq] at h
  intro a1 ha1 a2 ha2 y w hw
  exact h a1 ha1 a2 ha2 y (mem_F3_list y) w hw

theorem q8g_fst {α β : Type*} (m : α → α → α) (m' : β → β → β) (f : β → α)
    (hf : ∀ x y, f (m' x y) = m (f x) (f y)) (e x z : β) :
    (q8g m' e x z).map f = q8g m (f e) (f x) (f z) := by
  simp only [q8g, List.map_cons, List.map_nil, hf]

set_option maxRecDepth 100000 in
theorem trans_dec : ∀ c c' : Fin 2 → F3, c ≠ 0 → c' ≠ 0 → ∃ q ∈ Q8list, q.mulVec c = c' := by
  decide +kernel

def normCheck : Bool :=
  Q6.all fun I => Q6.all fun J =>
    !decide (I * J = -(J * I)) || allMat2.all fun g =>
      !decide (g.det ≠ 0) ||
        ((q8g (· * ·) (1 : Mat2) I J).any fun y => decide (g * I = y * g)) &&
        ((q8g (· * ·) (1 : Mat2) I J).any fun y => decide (g * J = y * g))

theorem normCheck_eq : normCheck = true := by decide +kernel

theorem norm_dec : ∀ I ∈ Q6, ∀ J ∈ Q6, I * J = -(J * I) → ∀ g : Mat2, g.det ≠ 0 →
    (∃ y ∈ q8g (· * ·) (1 : Mat2) I J, g * I = y * g) ∧
      (∃ y ∈ q8g (· * ·) (1 : Mat2) I J, g * J = y * g) := by
  have h := normCheck_eq
  simp only [normCheck, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not, Bool.and_eq_true, List.any_eq_true, decide_eq_true_eq] at h
  intro I hI J hJ hIJ g hg
  rcases h I hI J hJ with h1 | h1
  · exact absurd hIJ h1
  · rcases h1 g (mem_allMat2 g) with h2 | h2
    · exact absurd h2 (by simpa using hg)
    · exact h2

end CFSG.RankThree.PartTwo.Sec21.Hering2119S
