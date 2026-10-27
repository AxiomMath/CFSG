module

public import CFSG.Permutation.FinPackCount

public section

namespace CFSG.Permutation.FinPack

@[expose] noncomputable def passK {α : Type} (y : ℕ) (k : ℕ → α) : α :=
  Nat.rec (motive := fun _ => α) (k (nat_lit 0)) (fun n _ => k (Nat.succ n)) y

theorem passK_apply {α : Type} (y : ℕ) (k : ℕ → α) : passK y k = k y := by
  cases y <;> rfl

@[expose] noncomputable def imgK (c m k : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0 (fun i acc => Bool.rec (motive := fun _ => ℕ) acc
    (Nat.lor acc (Nat.shiftLeft 1 (rd c i))) (Nat.blt 0 (Nat.land m (Nat.shiftLeft 1 i)))) k

theorem testBit_imgK (c m y : ℕ) : ∀ k,
    (imgK c m k).testBit y = true ↔ ∃ i < k, m.testBit i = true ∧ rd c i = y := by
  intro k
  induction k with
  | zero =>
    change (0 : ℕ).testBit y = true ↔ _
    rw [Nat.zero_testBit]
    exact ⟨fun h => absurd h Bool.false_ne_true, fun ⟨i, hi, _⟩ => absurd hi (Nat.not_lt_zero i)⟩
  | succ k ih =>
    change (Bool.rec (motive := fun _ => ℕ) (imgK c m k)
      (Nat.lor (imgK c m k) (Nat.shiftLeft 1 (rd c k)))
      (Nat.blt 0 (Nat.land m (Nat.shiftLeft 1 k)))).testBit y = true ↔ _
    cases hb : Nat.blt 0 (Nat.land m (Nat.shiftLeft 1 k))
    · have hk : m.testBit k = false := by
        rw [← Bool.not_eq_true, ← blt_land_iff, hb]
        exact Bool.false_ne_true
      change (imgK c m k).testBit y = true ↔ _
      rw [ih]
      constructor
      · rintro ⟨i, hi, h⟩
        exact ⟨i, by omega, h⟩
      · rintro ⟨i, hi, h1, h2⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
        · exact ⟨i, hi, h1, h2⟩
        · rw [hk] at h1
          exact absurd h1 Bool.false_ne_true
    · have hk : m.testBit k = true := (blt_land_iff m k).1 hb
      change (imgK c m k ||| 1 <<< rd c k).testBit y = true ↔ _
      rw [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow, Bool.or_eq_true, ih,
        decide_eq_true_iff]
      constructor
      · rintro (⟨i, hi, h⟩ | h)
        · exact ⟨i, by omega, h⟩
        · exact ⟨k, by omega, hk, h⟩
      · rintro ⟨i, hi, h1, h2⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
        · exact Or.inl ⟨i, hi, h1, h2⟩
        · exact Or.inr h2

@[expose] noncomputable def stepK (n : ℕ) (L : List ℕ) (m : ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ) m (fun c _ r => Nat.lor r (imgK c m n)) L

theorem testBit_stepK (n : ℕ) (m y : ℕ) : ∀ L : List ℕ, (stepK n L m).testBit y = true ↔
    m.testBit y = true ∨ ∃ c ∈ L, ∃ i < n, m.testBit i = true ∧ rd c i = y := by
  intro L
  induction L with
  | nil =>
    change m.testBit y = true ↔ _
    simp
  | cons c L ih =>
    change (stepK n L m ||| imgK c m n).testBit y = true ↔ _
    rw [Nat.testBit_or, Bool.or_eq_true, ih, testBit_imgK]
    simp only [List.mem_cons, or_and_right, exists_or, exists_eq_left]
    constructor
    · rintro ((h | h) | h)
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
      · exact Or.inr (Or.inl h)
    · rintro (h | h | h)
      · exact Or.inl (Or.inl h)
      · exact Or.inr h
      · exact Or.inl (Or.inr h)

@[expose] noncomputable def orbK (n : ℕ) (L : List ℕ) (k : ℕ) : ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ) (fun m => m) (fun _ r m => passK (stepK n L m) r) k

theorem orbK_succ' (n : ℕ) (L : List ℕ) (k m : ℕ) :
    orbK n L (k + 1) m = orbK n L k (stepK n L m) :=
  passK_apply _ _

theorem orbK_succ (n : ℕ) (L : List ℕ) : ∀ k m, orbK n L (k + 1) m = stepK n L (orbK n L k m) := by
  intro k
  induction k with
  | zero =>
    intro m
    exact orbK_succ' n L 0 m
  | succ k ih =>
    intro m
    exact (orbK_succ' n L (k + 1) m).trans ((ih _).trans
      (congrArg (stepK n L) (orbK_succ' n L k m).symm))

end CFSG.Permutation.FinPack
