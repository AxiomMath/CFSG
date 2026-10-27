module

public import CFSG.OddTranspositions.PartThree.Eleven.Five.FiveFormAux
public import CFSG.OddTranspositions.PartFour.Fourteen.TableE1Five
public import CFSG.RankThree.GF2n.Tim79aSec2

public section

namespace CFSG.OddTranspositions.PartThree

open Matrix

namespace FiveWalk

@[simp] theorem fiveBilin_true_apply (k : ℕ) (ε : Bool) (x y : Fin (k + 1) → ZMod 5) :
    fiveBilin k ε true x y = fiveForm k ε x y := by
  rw [fiveBilin_apply]
  simp [fiveSignRep]

@[simp] theorem fiveForm_zero_right (k : ℕ) (ε : Bool) (x : Fin (k + 1) → ZMod 5) :
    fiveForm k ε x 0 = 0 := by
  simp [fiveForm]

@[simp] theorem fiveForm_zero_left (k : ℕ) (ε : Bool) (y : Fin (k + 1) → ZMod 5) :
    fiveForm k ε 0 y = 0 := by
  simp [fiveForm]

theorem five_inv_two : (2 : ZMod 5)⁻¹ = 3 := by
  have h23 : (2 : ZMod 5) * 3 = 1 := by decide
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  rw [inv_eq_of_mul_eq_one_right h23]

theorem five_eq_zero : (5 : ZMod 5) = 0 := by decide

theorem five_num_16 : (16 : ZMod 5) = 1 := by decide

theorem five_sq_class_same : ∀ c b : ZMod 5, c ≠ 0 → b ≠ 0 →
    ((2 * c - 2 * b) ≠ 0 ∧ (IsSquare (2 * c - 2 * b) ↔ IsSquare c)) ∨
    ((2 * c + 2 * b) ≠ 0 ∧ (IsSquare (2 * c + 2 * b) ↔ IsSquare c)) := by
  decide

theorem five_sq_class_opposite : ∀ c b : ZMod 5, c ≠ 0 → b ≠ c → b ≠ -c →
    ((2 * c - 2 * b) ≠ 0 ∧ (IsSquare (2 * c - 2 * b) ↔ ¬ IsSquare c)) ∨
    ((2 * c + 2 * b) ≠ 0 ∧ (IsSquare (2 * c + 2 * b) ↔ ¬ IsSquare c)) := by
  decide

theorem five_exists_sq_comb : ∀ a b d : ZMod 5, a ≠ 0 → b ≠ 0 →
    ∃ α β : ZMod 5, α ^ 2 * a + β ^ 2 * b = d := by
  decide

theorem fiveForm_nondegenerate (k : ℕ) (ε : Bool) (x : Fin (k + 1) → ZMod 5)
    (hx : ∀ y, fiveForm k ε x y = 0) : x = 0 :=
  fiveBilin_nondegenerate k ε true x (fun y => by rw [fiveBilin_true_apply]; exact hx y)

theorem fiveForm_sub_smul_expand (k : ℕ) (ε : Bool) (x y v : Fin (k + 1) → ZMod 5)
    (a b : ZMod 5) :
    fiveForm k ε (x - a • v) (y - b • v) =
      fiveForm k ε x y - b * fiveForm k ε x v - a * fiveForm k ε v y
        + a * b * fiveForm k ε v v := by
  simp only [fiveForm_sub_left, fiveForm_sub_right, fiveForm_smul_left, fiveForm_smul_right]
  ring

theorem fiveReflOf_mul_self (k : ℕ) (ε : Bool) (x : Fin (k + 1) → ZMod 5) :
    fiveReflOf k ε x * fiveReflOf k ε x = 1 := by
  apply Units.ext
  change fiveReflMatrix k ε x * fiveReflMatrix k ε x = 1
  exact fiveReflMatrix_mul_self k ε x

theorem fiveReflOf_neg (k : ℕ) (ε : Bool) (x : Fin (k + 1) → ZMod 5) :
    fiveReflOf k ε (-x) = fiveReflOf k ε x := by
  have h := fiveReflOf_smul k ε x (c := -1) (by decide : (-1 : ZMod 5) ≠ 0)
  rw [show (-1 : ZMod 5) • x = -x by
    ext j
    exact neg_one_mul (x j)] at h
  exact h

theorem fiveForm_fiveReflOf (k : ℕ) (ε : Bool) (v x y : Fin (k + 1) → ZMod 5) :
    fiveForm k ε (((fiveReflOf k ε v : GL (Fin (k + 1)) (ZMod 5)) :
        Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ x)
      (((fiveReflOf k ε v : GL (Fin (k + 1)) (ZMod 5)) :
        Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ y) =
      fiveForm k ε x y := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  rw [fiveReflOf_mulVec, fiveReflOf_mulVec, fiveForm_sub_smul_expand,
    fiveForm_comm k ε v y]
  by_cases hQ : fiveForm k ε v v = 0
  · simp [hQ]
    ring
  · field_simp
    ring

theorem fiveNorm_fiveReflOf (k : ℕ) (ε : Bool) (v w : Fin (k + 1) → ZMod 5) :
    fiveForm k ε (((fiveReflOf k ε v : GL (Fin (k + 1)) (ZMod 5)) :
        Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ w)
      (((fiveReflOf k ε v : GL (Fin (k + 1)) (ZMod 5)) :
        Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ w) =
      fiveForm k ε w w :=
  fiveForm_fiveReflOf k ε v w w

theorem fiveForm_fiveReflOf_eq_zero_of_perp (k : ℕ) (ε : Bool) {v w c : Fin (k + 1) → ZMod 5}
    (hvc : fiveForm k ε v c = 0) (hwc : fiveForm k ε w c = 0) :
    fiveForm k ε (((fiveReflOf k ε v : GL (Fin (k + 1)) (ZMod 5)) :
        Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ w) c = 0 := by
  have hc : (((fiveReflOf k ε v : GL (Fin (k + 1)) (ZMod 5)) :
      Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ c) = c := by
    rw [fiveReflOf_mulVec, fiveForm_comm k ε c v, hvc, mul_zero, zero_mul, zero_smul]
    abel
  rw [← hc, fiveForm_fiveReflOf, hwc]

theorem fiveNorm_sub (k : ℕ) (ε : Bool) (x y : Fin (k + 1) → ZMod 5) :
    fiveForm k ε (x - y) (x - y) =
      fiveForm k ε x x - 2 * fiveForm k ε x y + fiveForm k ε y y := by
  rw [fiveForm_sub_left, fiveForm_sub_right, fiveForm_sub_right,
    fiveForm_comm k ε y x]
  ring

theorem fiveNorm_add (k : ℕ) (ε : Bool) (x y : Fin (k + 1) → ZMod 5) :
    fiveForm k ε (x + y) (x + y) =
      fiveForm k ε x x + 2 * fiveForm k ε x y + fiveForm k ε y y := by
  rw [fiveForm_add_left, fiveForm_add_right, fiveForm_add_right,
    fiveForm_comm k ε y x]
  ring

theorem fiveNorm_add_smul (k : ℕ) (ε : Bool) (w₁ w₂ : Fin (k + 1) → ZMod 5) (α β : ZMod 5) :
    fiveForm k ε (α • w₁ + β • w₂) (α • w₁ + β • w₂) =
      α ^ 2 * fiveForm k ε w₁ w₁ + β ^ 2 * fiveForm k ε w₂ w₂ +
        2 * α * β * fiveForm k ε w₁ w₂ := by
  simp only [fiveForm_add_left, fiveForm_add_right, fiveForm_smul_left, fiveForm_smul_right]
  rw [fiveForm_comm k ε w₂ w₁]
  ring

theorem fivePair_sub (k : ℕ) (ε : Bool) (x y : Fin (k + 1) → ZMod 5) :
    fiveForm k ε x (x - y) = fiveForm k ε x x - fiveForm k ε x y := by
  rw [fiveForm_sub_right]

theorem fivePair_add (k : ℕ) (ε : Bool) (x y : Fin (k + 1) → ZMod 5) :
    fiveForm k ε x (x + y) = fiveForm k ε x x + fiveForm k ε x y := by
  rw [fiveForm_add_right]

theorem fiveReflOf_sub_mulVec (k : ℕ) (ε : Bool) {x y : Fin (k + 1) → ZMod 5}
    (hQ : fiveForm k ε y y = fiveForm k ε x x) (hne : fiveForm k ε (x - y) (x - y) ≠ 0) :
    (((fiveReflOf k ε (x - y) : GL (Fin (k + 1)) (ZMod 5)) :
        Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ x) = y := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  rw [fiveReflOf_mulVec]
  have hnorm : fiveForm k ε (x - y) (x - y) = 2 * fiveForm k ε x (x - y) := by
    rw [fiveNorm_sub, hQ, fivePair_sub]
    ring
  have hne' : 2 * fiveForm k ε x (x - y) ≠ 0 := by rwa [← hnorm]
  have hcoef : 2 * fiveForm k ε x (x - y) * (fiveForm k ε (x - y) (x - y))⁻¹ = 1 := by
    rw [hnorm]
    exact mul_inv_cancel₀ hne'
  rw [hcoef, one_smul]
  abel

theorem fiveReflOf_add_mulVec (k : ℕ) (ε : Bool) {x y : Fin (k + 1) → ZMod 5}
    (hQ : fiveForm k ε y y = fiveForm k ε x x) (hne : fiveForm k ε (x + y) (x + y) ≠ 0) :
    (((fiveReflOf k ε (x + y) : GL (Fin (k + 1)) (ZMod 5)) :
        Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ x) = -y := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  rw [fiveReflOf_mulVec]
  have hnorm : fiveForm k ε (x + y) (x + y) = 2 * fiveForm k ε x (x + y) := by
    rw [fiveNorm_add, hQ, fivePair_add]
    ring
  have hne' : 2 * fiveForm k ε x (x + y) ≠ 0 := by rwa [← hnorm]
  have hcoef : 2 * fiveForm k ε x (x + y) * (fiveForm k ε (x + y) (x + y))⁻¹ = 1 := by
    rw [hnorm]
    exact mul_inv_cancel₀ hne'
  rw [hcoef, one_smul]
  abel

theorem exists_aniso_perp_five {k : ℕ} (ε : Bool) {m : ℕ} (hm : m < k + 1)
    (u : Fin m → Fin (k + 1) → ZMod 5)
    (horth : ∀ i j, i ≠ j → fiveForm k ε (u i) (u j) = 0)
    (hanis : ∀ i, fiveForm k ε (u i) (u i) ≠ 0) :
    ∃ z, (∀ i, fiveForm k ε z (u i) = 0) ∧ fiveForm k ε z z ≠ 0 := by
  obtain ⟨z, hz, hzz⟩ := CFSG.OddTranspositions.PartFour.TableE1Five.exists_aniso_perp
    (b := fiveBilin k ε true) (n := k + 1)
    (fiveBilin_comm k ε true) (fiveBilin_nondegenerate k ε true) (k := m) hm u
    (fun i j hij => by rw [fiveBilin_true_apply]; exact horth i j hij)
    (fun i => by rw [fiveBilin_true_apply]; exact hanis i)
  exact ⟨z, fun i => by simpa using hz i, by simpa using hzz⟩

theorem exists_two_aniso_perp_orth {k : ℕ} (hk : 4 ≤ k) (ε : Bool)
    {a b' : Fin (k + 1) → ZMod 5} (ha : fiveForm k ε a a ≠ 0)
    (hb'a : fiveForm k ε b' a = 0) :
    ∃ w₁ w₂, fiveForm k ε w₁ a = 0 ∧ fiveForm k ε w₁ b' = 0 ∧ fiveForm k ε w₁ w₁ ≠ 0 ∧
      fiveForm k ε w₂ a = 0 ∧ fiveForm k ε w₂ b' = 0 ∧ fiveForm k ε w₂ w₂ ≠ 0 ∧
      fiveForm k ε w₁ w₂ = 0 := by
  have h2ne : (2 : ZMod 5) ≠ 0 := by decide
  have hneg2ne : (-2 : ZMod 5) ≠ 0 := by decide
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hb'a' : fiveForm k ε a b' = 0 := by rw [fiveForm_comm k ε a b']; exact hb'a
  by_cases hb'Q : fiveForm k ε b' b' = 0
  · by_cases hb'0 : b' = 0
    ·
      rw [hb'0]
      obtain ⟨w₁, hw₁, hw₁ne⟩ := exists_aniso_perp_five (k := k) ε (m := 1) (by omega) ![a]
        (fun i j hij => by fin_cases i <;> fin_cases j <;> exact absurd rfl hij)
        (fun i => by fin_cases i; simpa using ha)
      have hw₁a : fiveForm k ε w₁ a = 0 := by simpa using hw₁ 0
      have haw₁ : fiveForm k ε a w₁ = 0 := by rw [fiveForm_comm k ε a w₁]; exact hw₁a
      obtain ⟨w₂, hw₂, hw₂ne⟩ := exists_aniso_perp_five (k := k) ε (m := 2) (by omega) ![a, w₁]
        (fun i j hij => by
          fin_cases i <;> fin_cases j <;>
            first
              | exact absurd rfl hij
              | assumption)
        (fun i => by
          fin_cases i
          · simpa using ha
          · simpa using hw₁ne)
      have hw₂a : fiveForm k ε w₂ a = 0 := by simpa using hw₂ 0
      have hw₂w₁ : fiveForm k ε w₂ w₁ = 0 := by simpa using hw₂ 1
      exact ⟨w₁, w₂, hw₁a, by simp, hw₁ne, hw₂a, by simp, hw₂ne,
        by rw [fiveForm_comm k ε w₁ w₂]; exact hw₂w₁⟩
    ·
      obtain ⟨y, hy⟩ : ∃ y, fiveForm k ε b' y ≠ 0 := by
        by_contra h
        push Not at h
        exact hb'0 (fiveForm_nondegenerate k ε b' h)
      set y₀ : Fin (k + 1) → ZMod 5 := y - (fiveForm k ε y a * (fiveForm k ε a a)⁻¹) • a with hy₀
      have hy₀a : fiveForm k ε y₀ a = 0 := by
        rw [hy₀, fiveForm_sub_left, fiveForm_smul_left, mul_assoc, inv_mul_cancel₀ ha, mul_one,
          sub_self]
      have hb'y₀ : fiveForm k ε b' y₀ ≠ 0 := by
        rw [hy₀, fiveForm_sub_right, fiveForm_smul_right, hb'a, mul_zero]
        rw [show fiveForm k ε b' y - 0 = fiveForm k ε b' y by abel]
        exact hy
      obtain ⟨y₁, hby₁, hy₁a⟩ : ∃ y₁, fiveForm k ε b' y₁ = 1 ∧ fiveForm k ε y₁ a = 0 := by
        refine ⟨(fiveForm k ε b' y₀)⁻¹ • y₀, ?_, ?_⟩
        · rw [fiveForm_smul_right]
          exact inv_mul_cancel₀ hb'y₀
        · rw [fiveForm_smul_left, hy₀a, mul_zero]
      obtain ⟨d', hbd, hdQ, hda⟩ : ∃ d', fiveForm k ε b' d' = 1 ∧ fiveForm k ε d' d' = 0 ∧
          fiveForm k ε d' a = 0 := by
        refine ⟨y₁ - ((2 : ZMod 5)⁻¹ * fiveForm k ε y₁ y₁) • b', ?_, ?_, ?_⟩
        · rw [fiveForm_sub_right, fiveForm_smul_right, hby₁, hb'Q, mul_zero]
          ring
        · rw [fiveForm_sub_smul_expand, fiveForm_comm k ε y₁ b', hby₁, hb'Q, mul_one, mul_zero,
            add_zero, five_inv_two]
          ring_nf
          rw [five_eq_zero]
          ring
        · rw [fiveForm_sub_left, hy₁a, fiveForm_smul_left, hb'a, mul_zero]
          ring
      have hpQ : fiveForm k ε (b' + d') (b' + d') = 2 := by
        rw [fiveNorm_add, hb'Q, hbd, hdQ]; ring_nf
      have hqQ : fiveForm k ε (b' - d') (b' - d') = -2 := by
        rw [fiveNorm_sub, hb'Q, hbd, hdQ]; ring_nf; rfl
      have hpq : fiveForm k ε (b' + d') (b' - d') = 0 := by
        rw [fiveForm_add_left, fiveForm_sub_right, fiveForm_sub_right, hb'Q, hbd,
          fiveForm_comm k ε d' b', hbd, hdQ]
        ring
      have hqp : fiveForm k ε (b' - d') (b' + d') = 0 := by
        rw [fiveForm_comm k ε (b' - d') (b' + d'), hpq]
      have hpa : fiveForm k ε (b' + d') a = 0 := by
        rw [fiveForm_add_left, hb'a, hda, add_zero]
      have hqa : fiveForm k ε (b' - d') a = 0 := by
        rw [fiveForm_sub_left, hb'a, hda]
        ring
      have hap : fiveForm k ε a (b' + d') = 0 := by
        rw [fiveForm_comm k ε a (b' + d'), hpa]
      have haq : fiveForm k ε a (b' - d') = 0 := by
        rw [fiveForm_comm k ε a (b' - d'), hqa]
      have hb'_comb : b' = ((2 : ZMod 5)⁻¹) • ((b' + d') + (b' - d')) := by
        have h : (b' + d') + (b' - d') = (2 : ZMod 5) • b' := by module
        rw [h, smul_smul, inv_mul_cancel₀ h2ne, one_smul]
      have horthlist : ∀ i j : Fin 3, i ≠ j →
          fiveForm k ε (![a, b' + d', b' - d'] i) (![a, b' + d', b' - d'] j) = 0 := by
        intro i j hij
        fin_cases i <;> fin_cases j <;>
          first
            | exact absurd rfl hij
            | assumption
      have hanislist : ∀ i : Fin 3, fiveForm k ε (![a, b' + d', b' - d'] i)
          (![a, b' + d', b' - d'] i) ≠ 0 := by
        intro i
        fin_cases i
        · exact ha
        · change fiveForm k ε (b' + d') (b' + d') ≠ 0
          rw [hpQ]; exact h2ne
        · change fiveForm k ε (b' - d') (b' - d') ≠ 0
          rw [hqQ]; exact hneg2ne
      obtain ⟨w₁, hw₁, hw₁ne⟩ := exists_aniso_perp_five (k := k) ε (m := 3) (by omega) _ horthlist hanislist
      have hw₁a : fiveForm k ε w₁ a = 0 := by simpa using hw₁ 0
      have hw₁p : fiveForm k ε w₁ (b' + d') = 0 := by simpa using hw₁ 1
      have hw₁q : fiveForm k ε w₁ (b' - d') = 0 := by simpa using hw₁ 2
      have haw₁ : fiveForm k ε a w₁ = 0 := by rw [fiveForm_comm k ε a w₁]; exact hw₁a
      have hpw₁ : fiveForm k ε (b' + d') w₁ = 0 := by rw [fiveForm_comm k ε (b' + d') w₁]; exact hw₁p
      have hqw₁ : fiveForm k ε (b' - d') w₁ = 0 := by rw [fiveForm_comm k ε (b' - d') w₁]; exact hw₁q
      have horthlist2 : ∀ i j : Fin 4, i ≠ j →
          fiveForm k ε (![a, b' + d', b' - d', w₁] i) (![a, b' + d', b' - d', w₁] j) = 0 := by
        intro i j hij
        fin_cases i <;> fin_cases j <;>
          first
            | exact absurd rfl hij
            | assumption
      have hanislist2 : ∀ i : Fin 4, fiveForm k ε (![a, b' + d', b' - d', w₁] i)
          (![a, b' + d', b' - d', w₁] i) ≠ 0 := by
        intro i
        fin_cases i
        · exact ha
        · change fiveForm k ε (b' + d') (b' + d') ≠ 0
          rw [hpQ]; exact h2ne
        · change fiveForm k ε (b' - d') (b' - d') ≠ 0
          rw [hqQ]; exact hneg2ne
        · exact hw₁ne
      obtain ⟨w₂, hw₂, hw₂ne⟩ := exists_aniso_perp_five (k := k) ε (m := 4) (by omega) _ horthlist2 hanislist2
      have hw₂a : fiveForm k ε w₂ a = 0 := by simpa using hw₂ 0
      have hw₂p : fiveForm k ε w₂ (b' + d') = 0 := by simpa using hw₂ 1
      have hw₂q : fiveForm k ε w₂ (b' - d') = 0 := by simpa using hw₂ 2
      have hw₁b' : fiveForm k ε w₁ b' = 0 := by
        rw [hb'_comb, fiveForm_smul_right, fiveForm_add_right, hw₁p, hw₁q, add_zero, mul_zero]
      have hw₂b' : fiveForm k ε w₂ b' = 0 := by
        rw [hb'_comb, fiveForm_smul_right, fiveForm_add_right, hw₂p, hw₂q, add_zero, mul_zero]
      have h12 : fiveForm k ε w₁ w₂ = 0 := by
        rw [fiveForm_comm k ε w₁ w₂]; simpa using hw₂ 3
      exact ⟨w₁, w₂, hw₁a, hw₁b', hw₁ne, hw₂a, hw₂b', hw₂ne, h12⟩
  ·
    obtain ⟨w₁, hw₁, hw₁ne⟩ := exists_aniso_perp_five (k := k) ε (m := 2) (by omega) ![a, b']
      (fun i j hij => by
        fin_cases i <;> fin_cases j <;>
          first
            | exact absurd rfl hij
            | assumption)
      (fun i => by
        fin_cases i
        · simpa using ha
        · simpa using hb'Q)
    have hw₁a : fiveForm k ε w₁ a = 0 := by simpa using hw₁ 0
    have hw₁b' : fiveForm k ε w₁ b' = 0 := by simpa using hw₁ 1
    have haw₁ : fiveForm k ε a w₁ = 0 := by rw [fiveForm_comm k ε a w₁]; exact hw₁a
    have hb'w₁ : fiveForm k ε b' w₁ = 0 := by rw [fiveForm_comm k ε b' w₁]; exact hw₁b'
    have horthlist2 : ∀ i j : Fin 3, i ≠ j →
        fiveForm k ε (![a, b', w₁] i) (![a, b', w₁] j) = 0 := by
      intro i j hij
      fin_cases i <;> fin_cases j <;>
        first
          | exact absurd rfl hij
          | assumption
    have hanislist2 : ∀ i : Fin 3, fiveForm k ε (![a, b', w₁] i) (![a, b', w₁] i) ≠ 0 := by
      intro i
      fin_cases i
      · exact ha
      · exact hb'Q
      · exact hw₁ne
    obtain ⟨w₂, hw₂, hw₂ne⟩ := exists_aniso_perp_five (k := k) ε (m := 3) (by omega) _ horthlist2 hanislist2
    have hw₂a : fiveForm k ε w₂ a = 0 := by simpa using hw₂ 0
    have hw₂b' : fiveForm k ε w₂ b' = 0 := by simpa using hw₂ 1
    have h12 : fiveForm k ε w₁ w₂ = 0 := by
      rw [fiveForm_comm k ε w₁ w₂]; simpa using hw₂ 2
    exact ⟨w₁, w₂, hw₁a, hw₁b', hw₁ne, hw₂a, hw₂b', hw₂ne, h12⟩

theorem exists_two_aniso_perp {k : ℕ} (hk : 4 ≤ k) (ε : Bool)
    {a b : Fin (k + 1) → ZMod 5} (ha : fiveForm k ε a a ≠ 0) :
    ∃ w₁ w₂, fiveForm k ε w₁ a = 0 ∧ fiveForm k ε w₁ b = 0 ∧ fiveForm k ε w₁ w₁ ≠ 0 ∧
      fiveForm k ε w₂ a = 0 ∧ fiveForm k ε w₂ b = 0 ∧ fiveForm k ε w₂ w₂ ≠ 0 ∧
      fiveForm k ε w₁ w₂ = 0 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨w₁, w₂, h1a, h1b', h1n, h2a, h2b', h2n, h12⟩ :=
    exists_two_aniso_perp_orth (k := k) hk ε (b' := b - (fiveForm k ε b a * (fiveForm k ε a a)⁻¹) • a) ha
      (by
        rw [fiveForm_sub_left, fiveForm_smul_left, mul_assoc, inv_mul_cancel₀ ha, mul_one, sub_self])
  have hb_eq : b = (b - (fiveForm k ε b a * (fiveForm k ε a a)⁻¹) • a) +
      (fiveForm k ε b a * (fiveForm k ε a a)⁻¹) • a := by abel
  have key : ∀ z, fiveForm k ε z a = 0 →
      fiveForm k ε z (b - (fiveForm k ε b a * (fiveForm k ε a a)⁻¹) • a) = 0 →
      fiveForm k ε z b = 0 := by
    intro z hza hzb
    rw [hb_eq, fiveForm_add_right, fiveForm_smul_right, hzb, hza, mul_zero, add_zero]
  exact ⟨w₁, w₂, h1a, key w₁ h1a h1b', h1n, h2a, key w₂ h2a h2b', h2n, h12⟩

end FiveWalk

end CFSG.OddTranspositions.PartThree
