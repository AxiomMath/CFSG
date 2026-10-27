module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.ElementaryRowOperations

public section

namespace CFSG.StandardType.FF81.RootFusionLin

open Matrix

variable (r m : ℕ)

@[expose] def actA (P : GL (Fin r) (ZMod 2)) (R : GL (Fin m) (ZMod 2))
    (a : Matrix (Fin r) (Fin m) (ZMod 2)) : Matrix (Fin r) (Fin m) (ZMod 2) :=
  (P : Matrix (Fin r) (Fin r) (ZMod 2)) * a *
    ((R⁻¹ : GL (Fin m) (ZMod 2)) : Matrix (Fin m) (Fin m) (ZMod 2))

@[expose] def actB (P : GL (Fin r) (ZMod 2)) (R : GL (Fin m) (ZMod 2))
    (b : Matrix (Fin m) (Fin r) (ZMod 2)) : Matrix (Fin m) (Fin r) (ZMod 2) :=
  (R : Matrix (Fin m) (Fin m) (ZMod 2)) * b *
    ((P⁻¹ : GL (Fin r) (ZMod 2)) : Matrix (Fin r) (Fin r) (ZMod 2))

private theorem mod_one_add_transvection {n : ℕ} (j k : Fin n) (hjk : j ≠ k) :
    (1 : Matrix (Fin n) (Fin n) (ZMod 2)) +
      (Matrix.GeneralLinearGroup.transvection j k hjk (1 : ZMod 2) :
        Matrix (Fin n) (Fin n) (ZMod 2)) = Matrix.single j k (1 : ZMod 2) := by
  rw [show (Matrix.GeneralLinearGroup.transvection j k hjk (1 : ZMod 2) :
      Matrix (Fin n) (Fin n) (ZMod 2)) = Matrix.transvection j k (1 : ZMod 2) from rfl,
    Matrix.transvection]
  ext a b
  simp only [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
  rw [CharTwo.add_cancel_left]

private theorem mod_transvection_inv {n : ℕ} (j k : Fin n) (hjk : j ≠ k) :
    (Matrix.GeneralLinearGroup.transvection j k hjk (1 : ZMod 2))⁻¹ =
      Matrix.GeneralLinearGroup.transvection j k hjk (1 : ZMod 2) := by
  apply inv_eq_of_mul_eq_one_right
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_one]
  rw [show (Matrix.GeneralLinearGroup.transvection j k hjk (1 : ZMod 2) :
      Matrix (Fin n) (Fin n) (ZMod 2)) = Matrix.transvection j k (1 : ZMod 2) from rfl,
    Matrix.transvection_mul_transvection_same (i := j) (j := k) hjk (1 : ZMod 2) (1 : ZMod 2),
    show (1 : ZMod 2) + 1 = 0 from rfl, Matrix.transvection_zero]

private lemma mod_add_mul_transvection_right {p n : ℕ} (j k : Fin n) (hjk : j ≠ k)
    (a : Matrix (Fin p) (Fin n) (ZMod 2)) :
    a + a * (Matrix.GeneralLinearGroup.transvection j k hjk (1 : ZMod 2) :
      Matrix (Fin n) (Fin n) (ZMod 2)) = a * Matrix.single j k (1 : ZMod 2) := by
  have h : (1 : Matrix (Fin n) (Fin n) (ZMod 2)) +
      (Matrix.GeneralLinearGroup.transvection j k hjk (1 : ZMod 2) :
        Matrix (Fin n) (Fin n) (ZMod 2)) = Matrix.single j k (1 : ZMod 2) :=
    mod_one_add_transvection j k hjk
  calc a + a * ↑(Matrix.GeneralLinearGroup.transvection j k hjk (1 : ZMod 2))
      = a * (1 : Matrix (Fin n) (Fin n) (ZMod 2)) +
          a * ↑(Matrix.GeneralLinearGroup.transvection j k hjk (1 : ZMod 2)) := by
          rw [Matrix.mul_one]
    _ = a * Matrix.single j k (1 : ZMod 2) := by rw [← Matrix.mul_add, h]

private lemma mod_add_mul_transvection_left {n q : ℕ} (j k : Fin n) (hjk : j ≠ k)
    (b : Matrix (Fin n) (Fin q) (ZMod 2)) :
    b + (Matrix.GeneralLinearGroup.transvection j k hjk (1 : ZMod 2) :
      Matrix (Fin n) (Fin n) (ZMod 2)) * b = Matrix.single j k (1 : ZMod 2) * b := by
  have h : (1 : Matrix (Fin n) (Fin n) (ZMod 2)) +
      (Matrix.GeneralLinearGroup.transvection j k hjk (1 : ZMod 2) :
        Matrix (Fin n) (Fin n) (ZMod 2)) = Matrix.single j k (1 : ZMod 2) :=
    mod_one_add_transvection j k hjk
  calc b + ↑(Matrix.GeneralLinearGroup.transvection j k hjk (1 : ZMod 2)) * b
      = (1 : Matrix (Fin n) (Fin n) (ZMod 2)) * b +
          ↑(Matrix.GeneralLinearGroup.transvection j k hjk (1 : ZMod 2)) * b := by
          rw [Matrix.one_mul]
    _ = Matrix.single j k (1 : ZMod 2) * b := by rw [← Matrix.add_mul, h]

private lemma mod_zmod_two_eq_zero_or_one (c : ZMod 2) : c = 0 ∨ c = 1 := by
  rcases CharTwo.natCast_cases (ZMod 2) c.val with h | h
  · left; rw [← ZMod.natCast_zmod_val c]; exact h
  · right; rw [← ZMod.natCast_zmod_val c]; exact h

private lemma mod_single_mul_single_ne {n : ℕ} (i j k l : Fin n) (h : j ≠ k) :
    (Matrix.single i j (1 : ZMod 2) : Matrix (Fin n) (Fin n) (ZMod 2)) *
      Matrix.single k l (1 : ZMod 2) = 0 :=
  Matrix.single_mul_single_of_ne (1 : ZMod 2) i j k h (1 : ZMod 2)

private theorem mod_offdiag_left_mem
    (W : AddSubgroup (Matrix (Fin r) (Fin m) (ZMod 2)))
    (hW : ∀ (P : GL (Fin r) (ZMod 2)) (R : GL (Fin m) (ZMod 2)), ∀ a ∈ W,
      actA r m P R a ∈ W)
    {X : Matrix (Fin r) (Fin m) (ZMod 2)} (hX : X ∈ W)
    (i p : Fin r) (hip : i ≠ p) (c : ZMod 2) :
    Matrix.single i p c * X ∈ W := by
  have h1 : Matrix.single i p (1 : ZMod 2) * X ∈ W := by
    have hPW : (Matrix.GeneralLinearGroup.transvection i p hip (1 : ZMod 2) :
        Matrix (Fin r) (Fin r) (ZMod 2)) * X ∈ W := by
      have := hW (Matrix.GeneralLinearGroup.transvection i p hip (1 : ZMod 2)) 1 X hX
      simpa [actA, Matrix.GeneralLinearGroup.coe_one] using this
    have heq : Matrix.single i p (1 : ZMod 2) * X =
        (Matrix.GeneralLinearGroup.transvection i p hip (1 : ZMod 2) :
          Matrix (Fin r) (Fin r) (ZMod 2)) * X -
            (1 : Matrix (Fin r) (Fin r) (ZMod 2)) * X := by
      rw [show (Matrix.GeneralLinearGroup.transvection i p hip (1 : ZMod 2) :
            Matrix (Fin r) (Fin r) (ZMod 2)) =
          (1 : Matrix (Fin r) (Fin r) (ZMod 2)) + Matrix.single i p (1 : ZMod 2) from rfl,
        Matrix.add_mul, Matrix.one_mul]
      abel
    rw [heq]
    exact W.sub_mem hPW (by simpa using hX)
  rcases mod_zmod_two_eq_zero_or_one c with hc | hc
  · rw [hc, Matrix.single_zero]; simp
  · rw [hc]; exact h1

private theorem mod_single_left_mem
    (W : AddSubgroup (Matrix (Fin r) (Fin m) (ZMod 2)))
    (hW : ∀ (P : GL (Fin r) (ZMod 2)) (R : GL (Fin m) (ZMod 2)), ∀ a ∈ W,
      actA r m P R a ∈ W)
    {X : Matrix (Fin r) (Fin m) (ZMod 2)} (hX : X ∈ W) (i p : Fin r) (c : ZMod 2) :
    Matrix.single i p c * X ∈ W := by
  have hdiag : Matrix.single i i (1 : ZMod 2) * X ∈ W := by
    by_cases h : ∃ q : Fin r, q ≠ i
    · obtain ⟨q, hq⟩ := h
      have heq : Matrix.single i i (1 : ZMod 2) * X =
          Matrix.single i q (1 : ZMod 2) * (Matrix.single q i (1 : ZMod 2) * X) := by
        rw [← Matrix.mul_assoc, Matrix.single_mul_single_same]
        simp
      rw [heq]
      exact mod_offdiag_left_mem r m W hW
        (mod_offdiag_left_mem r m W hW hX q i hq 1) i q hq.symm 1
    · have hsubs : Subsingleton (Fin r) :=
        ⟨fun a b => by
          have ha : a = i := by_contra fun ha => h ⟨a, ha⟩
          have hb : b = i := by_contra fun hb => h ⟨b, hb⟩
          rw [ha, hb]⟩
      have hone : (Matrix.single i i (1 : ZMod 2) : Matrix (Fin r) (Fin r) (ZMod 2)) = 1 := by
        ext a b
        rw [Matrix.single_apply, Matrix.one_apply, hsubs.elim a i, hsubs.elim b i]
        simp
      rw [hone]; simpa using hX
  rcases mod_zmod_two_eq_zero_or_one c with hc | hc
  · rw [hc, Matrix.single_zero]; simp
  · rw [hc]
    rcases eq_or_ne i p with rfl | hip
    · exact hdiag
    · exact mod_offdiag_left_mem r m W hW hX i p hip 1

private theorem mod_offdiag_right_mem
    (W : AddSubgroup (Matrix (Fin r) (Fin m) (ZMod 2)))
    (hW : ∀ (P : GL (Fin r) (ZMod 2)) (R : GL (Fin m) (ZMod 2)), ∀ a ∈ W,
      actA r m P R a ∈ W)
    {X : Matrix (Fin r) (Fin m) (ZMod 2)} (hX : X ∈ W)
    (q j : Fin m) (hqj : q ≠ j) (c : ZMod 2) :
    X * Matrix.single q j c ∈ W := by
  have h1 : X * Matrix.single q j (1 : ZMod 2) ∈ W := by
    have hcoee : (((Matrix.GeneralLinearGroup.transvection q j hqj (1 : ZMod 2))⁻¹ :
          GL (Fin m) (ZMod 2)) : Matrix (Fin m) (Fin m) (ZMod 2)) =
        (Matrix.GeneralLinearGroup.transvection q j hqj (1 : ZMod 2) :
          Matrix (Fin m) (Fin m) (ZMod 2)) := by
      rw [mod_transvection_inv q j hqj]
    have hRW : X * (Matrix.GeneralLinearGroup.transvection q j hqj (1 : ZMod 2) :
        Matrix (Fin m) (Fin m) (ZMod 2)) ∈ W := by
      have := hW 1 (Matrix.GeneralLinearGroup.transvection q j hqj (1 : ZMod 2)) X hX
      simpa [actA, Matrix.GeneralLinearGroup.coe_one, hcoee] using this
    have heq : X * Matrix.single q j (1 : ZMod 2) =
        X * (Matrix.GeneralLinearGroup.transvection q j hqj (1 : ZMod 2) :
          Matrix (Fin m) (Fin m) (ZMod 2)) -
            X * (1 : Matrix (Fin m) (Fin m) (ZMod 2)) := by
      rw [show (Matrix.GeneralLinearGroup.transvection q j hqj (1 : ZMod 2) :
            Matrix (Fin m) (Fin m) (ZMod 2)) =
          (1 : Matrix (Fin m) (Fin m) (ZMod 2)) + Matrix.single q j (1 : ZMod 2) from rfl,
        Matrix.mul_add, Matrix.mul_one]
      abel
    rw [heq]
    exact W.sub_mem hRW (by simpa using hX)
  rcases mod_zmod_two_eq_zero_or_one c with hc | hc
  · rw [hc, Matrix.single_zero]; simp
  · rw [hc]; exact h1

private theorem mod_single_right_mem
    (W : AddSubgroup (Matrix (Fin r) (Fin m) (ZMod 2)))
    (hW : ∀ (P : GL (Fin r) (ZMod 2)) (R : GL (Fin m) (ZMod 2)), ∀ a ∈ W,
      actA r m P R a ∈ W)
    {X : Matrix (Fin r) (Fin m) (ZMod 2)} (hX : X ∈ W) (q j : Fin m) (c : ZMod 2) :
    X * Matrix.single q j c ∈ W := by
  have hdiag : X * Matrix.single q q (1 : ZMod 2) ∈ W := by
    by_cases h : ∃ t : Fin m, t ≠ q
    · obtain ⟨t, ht⟩ := h
      have heq : X * Matrix.single q q (1 : ZMod 2) =
          (X * Matrix.single q t (1 : ZMod 2)) * Matrix.single t q (1 : ZMod 2) := by
        rw [Matrix.mul_assoc, Matrix.single_mul_single_same]
        simp
      rw [heq]
      exact mod_offdiag_right_mem r m W hW
        (mod_offdiag_right_mem r m W hW hX q t ht.symm 1) t q ht 1
    · have hsubs : Subsingleton (Fin m) :=
        ⟨fun a b => by
          have ha : a = q := by_contra fun ha => h ⟨a, ha⟩
          have hb : b = q := by_contra fun hb => h ⟨b, hb⟩
          rw [ha, hb]⟩
      have hone : (Matrix.single q q (1 : ZMod 2) : Matrix (Fin m) (Fin m) (ZMod 2)) = 1 := by
        ext a b
        rw [Matrix.single_apply, Matrix.one_apply, hsubs.elim a q, hsubs.elim b q]
        simp
      rw [hone]; simpa using hX
  rcases mod_zmod_two_eq_zero_or_one c with hc | hc
  · rw [hc, Matrix.single_zero]; simp
  · rw [hc]
    rcases eq_or_ne q j with rfl | hqj
    · exact hdiag
    · exact mod_offdiag_right_mem r m W hW hX q j hqj 1

private theorem mod_deltaR_mem
    (W : AddSubgroup (Matrix (Fin r) (Fin m) (ZMod 2) × Matrix (Fin m) (Fin r) (ZMod 2)))
    (hW : ∀ (P : GL (Fin r) (ZMod 2)) (R : GL (Fin m) (ZMod 2)), ∀ w ∈ W,
      (actA r m P R w.1, actB r m P R w.2) ∈ W)
    {j k : Fin m} (hjk : j ≠ k)
    {w : Matrix (Fin r) (Fin m) (ZMod 2) × Matrix (Fin m) (Fin r) (ZMod 2)} (hw : w ∈ W) :
    (w.1 * Matrix.single j k (1 : ZMod 2), Matrix.single j k (1 : ZMod 2) * w.2) ∈ W := by
  have hcoee : (((Matrix.GeneralLinearGroup.transvection j k hjk (1 : ZMod 2))⁻¹ :
        GL (Fin m) (ZMod 2)) : Matrix (Fin m) (Fin m) (ZMod 2)) =
      (Matrix.GeneralLinearGroup.transvection j k hjk (1 : ZMod 2) :
        Matrix (Fin m) (Fin m) (ZMod 2)) := by
    rw [mod_transvection_inv j k hjk]
  have hsum : (w.1 + actA r m 1 (Matrix.GeneralLinearGroup.transvection j k hjk (1 : ZMod 2)) w.1,
      w.2 + actB r m 1 (Matrix.GeneralLinearGroup.transvection j k hjk (1 : ZMod 2)) w.2) ∈ W :=
    W.add_mem hw (hW 1 _ w hw)
  have h1 : w.1 * Matrix.single j k (1 : ZMod 2) =
      w.1 + actA r m 1 (Matrix.GeneralLinearGroup.transvection j k hjk (1 : ZMod 2)) w.1 := by
    simp only [actA, Matrix.GeneralLinearGroup.coe_one, Matrix.one_mul, hcoee]
    exact (mod_add_mul_transvection_right j k hjk w.1).symm
  have h2 : Matrix.single j k (1 : ZMod 2) * w.2 =
      w.2 + actB r m 1 (Matrix.GeneralLinearGroup.transvection j k hjk (1 : ZMod 2)) w.2 := by
    simp only [actB, inv_one, Matrix.GeneralLinearGroup.coe_one, Matrix.mul_one]
    exact (mod_add_mul_transvection_left j k hjk w.2).symm
  rw [h1, h2]
  exact hsum

private theorem mod_deltaL_mem
    (W : AddSubgroup (Matrix (Fin r) (Fin m) (ZMod 2) × Matrix (Fin m) (Fin r) (ZMod 2)))
    (hW : ∀ (P : GL (Fin r) (ZMod 2)) (R : GL (Fin m) (ZMod 2)), ∀ w ∈ W,
      (actA r m P R w.1, actB r m P R w.2) ∈ W)
    {i j : Fin r} (hij : i ≠ j)
    {w : Matrix (Fin r) (Fin m) (ZMod 2) × Matrix (Fin m) (Fin r) (ZMod 2)} (hw : w ∈ W) :
    (Matrix.single i j (1 : ZMod 2) * w.1, w.2 * Matrix.single i j (1 : ZMod 2)) ∈ W := by
  have hcoee : (((Matrix.GeneralLinearGroup.transvection i j hij (1 : ZMod 2))⁻¹ :
        GL (Fin r) (ZMod 2)) : Matrix (Fin r) (Fin r) (ZMod 2)) =
      (Matrix.GeneralLinearGroup.transvection i j hij (1 : ZMod 2) :
        Matrix (Fin r) (Fin r) (ZMod 2)) := by
    rw [mod_transvection_inv i j hij]
  have hsum : (w.1 + actA r m (Matrix.GeneralLinearGroup.transvection i j hij (1 : ZMod 2)) 1 w.1,
      w.2 + actB r m (Matrix.GeneralLinearGroup.transvection i j hij (1 : ZMod 2)) 1 w.2) ∈ W :=
    W.add_mem hw (hW _ 1 w hw)
  have h1 : Matrix.single i j (1 : ZMod 2) * w.1 =
      w.1 + actA r m (Matrix.GeneralLinearGroup.transvection i j hij (1 : ZMod 2)) 1 w.1 := by
    simp only [actA, inv_one, Matrix.GeneralLinearGroup.coe_one, Matrix.mul_one]
    exact (mod_add_mul_transvection_left i j hij w.1).symm
  have h2 : w.2 * Matrix.single i j (1 : ZMod 2) =
      w.2 + actB r m (Matrix.GeneralLinearGroup.transvection i j hij (1 : ZMod 2)) 1 w.2 := by
    simp only [actB, Matrix.GeneralLinearGroup.coe_one, Matrix.one_mul, hcoee]
    exact (mod_add_mul_transvection_right i j hij w.2).symm
  rw [h1, h2]
  exact hsum

private lemma mod_exists_ne_ne {n : ℕ} (h : 3 ≤ n) {j l : Fin n} (hjl : j ≠ l) :
    ∃ k : Fin n, k ≠ j ∧ k ≠ l := by
  have hcard : ({j, l} : Finset (Fin n)).card < (Finset.univ : Finset (Fin n)).card := by
    rw [Finset.card_univ, Fintype.card_fin, Finset.card_pair hjl]
    omega
  obtain ⟨k, _, hk⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  rw [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
  exact ⟨k, hk.1, hk.2⟩

theorem eq_bot_or_eq_top_of_actA (W : AddSubgroup (Matrix (Fin r) (Fin m) (ZMod 2)))
    (hW : ∀ (P : GL (Fin r) (ZMod 2)) (R : GL (Fin m) (ZMod 2)), ∀ a ∈ W, actA r m P R a ∈ W) :
    W = ⊥ ∨ W = ⊤ := by
  by_cases hbot : W = ⊥
  · exact Or.inl hbot
  · right
    have hex : ∃ A ∈ W, A ≠ 0 := by
      by_contra h
      exact hbot (le_antisymm (fun x hx => by
        rw [AddSubgroup.mem_bot]
        by_contra hx0
        exact h ⟨x, hx, hx0⟩) bot_le)
    obtain ⟨A, hAW, hA0⟩ := hex
    have hentry : ∃ p : Fin r, ∃ q : Fin m, A p q ≠ 0 := by
      by_contra h
      exact hA0 (funext fun i => funext fun j => by
        by_contra hij
        exact h ⟨i, j, hij⟩)
    obtain ⟨p, q, hpq⟩ := hentry
    have hpq1 : A p q = 1 := by
      rcases mod_zmod_two_eq_zero_or_one (A p q) with h | h
      · exact absurd h hpq
      · exact h
    have hsingle : ∀ i j,
        (Matrix.single i j (1 : ZMod 2) : Matrix (Fin r) (Fin m) (ZMod 2)) ∈ W := by
      intro i j
      have h1 : Matrix.single i p (1 : ZMod 2) * A ∈ W :=
        mod_single_left_mem r m W hW hAW i p 1
      have h2 : (Matrix.single i p (1 : ZMod 2) * A) * Matrix.single q j (1 : ZMod 2) ∈ W :=
        mod_single_right_mem r m W hW h1 q j 1
      have heq : (Matrix.single i p (1 : ZMod 2) * A) * Matrix.single q j (1 : ZMod 2) =
          Matrix.single i j (1 : ZMod 2) := by
        rw [Matrix.single_mul_mul_single, hpq1]
        simp
      rwa [heq] at h2
    apply le_antisymm le_top
    intro M _
    refine Matrix.induction_on' M ?_ ?_ ?_
    · exact W.zero_mem
    · intro P Q hP hQ; exact W.add_mem hP hQ
    · intro i j c
      rcases mod_zmod_two_eq_zero_or_one c with hc | hc
      · rw [hc, Matrix.single_zero]; exact W.zero_mem
      · rw [hc]; exact hsingle i j

private theorem mod_fst_eq_zero_of_three_le_m {a : Matrix (Fin r) (Fin m) (ZMod 2)}
    {b : Matrix (Fin m) (Fin r) (ZMod 2)} (hm : 3 ≤ m)
    (W : AddSubgroup (Matrix (Fin r) (Fin m) (ZMod 2) × Matrix (Fin m) (Fin r) (ZMod 2)))
    (hW : ∀ (P : GL (Fin r) (ZMod 2)) (R : GL (Fin m) (ZMod 2)), ∀ w ∈ W,
      (actA r m P R w.1, actB r m P R w.2) ∈ W)
    (hA : ∀ a, (a, (0 : Matrix (Fin m) (Fin r) (ZMod 2))) ∈ W → a = 0)
    (hw : (a, b) ∈ W) : a = 0 := by
  have hza : ∀ {j l : Fin m}, j ≠ l → a * Matrix.single j l (1 : ZMod 2) = 0 := by
    intro j l hjl
    obtain ⟨k, hkj, hkl⟩ := mod_exists_ne_ne hm hjl
    have hjk : j ≠ k := fun h => hkj h.symm
    have h1 : (a * Matrix.single j k (1 : ZMod 2),
        Matrix.single j k (1 : ZMod 2) * b) ∈ W :=
      mod_deltaR_mem r m W hW hjk hw
    have h2 : ((a * Matrix.single j k (1 : ZMod 2)) * Matrix.single k l (1 : ZMod 2),
        Matrix.single k l (1 : ZMod 2) * (Matrix.single j k (1 : ZMod 2) * b)) ∈ W :=
      mod_deltaR_mem r m W hW hkl h1
    have h2a : (a * Matrix.single j k (1 : ZMod 2)) * Matrix.single k l (1 : ZMod 2) =
        a * Matrix.single j l (1 : ZMod 2) := by
      rw [Matrix.mul_assoc, Matrix.single_mul_single_same]
      simp
    have h2b : Matrix.single k l (1 : ZMod 2) * (Matrix.single j k (1 : ZMod 2) * b) = 0 := by
      rw [← Matrix.mul_assoc, mod_single_mul_single_ne k l j k hjl.symm]
      simp
    rw [h2a, h2b] at h2
    exact hA _ h2
  ext x i
  obtain ⟨l, hl⟩ : ∃ l : Fin m, l ≠ i :=
    Fintype.exists_ne_of_one_lt_card (by rw [Fintype.card_fin]; omega) i
  have h0 : (a * Matrix.single i l (1 : ZMod 2)) x l = 0 := by
    rw [hza (Ne.symm hl)]; rfl
  rwa [Matrix.mul_single_apply_same, mul_one] at h0

private theorem mod_snd_eq_zero_of_three_le_m {a : Matrix (Fin r) (Fin m) (ZMod 2)}
    {b : Matrix (Fin m) (Fin r) (ZMod 2)} (hm : 3 ≤ m)
    (W : AddSubgroup (Matrix (Fin r) (Fin m) (ZMod 2) × Matrix (Fin m) (Fin r) (ZMod 2)))
    (hW : ∀ (P : GL (Fin r) (ZMod 2)) (R : GL (Fin m) (ZMod 2)), ∀ w ∈ W,
      (actA r m P R w.1, actB r m P R w.2) ∈ W)
    (hB : ∀ b, ((0 : Matrix (Fin r) (Fin m) (ZMod 2)), b) ∈ W → b = 0)
    (hw : (a, b) ∈ W) : b = 0 := by
  have hzb : ∀ {j l : Fin m}, j ≠ l → Matrix.single j l (1 : ZMod 2) * b = 0 := by
    intro j l hjl
    obtain ⟨k, hkj, hkl⟩ := mod_exists_ne_ne hm hjl
    have hjk : j ≠ k := fun h => hkj h.symm
    have h1 : (a * Matrix.single k l (1 : ZMod 2),
        Matrix.single k l (1 : ZMod 2) * b) ∈ W :=
      mod_deltaR_mem r m W hW hkl hw
    have h2 : ((a * Matrix.single k l (1 : ZMod 2)) * Matrix.single j k (1 : ZMod 2),
        Matrix.single j k (1 : ZMod 2) * (Matrix.single k l (1 : ZMod 2) * b)) ∈ W :=
      mod_deltaR_mem r m W hW hjk h1
    have h2a : (a * Matrix.single k l (1 : ZMod 2)) * Matrix.single j k (1 : ZMod 2) = 0 := by
      rw [Matrix.mul_assoc, mod_single_mul_single_ne k l j k hjl.symm]
      simp
    have h2b : Matrix.single j k (1 : ZMod 2) * (Matrix.single k l (1 : ZMod 2) * b) =
        Matrix.single j l (1 : ZMod 2) * b := by
      rw [← Matrix.mul_assoc, Matrix.single_mul_single_same]
      simp
    rw [h2a, h2b] at h2
    exact hB _ h2
  ext row col
  obtain ⟨l, hl⟩ : ∃ l : Fin m, l ≠ row :=
    Fintype.exists_ne_of_one_lt_card (by rw [Fintype.card_fin]; omega) row
  have h0 : (Matrix.single l row (1 : ZMod 2) * b) l col = 0 := by
    rw [hzb hl]; rfl
  rwa [Matrix.single_mul_apply_same, one_mul] at h0

private theorem mod_fst_eq_zero_of_three_le_r {a : Matrix (Fin r) (Fin m) (ZMod 2)}
    {b : Matrix (Fin m) (Fin r) (ZMod 2)} (hr : 3 ≤ r)
    (W : AddSubgroup (Matrix (Fin r) (Fin m) (ZMod 2) × Matrix (Fin m) (Fin r) (ZMod 2)))
    (hW : ∀ (P : GL (Fin r) (ZMod 2)) (R : GL (Fin m) (ZMod 2)), ∀ w ∈ W,
      (actA r m P R w.1, actB r m P R w.2) ∈ W)
    (hA : ∀ a, (a, (0 : Matrix (Fin m) (Fin r) (ZMod 2))) ∈ W → a = 0)
    (hw : (a, b) ∈ W) : a = 0 := by
  have hza : ∀ {i l : Fin r}, i ≠ l → Matrix.single i l (1 : ZMod 2) * a = 0 := by
    intro i l hil
    obtain ⟨j, hji, hjl⟩ := mod_exists_ne_ne hr hil
    have hij : i ≠ j := fun h => hji h.symm
    have h1 : (Matrix.single j l (1 : ZMod 2) * a,
        b * Matrix.single j l (1 : ZMod 2)) ∈ W :=
      mod_deltaL_mem r m W hW hjl hw
    have h2 : (Matrix.single i j (1 : ZMod 2) * (Matrix.single j l (1 : ZMod 2) * a),
        (b * Matrix.single j l (1 : ZMod 2)) * Matrix.single i j (1 : ZMod 2)) ∈ W :=
      mod_deltaL_mem r m W hW hij h1
    have h2a : Matrix.single i j (1 : ZMod 2) * (Matrix.single j l (1 : ZMod 2) * a) =
        Matrix.single i l (1 : ZMod 2) * a := by
      rw [← Matrix.mul_assoc, Matrix.single_mul_single_same]
      simp
    have h2b : (b * Matrix.single j l (1 : ZMod 2)) * Matrix.single i j (1 : ZMod 2) = 0 := by
      rw [Matrix.mul_assoc, mod_single_mul_single_ne j l i j hil.symm]
      simp
    rw [h2a, h2b] at h2
    exact hA _ h2
  ext row col
  obtain ⟨i, hi⟩ : ∃ i : Fin r, i ≠ row :=
    Fintype.exists_ne_of_one_lt_card (by rw [Fintype.card_fin]; omega) row
  have h0 : (Matrix.single i row (1 : ZMod 2) * a) i col = 0 := by
    rw [hza hi]; rfl
  rwa [Matrix.single_mul_apply_same, one_mul] at h0

private theorem mod_snd_eq_zero_of_three_le_r {a : Matrix (Fin r) (Fin m) (ZMod 2)}
    {b : Matrix (Fin m) (Fin r) (ZMod 2)} (hr : 3 ≤ r)
    (W : AddSubgroup (Matrix (Fin r) (Fin m) (ZMod 2) × Matrix (Fin m) (Fin r) (ZMod 2)))
    (hW : ∀ (P : GL (Fin r) (ZMod 2)) (R : GL (Fin m) (ZMod 2)), ∀ w ∈ W,
      (actA r m P R w.1, actB r m P R w.2) ∈ W)
    (hB : ∀ b, ((0 : Matrix (Fin r) (Fin m) (ZMod 2)), b) ∈ W → b = 0)
    (hw : (a, b) ∈ W) : b = 0 := by
  have hzb : ∀ {i l : Fin r}, i ≠ l → b * Matrix.single i l (1 : ZMod 2) = 0 := by
    intro i l hil
    obtain ⟨j, hji, hjl⟩ := mod_exists_ne_ne hr hil
    have hij : i ≠ j := fun h => hji h.symm
    have h1 : (Matrix.single i j (1 : ZMod 2) * a,
        b * Matrix.single i j (1 : ZMod 2)) ∈ W :=
      mod_deltaL_mem r m W hW hij hw
    have h2 : (Matrix.single j l (1 : ZMod 2) * (Matrix.single i j (1 : ZMod 2) * a),
        (b * Matrix.single i j (1 : ZMod 2)) * Matrix.single j l (1 : ZMod 2)) ∈ W :=
      mod_deltaL_mem r m W hW hjl h1
    have h2a : Matrix.single j l (1 : ZMod 2) * (Matrix.single i j (1 : ZMod 2) * a) = 0 := by
      rw [← Matrix.mul_assoc, mod_single_mul_single_ne j l i j hil.symm]
      simp
    have h2b : (b * Matrix.single i j (1 : ZMod 2)) * Matrix.single j l (1 : ZMod 2) =
        b * Matrix.single i l (1 : ZMod 2) := by
      rw [Matrix.mul_assoc, Matrix.single_mul_single_same]
      simp
    rw [h2a, h2b] at h2
    exact hB _ h2
  ext row col
  obtain ⟨l, hl⟩ : ∃ l : Fin r, l ≠ col :=
    Fintype.exists_ne_of_one_lt_card (by rw [Fintype.card_fin]; omega) col
  have h0 : (b * Matrix.single col l (1 : ZMod 2)) row l = 0 := by
    rw [hzb (Ne.symm hl)]; rfl
  rwa [Matrix.mul_single_apply_same, mul_one] at h0

theorem eq_bot_of_actA_actB (h3 : 3 ≤ r ∨ 3 ≤ m)
    (W : AddSubgroup (Matrix (Fin r) (Fin m) (ZMod 2) × Matrix (Fin m) (Fin r) (ZMod 2)))
    (hW : ∀ (P : GL (Fin r) (ZMod 2)) (R : GL (Fin m) (ZMod 2)), ∀ w ∈ W,
      (actA r m P R w.1, actB r m P R w.2) ∈ W)
    (hA : ∀ a, (a, (0 : Matrix (Fin m) (Fin r) (ZMod 2))) ∈ W → a = 0)
    (hB : ∀ b, ((0 : Matrix (Fin r) (Fin m) (ZMod 2)), b) ∈ W → b = 0) : W = ⊥ := by
  apply le_antisymm _ bot_le
  rintro ⟨a, b⟩ hw
  rw [AddSubgroup.mem_bot]
  apply Prod.ext
  · by_cases hm : 3 ≤ m
    · exact mod_fst_eq_zero_of_three_le_m r m hm W hW hA hw
    · exact mod_fst_eq_zero_of_three_le_r r m (by omega) W hW hA hw
  · by_cases hm : 3 ≤ m
    · exact mod_snd_eq_zero_of_three_le_m r m hm W hW hB hw
    · exact mod_snd_eq_zero_of_three_le_r r m (by omega) W hW hB hw

theorem eq_bot_or_actA_or_actB (h3 : 3 ≤ r ∨ 3 ≤ m)
    (W : AddSubgroup (Matrix (Fin r) (Fin m) (ZMod 2) × Matrix (Fin m) (Fin r) (ZMod 2)))
    (hW : ∀ (P : GL (Fin r) (ZMod 2)) (R : GL (Fin m) (ZMod 2)), ∀ w ∈ W,
      (actA r m P R w.1, actB r m P R w.2) ∈ W) :
    W = ⊥ ∨ (∀ a, (a, (0 : Matrix (Fin m) (Fin r) (ZMod 2))) ∈ W) ∨
      (∀ b, ((0 : Matrix (Fin r) (Fin m) (ZMod 2)), b) ∈ W) := by
  let Wa : AddSubgroup (Matrix (Fin r) (Fin m) (ZMod 2)) :=
    W.comap (AddMonoidHom.inl (Matrix (Fin r) (Fin m) (ZMod 2)) (Matrix (Fin m) (Fin r) (ZMod 2)))
  let Wb : AddSubgroup (Matrix (Fin m) (Fin r) (ZMod 2)) :=
    W.comap (AddMonoidHom.inr (Matrix (Fin r) (Fin m) (ZMod 2)) (Matrix (Fin m) (Fin r) (ZMod 2)))
  have hWa : ∀ (P : GL (Fin r) (ZMod 2)) (R : GL (Fin m) (ZMod 2)), ∀ a ∈ Wa,
      actA r m P R a ∈ Wa := by
    intro P R a ha
    have h := hW P R (a, 0) ha
    simpa [Wa, actB] using h
  have hWb : ∀ (R : GL (Fin m) (ZMod 2)) (P : GL (Fin r) (ZMod 2)), ∀ b ∈ Wb,
      actA m r R P b ∈ Wb := by
    intro R P b hb
    have h := hW P R (0, b) hb
    simpa [Wb, actA, actB] using h
  rcases eq_bot_or_eq_top_of_actA r m Wa hWa with ha | ha
  · rcases eq_bot_or_eq_top_of_actA m r Wb hWb with hb | hb
    · left
      refine eq_bot_of_actA_actB r m h3 W hW (fun a h => ?_) (fun b h => ?_)
      · have h' : a ∈ Wa := h
        rw [ha] at h'
        simpa using h'
      · have h' : b ∈ Wb := h
        rw [hb] at h'
        simpa using h'
    · right; right
      intro b
      have h' : b ∈ Wb := by rw [hb]; trivial
      exact h'
  · right; left
    intro a
    have h' : a ∈ Wa := by rw [ha]; trivial
    exact h'

end CFSG.StandardType.FF81.RootFusionLin

end
