module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Tactic.NoncommRing
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.RankThree.PartTwo.Sec13.K135SF

private lemma sf4_mem_ker_iff {n : ℕ} (g : Matrix (Fin n) (Fin n) (ZMod 3))
    (v : Fin n → ZMod 3) :
    v ∈ LinearMap.ker (Matrix.toLin' (g - 1)) ↔ Matrix.mulVec g v = v := by
  rw [LinearMap.mem_ker, Matrix.toLin'_apply, Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero]

private lemma sf4_natCard_fix {n : ℕ} (g : Matrix (Fin n) (Fin n) (ZMod 3)) :
    Nat.card {v : Fin n → ZMod 3 // Matrix.mulVec g v = v} =
      3 ^ Module.finrank (ZMod 3) (LinearMap.ker (Matrix.toLin' (g - 1))) := by
  have h := Module.natCard_eq_pow_finrank (K := ZMod 3)
    (V := LinearMap.ker (Matrix.toLin' (g - 1)))
  rw [Nat.card_zmod] at h
  rw [← h]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun v => (sf4_mem_ker_iff g v).symm)

private lemma sf4_top_le {n : ℕ} (a b : Matrix (Fin n) (Fin n) (ZMod 3))
    (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a) :
    (⊤ : Submodule (ZMod 3) (Fin n → ZMod 3)) ≤
      (LinearMap.ker (Matrix.toLin' (a - 1)) ⊔ LinearMap.ker (Matrix.toLin' (b - 1))) ⊔
        LinearMap.ker (Matrix.toLin' (a * b - 1)) := by
  have hba : b * a = a * b := hab.symm
  have e1 : a * (1 + a) = 1 + a := by rw [mul_add, mul_one, ha, add_comm]
  have e2 : b * (1 + b) = 1 + b := by rw [mul_add, mul_one, hb, add_comm]
  have f1 : a * (1 - a) = -(1 - a) := by rw [mul_sub, mul_one, ha, neg_sub]
  have f2 : b * (1 - b) = -(1 - b) := by rw [mul_sub, mul_one, hb, neg_sub]
  have hbmix : b * (1 - a) = (1 - a) * b := by
    rw [mul_sub, sub_mul, mul_one, one_mul, hba]
  have hab4 : a * b * ((1 - a) * (1 - b)) = (1 - a) * (1 - b) := by
    calc a * b * ((1 - a) * (1 - b)) = a * (b * (1 - a)) * (1 - b) := by simp only [mul_assoc]
      _ = a * ((1 - a) * b) * (1 - b) := by rw [hbmix]
      _ = a * (1 - a) * (b * (1 - b)) := by simp only [mul_assoc]
      _ = (-(1 - a)) * (-(1 - b)) := by rw [f1, f2]
      _ = (1 - a) * (1 - b) := neg_mul_neg _ _
  have h4 : (4 : Matrix (Fin n) (Fin n) (ZMod 3)) = 1 := by
    ext i j
    rw [Matrix.ofNat_apply, Matrix.one_apply]
    split_ifs <;> decide
  have hsum : (1 + a) * (1 + b) + (1 + a) * (1 - b) + (1 - a) * (1 + b) + (1 - a) * (1 - b)
      = 1 := by
    have h : (1 + a) * (1 + b) + (1 + a) * (1 - b) + (1 - a) * (1 + b) + (1 - a) * (1 - b)
        = (4 : Matrix (Fin n) (Fin n) (ZMod 3)) := by
      noncomm_ring
      simp
    rw [h]
    exact h4
  intro v _
  have hfix : ∀ (M g : Matrix (Fin n) (Fin n) (ZMod 3)), g * M = M →
      Matrix.mulVec g (Matrix.mulVec M v) = Matrix.mulVec M v := by
    intro M g hgM
    rw [Matrix.mulVec_mulVec, hgM]
  have hd : Matrix.mulVec ((1 + a) * (1 + b) + (1 + a) * (1 - b) + (1 - a) * (1 + b) +
      (1 - a) * (1 - b)) v = v := by
    rw [hsum, Matrix.one_mulVec]
  rw [Matrix.add_mulVec, Matrix.add_mulVec, Matrix.add_mulVec] at hd
  have m1 : Matrix.mulVec ((1 + a) * (1 + b)) v ∈ LinearMap.ker (Matrix.toLin' (a - 1)) :=
    (sf4_mem_ker_iff a _).2 (hfix ((1 + a) * (1 + b)) a (by rw [← mul_assoc, e1]))
  have m3 : Matrix.mulVec ((1 + a) * (1 - b)) v ∈ LinearMap.ker (Matrix.toLin' (a - 1)) :=
    (sf4_mem_ker_iff a _).2 (hfix ((1 + a) * (1 - b)) a (by rw [← mul_assoc, e1]))
  have m2 : Matrix.mulVec ((1 - a) * (1 + b)) v ∈ LinearMap.ker (Matrix.toLin' (b - 1)) :=
    (sf4_mem_ker_iff b _).2
      (hfix ((1 - a) * (1 + b)) b (by rw [← mul_assoc, hbmix, mul_assoc, e2]))
  have m4 : Matrix.mulVec ((1 - a) * (1 - b)) v ∈ LinearMap.ker (Matrix.toLin' (a * b - 1)) :=
    (sf4_mem_ker_iff (a * b) _).2 (hfix ((1 - a) * (1 - b)) (a * b) hab4)
  rw [← hd]
  have x13 : Matrix.mulVec ((1 + a) * (1 + b)) v + Matrix.mulVec ((1 + a) * (1 - b)) v ∈
      LinearMap.ker (Matrix.toLin' (a - 1)) := add_mem m1 m3
  exact add_mem (add_mem (Submodule.mem_sup_left (Submodule.mem_sup_left x13))
      (Submodule.mem_sup_left (Submodule.mem_sup_right m2)))
    (Submodule.mem_sup_right m4)

private lemma sf4_finrank_le {n : ℕ} (a b : Matrix (Fin n) (Fin n) (ZMod 3))
    (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a) :
    n ≤ Module.finrank (ZMod 3) (LinearMap.ker (Matrix.toLin' (a - 1))) +
      Module.finrank (ZMod 3) (LinearMap.ker (Matrix.toLin' (b - 1))) +
      Module.finrank (ZMod 3) (LinearMap.ker (Matrix.toLin' (a * b - 1))) := by
  have h1 := Submodule.finrank_mono (sf4_top_le a b ha hb hab)
  rw [finrank_top, Module.finrank_fin_fun] at h1
  have h2 := Submodule.finrank_add_le_finrank_add_finrank
    (LinearMap.ker (Matrix.toLin' (a - 1)) ⊔ LinearMap.ker (Matrix.toLin' (b - 1)))
    (LinearMap.ker (Matrix.toLin' (a * b - 1)))
  have h3 := Submodule.finrank_add_le_finrank_add_finrank
    (LinearMap.ker (Matrix.toLin' (a - 1))) (LinearMap.ker (Matrix.toLin' (b - 1)))
  omega

private lemma sf4_bound {n : ℕ} (a b : Matrix (Fin n) (Fin n) (ZMod 3))
    (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a) {c : ℕ}
    (hcA : Nat.card {v : Fin n → ZMod 3 // Matrix.mulVec a v = v} ≤ 3 ^ c)
    (hcB : Nat.card {v : Fin n → ZMod 3 // Matrix.mulVec b v = v} ≤ 3 ^ c)
    (hcAB : Nat.card {v : Fin n → ZMod 3 // Matrix.mulVec (a * b) v = v} ≤ 3 ^ c) :
    n ≤ 3 * c := by
  have hdim := sf4_finrank_le a b ha hb hab
  rw [sf4_natCard_fix a] at hcA
  rw [sf4_natCard_fix b] at hcB
  rw [sf4_natCard_fix (a * b)] at hcAB
  have k1 := (Nat.pow_le_pow_iff_right (by norm_num)).1 hcA
  have k2 := (Nat.pow_le_pow_iff_right (by norm_num)).1 hcB
  have k3 := (Nat.pow_le_pow_iff_right (by norm_num)).1 hcAB
  omega

theorem le_of_four_group_fixed {n : ℕ} (A B : Matrix.GeneralLinearGroup (Fin n) (ZMod 3))
    (hA : A * A = 1) (hB : B * B = 1) (hAB : A * B = B * A) {c : ℕ}
    (hcA : Nat.card {v : Fin n → ZMod 3 //
      Matrix.mulVec (A : Matrix (Fin n) (Fin n) (ZMod 3)) v = v} ≤ 3 ^ c)
    (hcB : Nat.card {v : Fin n → ZMod 3 //
      Matrix.mulVec (B : Matrix (Fin n) (Fin n) (ZMod 3)) v = v} ≤ 3 ^ c)
    (hcAB : Nat.card {v : Fin n → ZMod 3 //
      Matrix.mulVec ((A * B : Matrix.GeneralLinearGroup (Fin n) (ZMod 3)) :
        Matrix (Fin n) (Fin n) (ZMod 3)) v = v} ≤ 3 ^ c) : n ≤ 3 * c := by
  have ha : (A : Matrix (Fin n) (Fin n) (ZMod 3)) * (A : Matrix (Fin n) (Fin n) (ZMod 3)) = 1 := by
    rw [← Units.val_mul, hA, Units.val_one]
  have hb : (B : Matrix (Fin n) (Fin n) (ZMod 3)) * (B : Matrix (Fin n) (Fin n) (ZMod 3)) = 1 := by
    rw [← Units.val_mul, hB, Units.val_one]
  have hab : (A : Matrix (Fin n) (Fin n) (ZMod 3)) * (B : Matrix (Fin n) (Fin n) (ZMod 3)) =
      (B : Matrix (Fin n) (Fin n) (ZMod 3)) * (A : Matrix (Fin n) (Fin n) (ZMod 3)) := by
    rw [← Units.val_mul, ← Units.val_mul, hAB]
  rw [Units.val_mul] at hcAB
  exact sf4_bound _ _ ha hb hab hcA hcB hcAB

end CFSG.RankThree.PartTwo.Sec13.K135SF
