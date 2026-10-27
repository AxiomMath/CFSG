module

public import Mathlib.InformationTheory.Hamming
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Matrix.Mul

public section

namespace CFSG.Monster.Code

@[expose] def bvec (n a : ℕ) : Fin n → ZMod 2 := fun i => if a.testBit i then 1 else 0

@[expose] def popc : ℕ → ℕ → ℕ
  | 0, _ => 0
  | k + 1, a => a % 2 + popc k (a / 2)

@[expose] def treeSumN {M : Type*} [Add M] (F : ℕ → M) (m : ℕ → ℕ) : ℕ → ℕ → M
  | 0, a => F a
  | k + 1, a => treeSumN F m k a + treeSumN F m k (a ^^^ m k)

theorem bvec_apply (n a : ℕ) (i : Fin n) : bvec n a i = if a.testBit i then 1 else 0 := rfl

theorem bvec_zero (n : ℕ) : bvec n 0 = 0 := by
  funext i; simp [bvec]

theorem bvec_xor (n a b : ℕ) : bvec n (a ^^^ b) = bvec n a + bvec n b := by
  funext i
  simp only [bvec, Nat.testBit_xor, Pi.add_apply]
  cases a.testBit i <;> cases b.testBit i <;> decide

theorem bvec_and (n a b : ℕ) : bvec n (a &&& b) = bvec n a * bvec n b := by
  funext i
  simp only [bvec, Nat.testBit_and, Pi.mul_apply]
  cases a.testBit i <;> cases b.testBit i <;> decide

theorem bvec_ne_zero_iff (n a : ℕ) (i : Fin n) : bvec n a i ≠ 0 ↔ a.testBit i = true := by
  simp only [bvec]; cases a.testBit i <;> decide

theorem hammingNorm_bvec : ∀ (n a : ℕ), hammingNorm (bvec n a) = popc n a
  | 0, a => by simp [hammingNorm, popc]
  | n + 1, a => by
    have ih := hammingNorm_bvec n (a / 2)
    simp only [hammingNorm, Finset.card_filter, bvec_ne_zero_iff] at ih ⊢
    rw [Fin.sum_univ_succ, popc, ← ih]
    congr 1
    · simp only [Fin.val_zero, Nat.testBit_zero, decide_eq_true_eq]
      split_ifs with h <;> omega
    · simp only [Fin.val_succ, Nat.testBit_succ]

private theorem val_eq_ite : ∀ a : ZMod 2, a.val = if a ≠ 0 then 1 else 0 := by decide

theorem hammingNorm_eq_sum_val {ι : Type*} [Fintype ι] (v : ι → ZMod 2) :
    hammingNorm v = ∑ i, (v i).val := by
  rw [hammingNorm, Finset.card_filter]
  exact Finset.sum_congr rfl fun i _ => (val_eq_ite _).symm

theorem sum_eq_hammingNorm {ι : Type*} [Fintype ι] (v : ι → ZMod 2) :
    ∑ i, v i = (hammingNorm v : ZMod 2) := by
  have h : ∀ x : ZMod 2, x = if x ≠ 0 then 1 else 0 := by decide
  rw [hammingNorm, Finset.natCast_card_filter]
  exact Finset.sum_congr rfl fun i _ => h (v i)

theorem dotProduct_eq_hammingNorm {ι : Type*} [Fintype ι] (v w : ι → ZMod 2) :
    v ⬝ᵥ w = (hammingNorm (v * w) : ZMod 2) := by
  rw [dotProduct, ← sum_eq_hammingNorm]; rfl

theorem bvec_dotProduct (n a b : ℕ) : bvec n a ⬝ᵥ bvec n b = (popc n (a &&& b) : ZMod 2) := by
  rw [dotProduct_eq_hammingNorm, ← bvec_and, hammingNorm_bvec]

private theorem sum_zmod2 {M : Type*} [AddCommMonoid M] (f : ZMod 2 → M) :
    ∑ c, f c = f 0 + f 1 := by
  rw [show (Finset.univ : Finset (ZMod 2)) = {0, 1} by decide, Finset.sum_pair (by decide)]

theorem sum_comb_bvec {M : Type*} [AddCommMonoid M] (n : ℕ) (F : (Fin n → ZMod 2) → M)
    (m : ℕ → ℕ) : ∀ k a : ℕ,
    ∑ μ : Fin k → ZMod 2, F (bvec n a + ∑ i, μ i • bvec n (m i)) =
      treeSumN (fun a => F (bvec n a)) m k a
  | 0, a => by simp [treeSumN]
  | k + 1, a => by
    rw [treeSumN, ← sum_comb_bvec n F m k a, ← sum_comb_bvec n F m k (a ^^^ m k),
      ← (Fin.snocEquiv fun _ => ZMod 2).sum_comp, Fintype.sum_prod_type, sum_zmod2]
    congr 1 <;> refine Finset.sum_congr rfl fun μ _ => ?_ <;>
      simp only [Fin.snocEquiv, Equiv.coe_fn_mk, Fin.sum_univ_castSucc, Fin.snoc_castSucc,
        Fin.snoc_last, Fin.val_castSucc, Fin.val_last, zero_smul, add_zero, one_smul, bvec_xor]
    congr 1
    abel

end CFSG.Monster.Code
