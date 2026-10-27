module

public import CFSG.Quasithin.Vol2.Ch10SecKGCFd

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.C10KG

open CFSG.Quasithin CFSG.Assembly.LowTwoRank
open scoped Matrix

variable {K : Type} [Field K] [CharP K 2] (a : ℕ)

omit [CharP K 2] in
theorem frobPow_map (τ : K ≃+* K) (X : Matrix (Fin 2) (Fin 2) K) :
    frobPow a (X.map τ) = (frobPow a X).map τ := by
  ext i j
  simp [frobPow, map_pow]

theorem map_mem_hermSub (τ : K ≃+* K) (w : ↥(hermSub a (Fin 2) K)) :
    Multiplicative.ofAdd ((hmat a w).map τ) ∈ hermSub a (Fin 2) K := by
  have hw : (frobPow a (hmat a w))ᵀ = hmat a w := w.2
  change (frobPow a ((hmat a w).map τ))ᵀ = (hmat a w).map τ
  rw [frobPow_map, ← Matrix.transpose_map, hw]

@[expose] def hermMap (τ : K ≃+* K) : ↥(hermSub a (Fin 2) K) ≃* ↥(hermSub a (Fin 2) K) where
  toFun w := ⟨Multiplicative.ofAdd ((hmat a w).map τ), map_mem_hermSub a τ w⟩
  invFun w := ⟨Multiplicative.ofAdd ((hmat a w).map τ.symm), map_mem_hermSub a τ.symm w⟩
  left_inv w := hmat_injective a (by
    change ((hmat a w).map τ).map τ.symm = hmat a w
    ext i j
    simp)
  right_inv w := hmat_injective a (by
    change ((hmat a w).map τ.symm).map τ = hmat a w
    ext i j
    simp)
  map_mul' w₁ w₂ := hmat_injective a (by
    change (hmat a w₁ + hmat a w₂).map τ = (hmat a w₁).map τ + (hmat a w₂).map τ
    ext i j
    simp)

omit [CharP K 2] in
theorem map_twist (τ : K ≃+* K) (A X : Matrix (Fin 2) (Fin 2) K) :
    (A * X * (frobPow a A)ᵀ).map τ = A.map τ * X.map τ * (frobPow a (A.map τ))ᵀ := by
  ext i j
  simp [Matrix.mul_apply, Fin.sum_univ_two, frobPow, map_pow]

variable {V : Type} [CommGroup V] (BE : V ≃* ↥(hermSub a (Fin 2) K))

@[expose] def phiMap (τ : K ≃+* K) : MulAut V := (BE.trans (hermMap a τ)).trans BE.symm

theorem hmat_phiMap (τ : K ≃+* K) (v : V) :
    hmat a (BE (phiMap a BE τ v)) = (hmat a (BE v)).map τ := by
  change hmat a (BE (BE.symm _)) = _
  rw [MulEquiv.apply_symm_apply]
  rfl

theorem eq_one_of_mem_center_sl2 {N : Matrix.SpecialLinearGroup (Fin 2) K}
    (hN : N ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K)) : N = 1 := by
  obtain ⟨s, hs, hsN⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hN
  rw [Fintype.card_fin] at hs
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : (s - 1) ^ 2 = s ^ 2 - 1 ^ 2 := sub_pow_char s 1
  rw [hs, one_pow, sub_self] at h1
  have hs1 : s = 1 := sub_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp h1)
  ext i j
  rw [← hsN, hs1]
  simp

end CFSG.Quasithin.Vol2.Ch10.SecB.C10KG
