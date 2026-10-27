module

public import CFSG.Walter.Ree.Bombieri.Lemma2
public import Mathlib.Algebra.MvPolynomial.Monad

public section

namespace CFSG.Walter.Ree.Bombieri

@[expose] def substIdx (k : ℕ) (neg : Bool) (j : ℕ) : ℕ :=
  if neg then k - (4 - j) % (k + 1) else j % (k + 1)

@[expose] def substExp (k lam : ℕ) (neg : Bool) (j : ℕ) : ℕ :=
  lam * if neg then (4 - j) / (k + 1) else j / (k + 1)

theorem substIdx_lt (k : ℕ) (neg : Bool) (j : ℕ) : substIdx k neg j < k + 1 := by
  unfold substIdx
  split
  · omega
  · exact Nat.mod_lt _ (Nat.succ_pos k)

@[expose] def dHList : List ℕ := [53814, 44697, 18471, 7524, 1368]

@[expose] def degS (k lam : ℕ) (neg : Bool) (i : ℕ) : ℕ :=
  ((List.range 5).map fun j =>
    if substIdx k neg j = i then dHList.getD j 0 * 3 ^ substExp k lam neg j else 0).sum

theorem degS_eq (k lam : ℕ) (neg : Bool) (i : ℕ) :
    degS k lam neg i = ∑ j : Fin 5,
      if substIdx k neg j = i then Elim.dH j * 3 ^ substExp k lam neg j else 0 := by
  simp [degS, Fin.sum_univ_five, List.range_succ, dHList, Elim.dH]
  ring

namespace Elim

open MvPolynomial

noncomputable def substMap (k lam : ℕ) (neg : Bool) (j : Fin 5) :
    MvPolynomial (Fin (k + 1)) (ZMod 3) :=
  X ⟨substIdx k neg j, substIdx_lt k neg j⟩ ^ 3 ^ substExp k lam neg j

noncomputable def Hs (k lam : ℕ) (neg : Bool) : MvPolynomial (Fin (k + 1)) (ZMod 3) :=
  bind₁ (substMap k lam neg) H

theorem H_ne_zero_of_Hs_ne_zero {k lam : ℕ} {neg : Bool} (h : Hs k lam neg ≠ 0) : H ≠ 0 := by
  intro h0
  apply h
  rw [Hs, h0, map_zero]

theorem degreeOf_bind₁_le {σ τ R : Type*} [CommSemiring R] [Fintype σ]
    (φ : σ → MvPolynomial τ R) (p : MvPolynomial σ R) (i : τ) :
    (bind₁ φ p).degreeOf i ≤ ∑ j, p.degreeOf j * (φ j).degreeOf i := by
  rw [bind₁, aeval_def, algebraMap_eq, eval₂_eq']
  refine (degreeOf_sum_le _ _ _).trans (Finset.sup_le fun α hα => ?_)
  refine (degreeOf_C_mul_le _ _ _).trans ?_
  refine (degreeOf_prod_le _ _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  exact (degreeOf_pow_le _ _ _).trans (Nat.mul_le_mul_right _ (monomial_le_degreeOf j hα))

theorem degreeOf_Hs_le (k lam : ℕ) (neg : Bool) (i : Fin (k + 1)) :
    (Hs k lam neg).degreeOf i ≤ degS k lam neg i := by
  classical
  refine (degreeOf_bind₁_le _ _ _).trans ?_
  rw [degS_eq]
  refine Finset.sum_le_sum fun j _ => ?_
  split_ifs with h
  · refine Nat.mul_le_mul (H_degreeOf j) ((degreeOf_pow_le _ _ _).trans ?_)
    rw [degreeOf_X]
    split_ifs <;> simp
  · rw [substMap, degreeOf_X_pow_of_ne _ (fun h' => h (congrArg Fin.val h').symm), mul_zero]

variable {K : Type*} [Field K] [CharP K 3]

theorem evA5_eq (zs : Fin 5 → K) : evA5 zs = eval₂Hom (castThree K) zs := by
  refine MvPolynomial.ringHom_ext (fun c => ?_) (fun i => ?_)
  · rw [evA5_C]; simp
  · rw [evA5_X]; simp

theorem eval₂_Hs {k lam : ℕ} {neg : Bool} (w : Fin (k + 1) → K) :
    eval₂ (castThree K) w (Hs k lam neg) =
      evA5 (fun j => w ⟨substIdx k neg j, substIdx_lt k neg j⟩ ^ 3 ^ substExp k lam neg j) H := by
  rw [evA5_eq, Hs, ← coe_eval₂Hom, eval₂Hom_bind₁]
  congr 2
  funext j
  simp [substMap]

omit [CharP K 3] in
theorem pow_apply_pos {σ : K ≃+* K} {k lam : ℕ} (h : ∀ x, (σ ^ (k + 1)) x = x ^ 3 ^ lam)
    (j : ℕ) (z : K) :
    (σ ^ j) z = ((σ ^ (j % (k + 1))) z) ^ 3 ^ (lam * (j / (k + 1))) := by
  have hq : ∀ (q : ℕ) (x : K), (σ ^ ((k + 1) * q)) x = x ^ 3 ^ (lam * q) := by
    intro q
    induction q with
    | zero => intro x; simp
    | succ q ih =>
      intro x
      rw [Nat.mul_succ, pow_add, RingAut.mul_apply, h, ih, ← pow_mul, ← pow_add]
      congr 2
      ring
  conv_lhs => rw [← Nat.mod_add_div j (k + 1), pow_add, RingAut.mul_apply, hq, map_pow]

omit [CharP K 3] in
theorem pow_apply_neg {σ : K ≃+* K} {k lam : ℕ} (h : ∀ y, ((σ ^ (k + 1)) y) ^ 3 ^ lam = y)
    {j : ℕ} (hj : j ≤ 4) (z : K) :
    (σ ^ j) z = ((σ ^ (4 - (4 - j) % (k + 1))) z) ^ 3 ^ (lam * ((4 - j) / (k + 1))) := by
  have hq : ∀ (q : ℕ) (y : K), ((σ ^ ((k + 1) * q)) y) ^ 3 ^ (lam * q) = y := by
    intro q
    induction q with
    | zero => intro y; simp
    | succ q ih =>
      intro y
      have e1 : σ ^ ((k + 1) * (q + 1)) = σ ^ ((k + 1) * q) * σ ^ (k + 1) := by
        rw [Nat.mul_succ, pow_add]
      have e2 : (3 : ℕ) ^ (lam * (q + 1)) = 3 ^ (lam * q) * 3 ^ lam := by
        rw [Nat.mul_succ, pow_add]
      rw [e1, RingAut.mul_apply, e2, pow_mul _ (3 ^ (lam * q)) (3 ^ lam), ih, h]
  have e : 4 - (4 - j) % (k + 1) = (k + 1) * ((4 - j) / (k + 1)) + j := by
    have := Nat.mod_add_div (4 - j) (k + 1)
    omega
  rw [e, pow_add, RingAut.mul_apply, hq]

variable [Fintype K] {σ : K ≃+* K} {a s : ℕ} (hB1 : ∀ x : K, (σ x * x) ^ a = x ^ 2)
  (hB2 : ∀ x : K, (σ x * x ^ 2) ^ s = x)
  (hC : ∀ p ∈ ESigma K σ, thompsonT a p.1 p.2.1 p.2.2 = 0)
include hB1 hB2 hC

theorem Hs_vanish_pos {k lam : ℕ} (h : ∀ x, (σ ^ (k + 1)) x = x ^ 3 ^ lam) (z : K) :
    eval₂ (castThree K) (fun i : Fin (k + 1) => (σ ^ (i : ℕ)) z) (Hs k lam false) = 0 := by
  rw [eval₂_Hs]
  convert lemma2 hB1 hB2 hC z using 3
  funext j
  simp only [substIdx, substExp, Bool.false_eq_true, ite_false]
  exact (pow_apply_pos h j z).symm

theorem Hs_vanish_neg {k lam : ℕ} (hk : k ≤ 4) (h : ∀ y, ((σ ^ (k + 1)) y) ^ 3 ^ lam = y)
    (z : K) :
    eval₂ (castThree K) (fun i : Fin (k + 1) => (σ ^ (i : ℕ)) z) (Hs k lam true) = 0 := by
  rw [eval₂_Hs]
  convert lemma2 hB1 hB2 hC ((σ ^ (4 - k)).symm z) using 3
  funext j
  simp only [substIdx, substExp, ite_true]
  rw [pow_apply_neg h (Nat.le_of_lt_succ j.2)]
  have e : 4 - (4 - (j : ℕ)) % (k + 1) = (k - (4 - (j : ℕ)) % (k + 1)) + (4 - k) := by
    have := Nat.mod_lt (4 - (j : ℕ)) (show 0 < k + 1 by omega)
    omega
  rw [e, pow_add, RingAut.mul_apply, RingEquiv.apply_symm_apply]

end Elim

end CFSG.Walter.Ree.Bombieri
