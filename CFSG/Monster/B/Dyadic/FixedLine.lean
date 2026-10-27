module

public import CFSG.Monster.B.Dyadic.Data
public import CFSG.Open.LocalVocabulary
public import Certificates.Certificate3101

public section

namespace CFSG.Monster.B.Dyadic

open CFSG.Monster.B.Dyadic.Native CFSG.Monster.B.Binary.Native
open scoped Matrix

theorem zmod2_add_self (a : ZMod 2) : a + a = 0 := by
  generalize a = b
  revert b
  decide

theorem vec_add_self {n : ℕ} (z : Fin n → ZMod 2) : z + z = 0 :=
  funext fun i => zmod2_add_self (z i)

theorem list_sum_range' (f : ℕ → ℕ) : ∀ n, ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i
  | 0 => rfl
  | n + 1 => by rw [List.sum_range_succ, Finset.sum_range_succ, list_sum_range' f n]

theorem fvec_fixed (g : Fin 26) : fvec ᵥ* Cmat g = fvec :=
  Certificates.certificate3101.1 g

theorem fixed_vectors
    (y : Fin 4371 → ZMod 2) :
    (∀ g : Fin 26, y ᵥ* Cmat g = y) ↔ y = 0 ∨ y = fvec := by
  constructor
  · exact Certificates.certificate3101.2.1 y
  · rintro (rfl | rfl) g
    · exact Matrix.zero_vecMul _
    · exact fvec_fixed g

theorem fixed_covectors (x : Fin 4371 → ZMod 2) :
    (∀ g : Fin 26, Cmat g *ᵥ x = x) ↔ x = 0 := by
  constructor
  · exact Certificates.certificate3101.2.2.1 x
  · rintro rfl g
    exact Matrix.mulVec_zero _

theorem Pmap_fvec : Pmap fvec = 0 :=
  (Pmap_eq_zero_iff fvec).2 (Or.inr rfl)

theorem quotient_action (g : Fin 26)
    (y : Fin 4371 → ZMod 2) :
    Pmap (y ᵥ* Cmat g) = Pmap y ᵥ* Qmat g := by
  set z : Fin 4371 → ZMod 2 := y + y pIdx • fvec with hz
  have hzp : z pIdx = 0 := by
    rw [hz, Pi.add_apply, Pi.smul_apply, fvec_p, smul_eq_mul, mul_one, zmod2_add_self]
  have hPz : ∀ k : Fin 4370, Pmap y k = z (pIdx.succAbove k) := fun k => rfl
  have hzC : z ᵥ* Cmat g = y ᵥ* Cmat g + y pIdx • fvec := by
    rw [hz, Matrix.add_vecMul, Matrix.smul_vecMul, fvec_fixed]
  have lhs : Pmap (y ᵥ* Cmat g) = Pmap (z ᵥ* Cmat g) := by
    rw [hzC, map_add, map_smul, Pmap_fvec, smul_zero, add_zero]
  have hrow : Pmap (z ᵥ* Cmat g) = ∑ i, z i • Pmap (fun j => Cmat g i j) := by
    rw [Matrix.vecMul_eq_sum, map_sum]
    exact Finset.sum_congr rfl fun i _ => map_smul Pmap (z i) (Cmat g i)
  funext t
  rw [lhs, hrow, Fin.sum_univ_succAbove _ pIdx, hzp, zero_smul, zero_add, Finset.sum_apply]
  simp only [Matrix.vecMul, dotProduct]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, Qmat_apply, hPz]

theorem rank_Q0 : (Qmat 0 - 1).rank = 1860 :=
  Certificates.certificate3101.2.2.2.1

theorem rank_Q25 : (Qmat 25 - 1).rank = 2862 :=
  Certificates.certificate3101.2.2.2.2.1

theorem orders_facts :
    Qmat 0 * Qmat 0 = 1 ∧ Qmat 25 * Qmat 25 * Qmat 25 = 1 :=
  Certificates.certificate3101.2.2.2.2.2

theorem Q0_sq : Qmat 0 * Qmat 0 = 1 := orders_facts.1

theorem Q25_cube : Qmat 25 * Qmat 25 * Qmat 25 = 1 := orders_facts.2

theorem two_eq_zero_mat : (2 : Matrix (Fin 4370) (Fin 4370) (ZMod 2)) = 0 := by
  rw [show (2 : Matrix (Fin 4370) (Fin 4370) (ZMod 2)) = (2 : ZMod 2) • 1 by
    rw [two_smul, one_add_one_eq_two]]
  rw [show (2 : ZMod 2) = 0 from rfl, zero_smul]

theorem sub_one_mul_self_of {A : Type*} [Ring A] (h2 : (2 : A) = 0) {q : A} (hq : q * q = 1) :
    (q - 1) * (q - 1) = 0 := by
  have h : (q - 1) * (q - 1) = q * q + 1 - 2 * q := by
    simp only [sub_mul, mul_sub, mul_one, one_mul, two_mul]
    abel
  rw [h, hq, h2, zero_mul, sub_zero, one_add_one_eq_two, h2]

theorem Q0_sub_one_sq : (Qmat 0 - 1) * (Qmat 0 - 1) = 0 :=
  sub_one_mul_self_of two_eq_zero_mat Q0_sq

theorem Q25_sub_one_mul :
    (Qmat 25 - 1) * (Qmat 25 * Qmat 25 + Qmat 25 + 1) = 0 := by
  have h : (Qmat 25 - 1) * (Qmat 25 * Qmat 25 + Qmat 25 + 1) =
      Qmat 25 * Qmat 25 * Qmat 25 - 1 := by
    simp only [sub_mul, mul_add, mul_one, one_mul, mul_assoc]
    abel
  rw [h, Q25_cube, sub_self]

theorem Q0_ne_one : Qmat 0 ≠ 1 := by
  intro h
  have := rank_Q0
  rw [h, sub_self, Matrix.rank_zero] at this
  exact absurd this (by norm_num)

theorem Q25_ne_one : Qmat 25 ≠ 1 := by
  intro h
  have := rank_Q25
  rw [h, sub_self, Matrix.rank_zero] at this
  exact absurd this (by norm_num)

end CFSG.Monster.B.Dyadic

end
