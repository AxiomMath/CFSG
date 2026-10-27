module

public import CFSG.RankThree.PartOne.KFOUT3.KtyRow4
public import CFSG.RankThree.PartOne.KLAY.RootLayerRow4

public section

namespace CFSG.RankThree.PartOne.KFOUT3

open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU CFSG.RankThree.PartOne.KLAY
  CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag

section Coord

variable {p : ℕ} {K : Type} [Field K]

theorem f4s1_fixed_coord {v : G2V p K} (hv : f4s1 p K v = v) :
    ((v 1 : rootsOfUnity p K) : Kˣ) = ((v 0 : rootsOfUnity p K) : Kˣ) ^ 2 := by
  have h0 : (v 0)⁻¹ * v 1 = v 0 := by
    have := congrFun hv 0
    rwa [f4s1_apply_zero] at this
  have h1 : v 1 = v 0 * v 0 := by
    rw [inv_mul_eq_iff_eq_mul] at h0
    exact h0
  rw [h1, pow_two]
  rfl

theorem f4s2_fixed_coord (hp2 : Odd p) {θ : ℕ} {v : G2V p K} (hv : f4s2 p K θ v = v) :
    ((v 1 : rootsOfUnity p K) : Kˣ) = ((v 0 : rootsOfUnity p K) : Kˣ) ^ (1 + θ) := by
  have h0 : v 0 ^ (2 * θ + 2) * (v 1)⁻¹ = v 1 := by
    have := congrFun hv 1
    rwa [f4s2_apply_one] at this
  have h1 : v 1 * v 1 = v 0 ^ (2 * θ + 2) := by
    calc v 1 * v 1 = v 0 ^ (2 * θ + 2) * (v 1)⁻¹ * v 1 := by rw [h0]
      _ = v 0 ^ (2 * θ + 2) := by group
  have h2 : (v 1 * (v 0 ^ (1 + θ))⁻¹) ^ 2 = 1 := by
    have e : v 0 ^ (2 * θ + 2) = (v 0 ^ (1 + θ)) * (v 0 ^ (1 + θ)) := by
      rw [← pow_add]
      congr 1
      ring
    rw [e] at h1
    rw [sq, mul_mul_mul_comm, h1, mul_mul_mul_comm, mul_inv_cancel, one_mul]
  have h3 := eq_one_of_sq_eq_one_of_odd hp2 h2
  have h4 : v 1 = v 0 ^ (1 + θ) := by
    have := mul_inv_eq_one.mp h3
    exact this
  rw [h4]
  rfl

end Coord

theorem kf1322KtyRow4_of_s2
    (hs2 : ∀ {p a : ℕ} {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]
      (hP : F4Param p a K) (v : Fin 2 → rootsOfUnity p K), v ≠ 1 →
        ((v 1 : rootsOfUnity p K) : Kˣ) = ((v 0 : rootsOfUnity p K) : Kˣ) ^ (1 + 2 ^ a) →
        RootLayer ↥(F4.reeGamma K a) p (tp4M hP v)
          ((2 ^ (2 * a + 1)) ^ 2 * (((2 ^ (2 * a + 1)) ^ 2 + 1) * (2 ^ (2 * a + 1) - 1)))) :
    KF1322KtyRow 4 := by
  refine kf1322KtyRow4_of_layers ?_
  intro p a K _ _ _ hP
  refine ⟨fun v hv1 hv => rootLayer_row4_s1 hP v hv1 (f4s1_fixed_coord hv), fun v hv1 hv => ?_⟩
  have hodd : Odd p := hP.prime.odd_of_ne_two (by have := hP.five_le; omega)
  have h := hs2 hP v hv1 (f4s2_fixed_coord hodd hv)
  rwa [← Nat.mul_assoc] at h

end CFSG.RankThree.PartOne.KFOUT3
