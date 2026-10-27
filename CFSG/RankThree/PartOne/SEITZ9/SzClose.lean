module

public import CFSG.LieType.Ree.SuzukiBruhatNormalForm

public section

namespace CFSG.RankThree.PartOne.SEITZ9

open CFSG.Blueprint CFSG.LieType.Ree

variable {a : ℕ} {K : Type} [Field K]

theorem suzukiDElt_mem_of_unipotent_weyl [Finite K]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (H : Subgroup (suzukiGroup a K))
    (hS : ∀ u v : K, suzukiSElt a K u v ∈ H) (hW : suzukiWElt a K ∈ H) (l : Kˣ) :
    suzukiDElt a K l ∈ H := by
  have hθ0 : 2 ^ (a + 1) ≠ 0 := pow_ne_zero _ two_ne_zero
  obtain ⟨-, ⟨φ, hφ⟩, -, -, -, -, -, -, -, -, -, hbij, -⟩ := suzuki_frobenius_exponents a K hK
  obtain ⟨t, rfl⟩ := hbij.2 l
  set v := φ.symm (t : K) with hv
  have hvt : v ^ 2 ^ (a + 1) = t := by rw [← hφ, hv, RingEquiv.apply_symm_apply]
  have hv0 : v ≠ 0 := by
    intro h
    rw [h, zero_pow hθ0] at hvt
    exact t.ne_zero hvt.symm
  obtain ⟨-, hfac⟩ := suzuki_bruhat_factorization hK (0 : K) v (by simp [hv0])
  have hN : (t : K) = suzukiN a 0 v := by
    simp [suzukiN, hvt]
  have e : suzukiWElt a K * suzukiSElt a K 0 v * suzukiWElt a K =
      suzukiSElt a K (v / (t : K)) (0 / (t : K)) *
        suzukiDElt a K (t ^ (2 - 2 ^ (a + 1) : ℤ)) * suzukiWElt a K *
        suzukiSElt a K ((0 ^ (2 ^ (a + 1) + 1) + v) / (t : K)) (v / (t : K) ^ 2 ^ (a + 1)) :=
    suzukiSElt_ext (hfac t hN)
  have hDeq : suzukiDElt a K (t ^ (2 - 2 ^ (a + 1) : ℤ)) =
      (suzukiSElt a K (v / (t : K)) (0 / (t : K)))⁻¹ *
        (suzukiWElt a K * suzukiSElt a K 0 v * (suzukiWElt a K)⁻¹) *
        (suzukiSElt a K ((0 ^ (2 ^ (a + 1) + 1) + v) / (t : K))
          (v / (t : K) ^ 2 ^ (a + 1)))⁻¹ * (suzukiWElt a K)⁻¹ := by
    rw [suzukiWElt_inv, e]
    group
    rw [mul_assoc, suzukiWElt_mul_self, mul_one]
  rw [hDeq]
  exact mul_mem (mul_mem (mul_mem (inv_mem (hS _ _))
    (mul_mem (mul_mem hW (hS 0 v)) (inv_mem hW))) (inv_mem (hS _ _))) (inv_mem hW)

theorem suzuki_eq_top_of_unipotent_weyl [Finite K]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (H : Subgroup (suzukiGroup a K))
    (hS : ∀ u v : K, suzukiSElt a K u v ∈ H) (hW : suzukiWElt a K ∈ H) : H = ⊤ := by
  refine eq_top_iff.2 fun g _ => ?_
  rcases (suzuki_bruhat_normal_form hK g).1 with ⟨u, v, l, rfl⟩ | ⟨u, v, l, c, d, rfl⟩
  · exact mul_mem (hS u v) (suzukiDElt_mem_of_unipotent_weyl hK H hS hW l)
  · exact mul_mem (mul_mem (mul_mem (hS u v) (suzukiDElt_mem_of_unipotent_weyl hK H hS hW l))
      hW) (hS c d)

end CFSG.RankThree.PartOne.SEITZ9
