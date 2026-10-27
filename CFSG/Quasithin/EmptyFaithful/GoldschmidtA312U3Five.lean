module

public import CFSG.RankThree.SubgroupLists.RationalFiveExclusions

public section

namespace CFSG.Quasithin.A312U3

open CFSG.RankThree.SubgroupLists Matrix

variable {K : Type*} [Field K] {H : Subgroup (GL (Fin 3) K)}

theorem not_mulEquiv_alternating_seven_K (h5 : (5 : K) ≠ 0)
    (hdet : ∀ x ∈ H, (x : Matrix (Fin 3) (Fin 3) K).det = 1)
    (hZ3 : ∀ z ∈ Subgroup.center H, z ^ 3 = 1)
    (e : (H ⧸ Subgroup.center H) ≃* alternatingGroup (Fin 7)) : False := by
  have hs5 : (e.symm a7Five) ^ 5 = 1 := by rw [← map_pow, a7Five_pow_five, map_one]
  have hs1 : e.symm a7Five ≠ 1 := fun h => a7Five_ne_one (e.symm.injective (by rw [h, map_one]))
  have hg : e.symm a7Conj * e.symm a7Five * (e.symm a7Conj)⁻¹ = (e.symm a7Five) ^ 2 := by
    rw [← map_inv, ← map_mul, ← map_mul, a7Conj_conj, map_pow]
  exact h5 (five_eq_zero_of_rational_five hdet hZ3 hs5 hs1 hg)

theorem not_mulEquiv_m11_K (h5 : (5 : K) ≠ 0)
    (hdet : ∀ x ∈ H, (x : Matrix (Fin 3) (Fin 3) K).det = 1)
    (hZ3 : ∀ z ∈ Subgroup.center H, z ^ 3 = 1)
    (e : (H ⧸ Subgroup.center H) ≃* CFSG.Assembly.LowTwoRank.StatedM11) : False := by
  have hs5 : (e.symm m11Five) ^ 5 = 1 := by rw [← map_pow, m11Five_pow_five, map_one]
  have hs1 : e.symm m11Five ≠ 1 := fun h =>
    m11Five_ne_one (e.symm.injective (by rw [h, map_one]))
  have hg : e.symm m11B * e.symm m11Five * (e.symm m11B)⁻¹ = (e.symm m11Five) ^ 2 := by
    rw [← map_inv, ← map_mul, ← map_mul, m11B_conj, map_pow]
  exact h5 (five_eq_zero_of_rational_five hdet hZ3 hs5 hs1 hg)

end CFSG.Quasithin.A312U3
