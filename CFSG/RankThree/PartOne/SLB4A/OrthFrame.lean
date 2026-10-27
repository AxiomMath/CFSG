module

public import CFSG.RankThree.PartOne.SLB4A.OrthOdd

public section

namespace CFSG.RankThree.PartOne.SLB4A

open CFSG CFSG.Assembly.LowTwoRank CFSG.LieType.BorelTits Matrix

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

theorem exists_two_pow_five_orth_planes (Φ : QuadForm K (ι → K)) (h2 : (2 : K) ≠ 0)
    (ex ey : Fin 3 → ι → K) (z : ι → K)
    (hxx : ∀ i j, Φ.polar.β (ex i) (ex j) = 0) (hyy : ∀ i j, Φ.polar.β (ey i) (ey j) = 0)
    (hxy : ∀ i j, Φ.polar.β (ex i) (ey j) = if i = j then 1 else 0)
    (hzx : ∀ i, Φ.polar.β z (ex i) = 0) (hzy : ∀ i, Φ.polar.β z (ey i) = 0)
    (hQx : ∀ i, Φ.Q (ex i) = 0) (hQy : ∀ i, Φ.Q (ey i) = 0) (hQz : Φ.Q z = 1) :
    ∃ U : Subgroup (StatedProj (StatedOmega Φ.Q)), IsElementaryAbelian 2 U ∧
      Nat.card U = 2 ^ 5 := by
  have hyx : ∀ i j, Φ.polar.β (ey i) (ex j) = if j = i then 1 else 0 := fun i j => by
    rw [Φ.polar_symm, hxy]
  have hxz : ∀ i, Φ.polar.β (ex i) z = 0 := fun i => by rw [Φ.polar_symm, hzx]
  have hyz : ∀ i, Φ.polar.β (ey i) z = 0 := fun i => by rw [Φ.polar_symm, hzy]
  let f : Fin 7 → ι → K := ![ex 0 + ey 0, ex 1 + ey 1, ex 2 + ey 2, z, ex 0 - ey 0, ex 1 - ey 1,
    ex 2 - ey 2]
  have hQp : ∀ i, Φ.Q (ex i + ey i) = 1 := fun i => by
    rw [Φ.Q_add, hQx, hQy, hxy]
    simp
  have hQm : ∀ i, Φ.Q (ex i - ey i) = -1 := fun i => by
    rw [Q_sub, hQx, hQy, hxy]
    simp
  refine exists_two_pow_five_orth_odd Φ h2 f ?_ ?_ ?_ ?_
  · intro j
    fin_cases j <;> simp [f, hQp, hQm, hQz]
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      first
        | exact absurd rfl hij
        | (simp [f, Φ.polar.add_left, Φ.polar.add_right, Φ.polar.β_sub_left, Φ.polar.β_sub_right,
            hxx, hyy, hxy, hyx, hzx, hzy, hxz, hyz])
  · intro j hj
    fin_cases j <;> first | (exfalso; simp at hj; done) | simp [f, hQp, hQz]
  · intro j hj
    fin_cases j <;> first | (exfalso; simp at hj; done) | simp [f, hQm]

end CFSG.RankThree.PartOne.SLB4A
