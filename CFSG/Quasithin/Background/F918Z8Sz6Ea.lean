module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Sporadic.M23.SimplicityCriterion

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank

section LinearAlgebra

variable {K : Type} [Field K]

theorem transvection_mulVec_eq {ι : Type} [Fintype ι] [DecidableEq ι] {i j : ι} (c : K)
    (v : ι → K) :
    (Matrix.transvection i j c).mulVec v = v + Pi.single i (c * v j) := by
  rw [Matrix.transvection, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec]
  rfl

theorem exists_scalar_of_commute_transvection (g : (Fin 3 → K) →+ (Fin 3 → K))
    (hg : ∀ (i j : Fin 3), i ≠ j → ∀ (c : K) (v : Fin 3 → K),
      g ((Matrix.transvection i j c).mulVec v) = (Matrix.transvection i j c).mulVec (g v)) :
    ∃ s : K, ∀ v : Fin 3 → K, g v = s • v := by
  have h1 : ∀ i j : Fin 3, i ≠ j → ∀ c : K,
      g (Pi.single i c) = Pi.single i (c * g (Pi.single j 1) j) := by
    intro i j hij c
    have h := hg i j hij c (Pi.single j 1)
    rw [transvection_mulVec_eq, transvection_mulVec_eq, map_add] at h
    have h2 := add_left_cancel h
    simpa using h2
  obtain ⟨s, hs⟩ : ∃ s : Fin 3 → K, ∀ j, s j = g (Pi.single j 1) j := ⟨_, fun _ => rfl⟩
  have h2 : ∀ i j : Fin 3, s i = s j := by
    intro i j
    by_cases hij : i = j
    · rw [hij]
    · have h' := congrFun (h1 i j hij 1) i
      rw [hs i, hs j, h', Pi.single_eq_same, one_mul]
  refine ⟨s 0, fun v => ?_⟩
  have hv : v = ∑ i, Pi.single i (v i) := (Finset.univ_sum_single v).symm
  calc g v = g (∑ i, Pi.single i (v i)) := by rw [← hv]
    _ = ∑ i, g (Pi.single i (v i)) := map_sum g _ _
    _ = ∑ i : Fin 3, Pi.single i (v i * s 0) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        obtain ⟨j, hj⟩ := exists_ne i
        rw [h1 i j hj.symm (v i), ← hs j, h2 j 0]
    _ = s 0 • v := by
        rw [Finset.univ_sum_single (fun i => v i * s 0)]
        ext k
        simp [mul_comm]

end LinearAlgebra

end CFSG.Quasithin
