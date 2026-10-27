module

public import CFSG.RankThree.PartOne.SLB4A.OrthFrame
public import CFSG.LieType.BorelTits.OrthogonalModels

public section

namespace CFSG.RankThree.PartOne.SLB4A

open CFSG CFSG.Assembly.LowTwoRank CFSG.LieType.BorelTits Matrix

variable {K : Type} [Field K]

theorem exists_two_pow_five_pomega_odd (n : ℕ) (hn : 3 ≤ n) (h2 : (2 : K) ≠ 0) :
    ∃ U : Subgroup (StatedProj (StatedOmega (StatedQuadOdd n K))), IsElementaryAbelian 2 U ∧
      Nat.card U = 2 ^ 5 := by
  let pl : Fin 3 → Fin n := fun i => ⟨i.1, by omega⟩
  have hpl : ∀ i j, pl i = pl j ↔ i = j := fun i j => by
    simp [pl, Fin.ext_iff]
  refine exists_two_pow_five_orth_planes (quadOddForm n K h2) h2
    (fun i => Pi.single (.inl (pl i)) 1) (fun i => Pi.single (.inr (.inl (pl i))) 1)
    (Pi.single (.inr (.inr ())) 1) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro i j
    show quadOddPolar n K _ _ = _
    simp [quadOddPolar, Pi.single_apply]
  · intro i j
    show quadOddPolar n K _ _ = _
    simp [quadOddPolar, Pi.single_apply]
  · intro i j
    show quadOddPolar n K _ _ = _
    simp [quadOddPolar, Pi.single_apply, hpl]
    exact if_congr eq_comm rfl rfl
  · intro i
    show quadOddPolar n K _ _ = _
    simp [quadOddPolar, Pi.single_apply]
  · intro i
    show quadOddPolar n K _ _ = _
    simp [quadOddPolar, Pi.single_apply]
  · intro i
    show StatedQuadOdd n K _ = _
    simp [StatedQuadOdd, Pi.single_apply]
  · intro i
    show StatedQuadOdd n K _ = _
    simp [StatedQuadOdd, Pi.single_apply]
  · show StatedQuadOdd n K _ = _
    simp [StatedQuadOdd]

end CFSG.RankThree.PartOne.SLB4A
