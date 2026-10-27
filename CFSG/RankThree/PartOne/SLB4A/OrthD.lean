module

public import CFSG.RankThree.PartOne.SLB4A.OrthFrame
public import CFSG.LieType.BorelTits.OrthogonalModels

public section

namespace CFSG.RankThree.PartOne.SLB4A

open CFSG CFSG.Assembly.LowTwoRank CFSG.LieType.BorelTits Matrix

variable {K : Type} [Field K]

theorem exists_two_pow_five_pomega_plus_odd (n : ℕ) (hn : 4 ≤ n) (h2 : (2 : K) ≠ 0) :
    ∃ U : Subgroup (StatedProj (StatedOmega (StatedQuadPlus n K))), IsElementaryAbelian 2 U ∧
      Nat.card U = 2 ^ 5 := by
  let pl : Fin 3 → Fin n := fun i => ⟨i.1, by omega⟩
  let p3 : Fin n := ⟨3, by omega⟩
  have hpl : ∀ i j, pl i = pl j ↔ i = j := fun i j => by
    simp [pl, Fin.ext_iff]
  have hp3 : ∀ i, pl i ≠ p3 := fun i h => by
    have := i.2
    simp [pl, p3, Fin.ext_iff] at h
    omega
  refine exists_two_pow_five_orth_planes (quadPlusForm n K) h2
    (fun i => Pi.single (.inl (pl i)) 1) (fun i => Pi.single (.inr (pl i)) 1)
    (Pi.single (.inl p3) 1 + Pi.single (.inr p3) 1) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro i j
    show quadPlusPolar n K _ _ = _
    simp [quadPlusPolar, Pi.single_apply]
  · intro i j
    show quadPlusPolar n K _ _ = _
    simp [quadPlusPolar, Pi.single_apply]
  · intro i j
    show quadPlusPolar n K _ _ = _
    simp [quadPlusPolar, Pi.single_apply, hpl]
    exact if_congr eq_comm rfl rfl
  · intro i
    show quadPlusPolar n K _ _ = _
    simp [quadPlusPolar, Pi.single_apply, (hp3 i).symm]
  · intro i
    show quadPlusPolar n K _ _ = _
    simp [quadPlusPolar, Pi.single_apply, hp3 i]
  · intro i
    show StatedQuadPlus n K _ = _
    simp [StatedQuadPlus, Pi.single_apply]
  · intro i
    show StatedQuadPlus n K _ = _
    simp [StatedQuadPlus, Pi.single_apply]
  · show StatedQuadPlus n K _ = _
    simp [StatedQuadPlus, Pi.single_apply]

theorem exists_two_pow_five_pomega_minus_odd [Finite K] (n : ℕ) (hn : 4 ≤ n) (b c : K)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (h2 : (2 : K) ≠ 0) :
    ∃ U : Subgroup (StatedProj (StatedOmega (StatedQuadMinus n K b c))), IsElementaryAbelian 2 U ∧
      Nat.card U = 2 ^ 5 := by
  let pl : Fin 3 → Fin (n - 1) := fun i => ⟨i.1, by omega⟩
  have hpl : ∀ i j, pl i = pl j ↔ i = j := fun i j => by
    simp [pl, Fin.ext_iff]
  refine exists_two_pow_five_orth_planes (quadMinusForm n K b c hirr) h2
    (fun i => Pi.single (.inl (pl i)) 1) (fun i => Pi.single (.inr (.inl (pl i))) 1)
    (Pi.single (.inr (.inr 0)) 1) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro i j
    show quadMinusPolar n K b c _ _ = _
    simp [quadMinusPolar, Pi.single_apply]
  · intro i j
    show quadMinusPolar n K b c _ _ = _
    simp [quadMinusPolar, Pi.single_apply]
  · intro i j
    show quadMinusPolar n K b c _ _ = _
    simp [quadMinusPolar, Pi.single_apply, hpl]
    exact if_congr eq_comm rfl rfl
  · intro i
    show quadMinusPolar n K b c _ _ = _
    simp [quadMinusPolar, Pi.single_apply]
  · intro i
    show quadMinusPolar n K b c _ _ = _
    simp [quadMinusPolar, Pi.single_apply]
  · intro i
    show StatedQuadMinus n K b c _ = _
    simp [StatedQuadMinus, Pi.single_apply]
  · intro i
    show StatedQuadMinus n K b c _ = _
    simp [StatedQuadMinus, Pi.single_apply]
  · show StatedQuadMinus n K b c _ = _
    simp [StatedQuadMinus]

end CFSG.RankThree.PartOne.SLB4A
