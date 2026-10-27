module

public import CFSG.RankThree.PartOne.SLB4A.OrthEven
public import CFSG.LieType.BorelTits.OrthogonalModels

public section

namespace CFSG.RankThree.PartOne.SLB4A

open CFSG CFSG.Assembly.LowTwoRank CFSG.LieType.BorelTits Matrix

variable {K : Type} [Field K]

theorem exists_two_pow_five_pomega_plus_even [CharP K 2] (n : ℕ) (hn : 4 ≤ n) :
    ∃ U : Subgroup (StatedProj (StatedOmega (StatedQuadPlus n K))), IsElementaryAbelian 2 U ∧
      Nat.card U = 2 ^ 5 := by
  let pl : Fin 4 → Fin n := fun i => ⟨i.1, by omega⟩
  have hpl : Function.Injective pl := fun i j h => Fin.ext (by simpa [pl] using congrArg Fin.val h)
  refine exists_two_pow_five_orth_even (quadPlusForm n K) (fun i => .inl (pl i))
    (fun i => .inr (pl i)) (fun i j h => hpl (Sum.inl.inj h)) (fun i j h => hpl (Sum.inr.inj h))
    (fun i j => Sum.inr_ne_inl) ?_ ?_ ?_
  · intro i
    show StatedQuadPlus n K _ = _
    simp [StatedQuadPlus, Pi.single_apply]
  · intro i v
    show quadPlusPolar n K _ _ = _
    simp [quadPlusPolar, Pi.single_apply]
  · rw [Fintype.card_sum, Fintype.card_fin]
    omega

theorem exists_two_pow_five_pomega_minus_even [CharP K 2] [Finite K] (n : ℕ) (hn : 5 ≤ n) (b c : K)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    ∃ U : Subgroup (StatedProj (StatedOmega (StatedQuadMinus n K b c))), IsElementaryAbelian 2 U ∧
      Nat.card U = 2 ^ 5 := by
  let pl : Fin 4 → Fin (n - 1) := fun i => ⟨i.1, by omega⟩
  have hpl : Function.Injective pl := fun i j h => Fin.ext (by simpa [pl] using congrArg Fin.val h)
  refine exists_two_pow_five_orth_even (quadMinusForm n K b c hirr) (fun i => .inl (pl i))
    (fun i => .inr (.inl (pl i))) (fun i j h => hpl (Sum.inl.inj h))
    (fun i j h => hpl (Sum.inl.inj (Sum.inr.inj h))) (fun i j => by simp) ?_ ?_ ?_
  · intro i
    show StatedQuadMinus n K b c _ = _
    simp [StatedQuadMinus, Pi.single_apply]
  · intro i v
    show quadMinusPolar n K b c _ _ = _
    simp [quadMinusPolar, Pi.single_apply]
  · simp only [Fintype.card_sum, Fintype.card_fin]
    omega

end CFSG.RankThree.PartOne.SLB4A
