module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKTableSix

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open CFSG.LieType.Universal.Spin

private theorem s15k_tps_step {k : ℕ} (z : Fin (k + 1) ⊕ Fin (k + 1) → ZMod 2)
    (h : ∀ z' : Fin k ⊕ Fin k → ZMod 2, s15kPlanePair (quadPlus k (ZMod 2)) z') :
    s15kPlanePair (quadPlus (k + 1) (ZMod 2)) z := by
  let E : (Fin k ⊕ Fin k → ZMod 2) → (Fin (k + 1) ⊕ Fin (k + 1) → ZMod 2) := fun p =>
    Sum.elim (fun i => Fin.lastCases 0 (fun j => p (Sum.inl j)) i)
      (fun i => Fin.lastCases 0 (fun j => p (Sum.inr j)) i)
  let R : (Fin (k + 1) ⊕ Fin (k + 1) → ZMod 2) → (Fin k ⊕ Fin k → ZMod 2) := fun w =>
    Sum.elim (fun j => w (Sum.inl j.castSucc)) (fun j => w (Sum.inr j.castSucc))
  refine s15k_table_planePair_of_embed (quadPlus k (ZMod 2)) (quadPlus (k + 1) (ZMod 2)) E R
    ?_ ?_ ?_ z (h (R z))
  · intro p
    rw [quadPlus_apply, quadPlus_apply, Fin.sum_univ_castSucc]
    simp [E]
  · intro w p
    rw [polar_quadPlus, polar_quadPlus, Fin.sum_univ_castSucc]
    simp [E, R]
  · intro p
    funext i
    rcases i with i | i <;> simp [E, R]

theorem s15k_table_plus_pair {k : ℕ} (hk : 3 ≤ k) (z : Fin k ⊕ Fin k → ZMod 2) :
    s15kPlanePair (quadPlus k (ZMod 2)) z := by
  induction k, hk using Nat.le_induction with
  | base => exact s15k_table_plus_three z
  | succ k hk ih => exact s15k_tps_step z ih

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
