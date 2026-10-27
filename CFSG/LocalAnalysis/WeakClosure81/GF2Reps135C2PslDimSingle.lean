module

public import CFSG.LieType.SpecialLinear.ExteriorModel.Binary
import CFSG.LieType.SpecialLinear.ExteriorModel.Fundamental

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Module Finset
open CFSG.LieType.SpecialLinear.ExteriorModel

private theorem c2sldsi_card_powersetCard (n d : ℕ) :
    Fintype.card (Set.powersetCard (Fin n) d) = n.choose d := by
  rw [Fintype.card_eq_nat_card, Set.powersetCard.card, Nat.card_eq_fintype_card, Fintype.card_fin]

private theorem c2sldsi_card_bIdx {n f : ℕ} (ε : Fin f → Finset (Fin n)) :
    Fintype.card (BIdx ε) = ∏ p : Fin f × Fin n, n.choose (bdeg ε p) := by
  rw [Fintype.card_pi]
  exact Finset.prod_congr rfl fun p _ => c2sldsi_card_powersetCard n (bdeg ε p)

private theorem c2sldsi_prod_bdeg {n f : ℕ} (ε : Fin f → Finset (Fin n)) :
    ∏ p : Fin f × Fin n, n.choose (bdeg ε p) = ∏ r, ∏ j ∈ ε r, n.choose (j : ℕ) := by
  rw [Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun r _ => ?_
  rw [← Fintype.prod_ite_mem (ε r) (fun j : Fin n => n.choose (j : ℕ))]
  refine Finset.prod_congr rfl fun j _ => ?_
  by_cases hj : j ∈ ε r
  · simp [bdeg, hj]
  · simp [bdeg, hj, Nat.choose_zero_right]

theorem w135c2_finrank_bModel_of_card_le_one {k : Type} [Field k] [CharP k 2] {n f : ℕ}
    (ε : Fin f → Finset (Fin n)) (h : ∀ r, (ε r).card ≤ 1) :
    finrank k (BModel k ε) = ∏ r, ∏ j ∈ ε r, n.choose (j : ℕ) := by
  classical
  rw [LinearEquiv.finrank_eq (bModelEquivOfCardLeOne (k := k) ε h),
    Module.finrank_fintype_fun_eq_card, c2sldsi_card_bIdx, c2sldsi_prod_bdeg]

end CFSG.LocalAnalysis.WeakClosure81
