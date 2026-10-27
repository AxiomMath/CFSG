module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyU

public section

namespace CFSG.StandardType

theorem ggTBRowPerm_card_sumZero (m p : ℕ) [NeZero p] :
    Nat.card ↥(UCoord.sumZero (m + 1) p) = p ^ m := by
  refine le_antisymm (UCoord.card_sumZero_le m p) ?_
  have hcard : Nat.card (Fin m → Multiplicative (ZMod p)) = p ^ m := by
    rw [Nat.card_fun, Nat.card_fin]
    congr 1
    exact Nat.card_zmod p
  rw [← hcard]
  let G : (Fin m → Multiplicative (ZMod p)) → ↥(UCoord.sumZero (m + 1) p) := fun g =>
    ⟨Fin.lastCases (Multiplicative.ofAdd (-∑ i : Fin m, Multiplicative.toAdd (g i)))
      (fun i => g i), by
        rw [UCoord.mem_sumZero, Fin.sum_univ_castSucc]
        simp [Fin.lastCases_castSucc, Fin.lastCases_last, Finset.sum_neg_distrib]⟩
  refine Nat.card_le_card_of_injective G (fun g g' hgg => ?_)
  funext i
  have h' := congrArg (fun f : ↥(UCoord.sumZero (m + 1) p) =>
    (f : Fin (m + 1) → Multiplicative (ZMod p)) (Fin.castSucc i)) hgg
  simpa only [G, Fin.lastCases_castSucc] using h'

theorem ggTBRowPerm_card_sumZero' (d p : ℕ) [NeZero p] :
    Nat.card ↥(UCoord.sumZero d p) = p ^ (d - 1) := by
  rcases d with _ | m
  · rw [Nat.zero_sub, pow_zero]
    have htop : UCoord.sumZero 0 p = ⊤ := by
      rw [eq_top_iff]
      intro f _
      rw [UCoord.mem_sumZero]
      simp
    rw [htop, Nat.card_congr Subgroup.topEquiv.toEquiv, Nat.card_fun, Nat.card_fin, pow_zero]
  · simpa using ggTBRowPerm_card_sumZero m p

end CFSG.StandardType

end

