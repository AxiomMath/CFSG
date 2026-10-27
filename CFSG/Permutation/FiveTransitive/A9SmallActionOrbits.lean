module

public import CFSG.Permutation.FiveTransitive.A9SmallActionIndex

public section

namespace CFSG

namespace FiveTransitive.A9SmallActionOrbits
open MulAction

theorem card_one_or_nine
    {F E : Type*} [Fintype F] [DecidableEq F] [Finite E]
    [MulAction (alternatingGroup F) E] (hF : Nat.card F = 9) (hE : Nat.card E ≤ 14)
    (x : E) : Nat.card (orbit (alternatingGroup F) x) = 1 ∨
      Nat.card (orbit (alternatingGroup F) x) = 9 := by
  have hb : (stabilizer (alternatingGroup F) x).index ≤ 14 := by
    rw [index_stabilizer,← Nat.card_coe_set_eq]
    exact (Nat.card_le_card_of_injective (fun z : orbit (alternatingGroup F) x => z.val)
      Subtype.val_injective).trans hE
  simpa only [index_stabilizer,← Nat.card_coe_set_eq] using
    A9SmallActionIndex.one_or_nine hF (stabilizer (alternatingGroup F) x) hb

end FiveTransitive.A9SmallActionOrbits

end CFSG
