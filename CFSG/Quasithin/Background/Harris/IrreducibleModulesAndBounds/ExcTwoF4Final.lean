module

public import CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.ExcTwoF4Reduce
public import CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.ExcTwoF4Rank

public section

namespace CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds

open CFSG.Quasithin CFSG.Quasithin.G11 CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

section Main


theorem false_of_twistedF4 {f : ℕ} (hf : Odd f) (hf3 : 3 ≤ f) {Γ A L : Subgroup (GLV V)}
    {m : ℕ} (h : G93Hyp Γ A L L m)
    (hX : ReeTitsModel (↥L ⧸ Subgroup.center ↥L) .twistedF4 2 f) : False := by
  refine false_of_twistedF4_of_rank hf hf3 (r := 6 * f - 2) (by omega) ?_ h hX
  intro K _ _ _ a hfa hK B hcomm hsq
  have hK' : Nat.card K = 2 ^ (2 * a + 1) := by rw [hK, hfa]
  have := card_le_two_pow_of_isElem2 (m := a) (by omega) hK' (E := B) hcomm
    (fun x hx => by rw [sq]; exact hsq x hx)
  rwa [← hfa] at this

end Main

end CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds
