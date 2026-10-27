module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearNormalizerOrbit
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# The first equation-(8) parameter bound
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- The relative normalizer index `p₀` is bounded by the number of ambient
conjugates of `P` lying in the elementary-abelian plane `A`. -/
public theorem secondCase_linear_p0_le_conjugateCount
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (od : SecondCaseLinearOmegaData c w d) :
    (normalizerIn c.U od.P).relIndex (normalizerIn c.U od.A) ≤
      conjugateCount od.P od.A := by
  exact secondCase_linear_normalizerOrbit_le_conjugateCount
    (U := c.U) (P := od.P) (A := od.A)
    (hPleA := by
      rw [od.A_eq]
      exact le_sup_left)

end CFSG.GorensteinWalter
