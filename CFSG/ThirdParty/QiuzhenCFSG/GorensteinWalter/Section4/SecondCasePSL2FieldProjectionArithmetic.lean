module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FieldAutomorphismCentralizerArithmetic
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# The finite-field arithmetic core of the PSL₂ equation-(4) route

The missing semilinear centralizer calculation produces one of two displayed
cardinality equations.  This owner discharges the final contradiction once
that calculation has been supplied, keeping it independent of the matrix
and subgroup transport.
-/

namespace CFSG.GorensteinWalter

/-- A prime-order field component with either source centralizer equation is
impossible. -/
public theorem secondCase_psl2_field_component_equation_impossible
    (r p : ℕ) (hr : 3 ≤ r) (hp : 3 ≤ p)
    (heq : r ^ p + 1 = p * (r + 1) ∨
      r ^ p - 1 = p * (r - 1)) : False := by
  rcases fieldAutomorphism_centralizer_equations_impossible r p hr hp with
    ⟨hplus, hminus⟩
  rcases heq with h | h
  · exact hplus h
  · exact hminus h

end CFSG.GorensteinWalter
