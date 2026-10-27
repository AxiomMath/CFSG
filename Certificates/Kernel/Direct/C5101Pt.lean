module

public import CFSG.GH74.GLS.Stage4.Q9.PermCharInputs
import CFSG.GH74.GLS.Stage4.Q9.ModelBaseInputs
import CFSG.GH74.GLS.Stage4.Q9.ModelBase

public section

namespace CertificateChecks.KernelDirect.C5101

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage4 CFSG.GH74.GLS.Stage4.Q9

@[expose] def ptFacts (l : Lg) (a : ℤ) : Prop :=
  a ∈ ({-1, 0, 1, 9} : Finset ℤ) ∧ (a = 9 ↔ l = 1 ∨ l = innerL minusOne) ∧
    (parityL l ≠ 1 → a ∈ ({-1, 1} : Finset ℤ)) ∧ a = aByOrder (decide (parityL l = 1)) (ordL l)

instance (l : Lg) (a : ℤ) : Decidable (ptFacts l a) := by
  unfold ptFacts
  infer_instance

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ptFacts_aTabFast : ∀ l : Lg, ptFacts l (aTabFast l) := by
  decide +kernel

end CertificateChecks.KernelDirect.C5101
