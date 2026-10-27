module

public import CFSG.ClassicalInvolution.SmallCases.Sporadic.McL

public section

namespace CFSG.LocalAnalysis.WeakClosure81.SporMcL

open CFSG.ClassicalInvolution.McLProof

@[expose] def z2Set : Set (Equiv.Perm (Fin 275)) :=
  {x | x ∈ S ∧ ∀ t ∈ S, x * t * x⁻¹ * t⁻¹ = 1 ∨ x * t * x⁻¹ * t⁻¹ = pa}

end CFSG.LocalAnalysis.WeakClosure81.SporMcL

end
