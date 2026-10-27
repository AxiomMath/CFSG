
module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.A1cModuleDefs

@[expose] public section

namespace CFSG.Quasithin

namespace A37

open scoped commutatorElement

theorem mulAut_conj_conj {X : Type*} [Group X] (α : MulAut X) (x : X) :
    α * MulAut.conj x * α⁻¹ = MulAut.conj (α x) := by
  refine MulEquiv.ext fun y => ?_
  simp [MulAut.mul_apply, MulAut.conj_apply]

end A37

end CFSG.Quasithin
