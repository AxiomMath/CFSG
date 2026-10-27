module

public import CFSG.Sporadic.ON

public section

namespace CFSG.Sporadic.ONOddCore

open CFSG.Blueprint

theorem fam_on_certified_simplicity :
    Nontrivial NativeSporadic.ON ∧ IsSimpleGroup NativeSporadic.ON :=
  ⟨CFSG.Sporadic.ON.fam_on_simplicity.2.1, CFSG.Sporadic.ON.fam_on_simplicity.2.2⟩

end CFSG.Sporadic.ONOddCore
