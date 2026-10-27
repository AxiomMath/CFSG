module

public import TauCeti.LinearAlgebra.RootSystem.EquivInvariance

public section

namespace CFSG.RootPairing

open TauCeti

variable {ι R M N : Type*} [Field R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : _root_.RootPairing ι R M N)

def rootLattice : AddSubgroup M := (P.rootSpan ℤ).toAddSubgroup

variable {P}

@[simp]
lemma mem_rootLattice {x : M} : x ∈ rootLattice P ↔ x ∈ P.rootSpan ℤ := Iff.rfl

end CFSG.RootPairing
