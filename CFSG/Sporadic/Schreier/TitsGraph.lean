module

public import CFSG.Sporadic.Schreier.TitsLocal
public import Mathlib.Combinatorics.SimpleGraph.Basic

public section

namespace CFSG.Sporadic.Schreier.Tits

@[expose] def titsPointGraph : SimpleGraph (Fin 1755) where
  Adj u v := u ≠ v ∧ ∃ e f : Fin 8775, titsBeta e = u ∧ titsBeta f = v ∧ titsKappa e = titsKappa f
  symm := ⟨fun _ _ ⟨huv, e, f, he, hf, hef⟩ => ⟨huv.symm, f, e, hf, he, hef.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

end CFSG.Sporadic.Schreier.Tits
