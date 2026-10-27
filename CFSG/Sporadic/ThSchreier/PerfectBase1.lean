
module


public import CFSG.Sporadic.Th.Max3.RelationsBase1

@[expose] public section

namespace CFSG.Sporadic.ThSchreier

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Max3 CFSG.Certificates
open scoped commutatorElement

noncomputable abbrev commM : Subgroup ↥M := commutator ↥M

@[expose] noncomputable def nfM
    (v : Fin 8 → ZMod 2) : ↥M := ⟨nf 0 v, Q_le_M (nf_mem_Q 0 v)⟩

@[expose] noncomputable def xM : ↥M := ⟨x, x_mem_M⟩

@[expose] noncomputable def yM : ↥M := ⟨y, y_mem_M⟩

end CFSG.Sporadic.ThSchreier
