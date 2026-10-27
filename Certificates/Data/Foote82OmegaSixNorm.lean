module

public import Certificates.Data.Foote82OmegaSix

public section

namespace CFSG.CGT.Foote82.OmegaSix

@[expose] def v0 : ℕ := 16

@[expose] def transCheck (_ : Unit := ()) : Bool :=
  let E := omegaEnum ()
  (List.range 64).all fun n => !(q6 (cvec n) == 1) || E.elems.any fun t => t[v0]! == n

@[expose] def countCheck (_ : Unit := ()) : Bool :=
  decide ((Finset.univ.filter fun v : Fin 2 ⊕ Fin 2 ⊕ Fin 2 → ZMod 2 => q6 v = 1).card = 36) &&
    decide ((Finset.univ.filter fun v : Fin 2 ⊕ Fin 2 ⊕ Fin 2 → ZMod 2 =>
      v ≠ 0 ∧ q6 v = 0).card = 27)

end CFSG.CGT.Foote82.OmegaSix
