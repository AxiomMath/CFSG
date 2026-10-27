module

public import Certificates.Data.Kernel.BabyMonster.PcFive

public section

namespace CFSG.KC.HN.PcFive

open CFSG.KC.BM.PcFive

@[expose] def cmHN : CM := ⟨4, 0, 0, 0, 0, 4⟩

@[expose] def xActHN : QAct :=
  ⟨⟨1, 1, 4, 2, 1⟩, ⟨3, 4, 1, 3, 0⟩, ⟨3, 0, 0, 2, 1⟩, ⟨2, 0, 2, 4, 4⟩, ⟨0, 0, 0, 0, 1⟩⟩

@[expose] def qHN : QAct :=
  ⟨⟨0, 0, 2, 3, 0⟩, ⟨1, 0, 4, 4, 1⟩, ⟨2, 0, 1, 1, 1⟩, ⟨1, 1, 2, 1, 4⟩, ⟨0, 0, 0, 0, 1⟩⟩

@[expose] def indepV (t a b : V6) : Bool :=
  allBelow (fun i => allBelow (fun j => allBelow (fun l =>
    (i.beq 0 && j.beq 0 && l.beq 0) ||
      !(mulV (mulV (powV t i) (powV a j)) (powV b l)).isOne) 5) 5) 5

@[expose] def tripV (t a b : V6) : Bool :=
  (mulV t a).beq (mulV a t) && (mulV t b).beq (mulV b t) && (mulV a b).beq (mulV b a) &&
    ord5 t && ord5 a && ord5 b && indepV t a b

@[expose] def e3OK (rep ea eb : Nat → Nat) (nc : Nat) : Bool :=
  allBelow (fun c => tripV (dec (rep c)) (dec (ea c)) (dec (eb c))) nc

end CFSG.KC.HN.PcFive

end
