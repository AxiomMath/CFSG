module

public import Certificates.Data.Kernel.M24G.Kzero
public import Certificates.Data.Kernel.M24G.Duad
public import Certificates.Data.Kernel.M24G.Steps

public section

namespace CFSG.KC.M24G

open CFSG.Quasithin.H13.AS91.M24G

abbrev KzE : Type := Array Nat × Nat × Nat × Nat

@[expose] def kzRowOK (hs : List (Array Nat × Array Nat)) (D : List KzE) (j : Nat) (e : KzE) :
    Bool :=
  (e.2.1 == 1 && decide (e.2.2.1 < hs.length) && decide (e.2.2.2 < j) &&
      duadEqT e.1 (kzeroConjF (hs.getD e.2.2.1 (#[], #[])) (D.getD e.2.2.2 default).1)) ||
    (e.2.1 == 2 && decide (e.2.2.1 < j) && decide (e.2.2.2 < j) &&
      duadEqT e.1 (mulTabF (D.getD e.2.2.1 default).1 (D.getD e.2.2.2 default).1))

@[expose] def kzRowsOK (hs : List (Array Nat × Array Nat)) (D : List KzE) :
    List KzE → Nat → Bool
  | [], _ => true
  | e :: es, j => kzRowOK hs D j e && kzRowsOK hs D es (j + 1)

@[expose] def kzDerivF (hs : List (Array Nat × Array Nat)) (K : List (Array Nat)) (k : Array Nat)
    (D : List KzE) : Bool :=
  match D with
  | [] => false
  | e :: es => duadEqT e.1 k && kzRowsOK hs (e :: es) es 1 &&
    K.all fun x => (e :: es).any fun f => duadEqT f.1 x

@[expose] def kzDerivAllF (hs : List (Array Nat × Array Nat)) (K : List (Array Nat))
    (Ds : List (List KzE)) : Bool :=
  Ds.length == K.length &&
    (K.zip Ds).all fun kd => duadEqT kd.1 Native.kzeroId || kzDerivF hs K kd.1 kd.2

@[expose] def kzeroUFixF : Bool :=
  Native.uTabs.all fun g => imgSextF g.toList Native.baseSext == Native.baseSext

end CFSG.KC.M24G
