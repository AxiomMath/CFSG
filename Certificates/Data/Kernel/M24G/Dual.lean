module

public import Certificates.Data.CFSGNative.AS91.M24Geom

public section

namespace CFSG.KC.M24G

open CFSG.Quasithin.H13.AS91.M24G

@[expose] def dualCk (LU : List Nat) (tr : Nat → Nat × Nat × Nat) (O : List Nat) : Bool :=
  let mt := fun a b => Native.meets (tr a) (tr b)
  let Sp := (Native.combs 5 LU).filter fun D => D.all fun d => D.all fun k => d == k || !(mt d k)
  LU.length == 15 && Sp.length == 6 &&
    LU.all (fun l => (Sp.filter (·.contains l)).length == 2) &&
    Sp.all (fun D => Sp.all fun D' => D == D' || (D.filter (D'.contains ·)).length == 1) &&
    Sp.all (fun D => O.all fun o => (D.filter fun k => (Native.octsT (tr k)).contains o).length == 1) &&
    (Native.combs 3 LU).all (fun c => !(c.all fun a => c.all fun b => a == b || mt a b) ||
      O.any fun o => c.all fun k => (Native.octsT (tr k)).contains o) &&
    LU.all fun a => LU.all fun b => a == b || (mt a b == !(Sp.any fun D => D.contains a &&
      D.contains b))

@[expose] def tabLU (LU : List Nat) (TU : List (Nat × Nat × Nat)) (a : Nat) : Nat × Nat × Nat :=
  ((LU.zip TU).lookup a).getD (0, 0, 0)

end CFSG.KC.M24G
