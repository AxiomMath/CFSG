module

public import Certificates.Data.Kernel.S151IdxF
public import Certificates.Data.CFSGNative.SporLat.Code

public section

namespace CFSG.KC.IdxG

open CFSG.KC.E64F CFSG.KC.IdxF CFSG.Quasithin.S151S9T CFSG.QuasithinUnique.Ch1.SporLat

@[expose] def idx3OkG (W : Idx3Wit) (n : Nat) (fx : (Nat → Nat) → Bool) (nm ns : Nat)
    (mlen : Nat → Nat) (M : Nat → Nat → Nat → Nat) (Sl : Nat → Nat → Nat) (z : Nat → Nat) : Bool :=
  decide (W.p < nm) && mlen W.p == 1 &&
    W.xw.all (fun l => decide (l < ns + 1)) &&
    W.czv.length == nm &&
    ((List.range nm).all fun j => W.czv.getD j false ==
      (List.range (mlen j)).all fun k =>
        eqOn n (fun p => z (M j (ns + k) p)) (fun p => M j (ns + k) (z p))) &&
    idOn n (fun p => xF W M (xF W M (xF W M p))) && !idOn n (xF W M) &&
    W.rw.length == 5 && W.ri.length == 5 &&
    (List.range 5).all (fun i =>
      (W.rw.getD i []).all (fun l => decide (l < ns)) &&
        (W.ri.getD i []).all (fun l => decide (l < ns)) &&
        idOn n (fun p => wordF Sl (W.rw.getD i []) (wordF Sl (W.ri.getD i []) p)) &&
        fx (wordF (three (xF W M) (wordF Sl (W.rw.getD i [])) id) [0, 0, 1, 0]) &&
        fx (wordF (three (xF W M) (wordF Sl (W.rw.getD i [])) id) [0, 1, 0, 0])) &&
    distinct5 n (fun i => wordF (three (wordF Sl (W.rw.getD i [])) (xF W M)
      (wordF Sl (W.ri.getD i []))) dcWord)

@[expose] def codeF (n : Nat) (f : Nat → Nat) (c : Nat) : Nat :=
  encodeSet n (insN ((decodeSet n c c).map f))

@[expose] def codeSetF (n : Nat) (f : Nat → Nat) (L : List Nat) : List Nat :=
  insN (L.map (codeF n f))

@[expose] def fixCodes (n : Nat) (Δ : List Nat) (f : Nat → Nat) : Bool := codeSetF n f Δ == Δ

@[expose] def codesBelow (n : Nat) (Δ : List Nat) : Bool :=
  Δ.all fun c => (decodeSet n c c).all fun p => decide (p < n)

end CFSG.KC.IdxG

end
