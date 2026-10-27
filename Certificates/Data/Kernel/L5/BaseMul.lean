module

public import CFSG.GH74.GLS.C3.Layer2.L5C2e

public section

namespace CFSG.KD.L5

open Equiv CFSG.GH74.GLS.C3.Layer2.L5.Fus

@[expose] def cget (P w a : Nat) : Nat := (P >>> (w * a)) % 2 ^ w

@[expose] def packN (w : Nat) (L : List Nat) : Nat := L.foldr (fun x acc => x + (acc <<< w)) 0

@[expose] def dg (c i : Nat) : Nat := (c >>> (4 * (15 - i))) % 16

@[expose] def keyN (K kw x y : Nat) : Nat := cget K kw (16 * x + y)

@[expose] def mulBN (n C K kw b0 b1 a b : Nat) : Nat :=
  let ca := cget C 64 a
  let cb := cget C 64 b
  keyN K kw (dg ca (dg cb b0)) (dg ca (dg cb b1)) % n

@[expose] def mulB (n C K kw b0 b1 : Nat) (a b : Idx n) : Idx n :=
  ⟨⟨mulBN n C K kw b0 b1 a.v b.v, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) a.v_lt)⟩⟩

@[expose] def invB (n I kw : Nat) (a : Idx n) : Idx n :=
  ⟨⟨cget I kw a.v % n, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) a.v_lt)⟩⟩

@[expose] def codesChk {M : Type} (f : M → Perm (Fin 16)) (elems : List M) (C : Nat) : Bool :=
  decide ((elems.map fun m => codeP16 (f m)) = (List.range elems.length).map (cget C 64))

@[expose] def keyChk (n C K kw b0 b1 : Nat) : Bool :=
  (List.range n).all fun a => decide (keyN K kw (dg (cget C 64 a) b0) (dg (cget C 64 a) b1) = a)

@[expose] def invChkB (n C K kw b0 b1 I o : Nat) : Bool :=
  (List.range n).all fun a => decide (mulBN n C K kw b0 b1 a (cget I kw a % n) = o)

end CFSG.KD.L5

end
