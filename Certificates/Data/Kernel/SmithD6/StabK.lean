module

public import Certificates.Data.Kernel.KeyTreeChunks

public section

namespace CFSG.KD.SmithD6Stab

open CFSG.KC.Loop CFSG.KC.KeyTree

@[expose] def par6K (x : Nat) : Bool := ((0x6996966996696996 : Nat) >>> x) &&& 1 == 1

@[expose] def bfK (x y : Nat) : Bool :=
  par6K ((x &&& 63) &&& (y >>> 6)) ^^ par6K ((y &&& 63) &&& (x >>> 6))

@[expose] def sglK (u w x : Nat) : Nat :=
  (x ^^^ (if bfK x w then u else 0)) ^^^ (if bfK x u then w else 0)

@[expose] def pairK (k : Nat) : Nat × Nat := (k / 4096, k % 4096)

@[expose] def meetP (p0 p : Nat × Nat) : Nat :=
  ([p0.1, p0.2, p0.1 ^^^ p0.2].filter fun x => [p.1, p.2, p.1 ^^^ p.2].contains x).length

@[expose] def rankP (p0 p : Nat × Nat) : Nat :=
  let r0 := (bfK p0.1 p.1).toNat + 2 * (bfK p0.1 p.2).toNat
  let r1 := (bfK p0.2 p.1).toNat + 2 * (bfK p0.2 p.2).toNat
  if r0 == 0 && r1 == 0 then 0 else if r0 == 0 || r1 == 0 || r0 == r1 then 1 else 2

@[expose] def clsP (z : Bool) (p0 p : Nat × Nat) : Nat :=
  if z then 0
  else if meetP p0 p == 1 then (if rankP p0 p == 0 then 1 else 2)
  else if rankP p0 p == 0 then 3 else if rankP p0 p == 1 then 4 else 5

@[expose] def clsK (k : Nat) : Nat := clsP (k == 4098) (pairK 4098) (pairK k)

@[expose] noncomputable def cntGo (l : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun a => a)
    (fun k _ ih a => strictN (Nat.add a (Nat.pow 2 (Nat.mul 19 (clsK k)))) ih) l

@[expose] noncomputable def firstGo (r : Nat → Nat) (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun k _ ih => bAnd(Nat.ble (r (clsK k)) k, ih)) l

@[expose] def prodStepP (pa pb : Nat × Nat) (x : Nat) : Nat := sglK pa.1 pa.2 (sglK pb.1 pb.2 x)

@[expose] def prodPowP (pa pb : Nat × Nat) : Nat → Nat → Nat
  | 0, x => x
  | n + 1, x => prodPowP pa pb n (prodStepP pa pb x)

@[expose] def ordOKP (pa pb : Nat × Nat) (o : Nat) : Bool :=
  (List.range 4096).all (fun x => prodPowP pa pb o x == x) &&
  (if o == 1 then true
   else if o == 4 then (List.range 4096).any fun x => prodPowP pa pb 2 x != x
   else (List.range 4096).any fun x => prodStepP pa pb x != x)

@[expose] def repKeys : List Nat := [4098, 4100, 4224, 16392, 16448, 262272]

@[expose] def repPos : List Nat := [0, 1, 31, 1579, 1607, 31899]

@[expose] def ordL : List Nat := [1, 2, 2, 2, 4, 3]

@[expose] noncomputable def clsChunkOK (cs : List (List Nat)) (ns : List Nat) (c : Nat) : Bool :=
  (fun l => bAnd(firstGo (fun c' => repKeys.getD c' 0) l, Nat.beq (cntGo l 0) (ns.getD c 0)))
    (nthC cs c)

@[expose] noncomputable def repOK (t : KT) (c : Nat) : Bool :=
  clsK (repKeys.getD c 0) == c && KT.find (repKeys.getD c 0) t == repPos.getD c 0 + 1 &&
  ordOKP (pairK 4098) (pairK (repKeys.getD c 0)) (ordL.getD c 0)

end CFSG.KD.SmithD6Stab

end
