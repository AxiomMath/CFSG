module

public import Certificates.Data.Kernel.J4TreeTopEClass

public section

namespace CFSG.KC.J4TreeT

open CFSG.KC.J4Tree CFSG.KC.J4TreeN CFSG.KC.F2W CFSG.J4Tree.Native

@[expose] noncomputable def lamX (B : List Nat) (x : Nat) : Nat :=
  (B.zipIdx).foldl
    (fun acc p => acc ||| (translK (M x p.1) ^^^ translK (M p.1 x)) * 2 ^ (11 * p.2)) 0

@[expose] noncomputable def lamK (T : Tabs) (B : List Nat) (w : Nat) : Nat := lamX B (T.eta w)

@[expose] noncomputable def linC (a b : Nat) : Bool := Nat.beq (M a b / 4096) (M b a / 4096)

structure WHd where
  vs : List Nat
  ws : List Nat
  vas : List Nat
  ms : List Nat
  gs : List (Nat × Nat)
deriving Inhabited

@[expose] def parseWHd (l : List Nat) : WHd :=
  match l with
  | p :: q :: a :: g :: l => ⟨l.take p, (l.drop p).take q, (l.drop (p + q)).take a,
      (l.drop (p + q + a)).take a, pairs ((l.drop (p + q + 2 * a)).take (2 * g))⟩
  | _ => default

@[expose] noncomputable def wLeaf (G : List Nat) (e L X I : Nat) : Bool :=
  !(sqOneK X) || (e == 0 && I == 0) || (L.testBit I && G.any fun s => !commK s X)

@[expose] noncomputable def whdOK (T : Tabs) (B : List Nat) (H : WHd) : Bool :=
  B.all (fun b => sqOneK b && B.all fun b' => commK b b') &&
  H.vs.length + H.ws.length == 11 && H.vas.length == H.ms.length &&
    (H.vs ++ H.ws ++ H.vas).all (fun c => Nat.blt c 2048) && spanAll (H.vs ++ H.ws) &&
    H.vs.all (fun v => B.all fun b => commK (T.eta v) b) &&
    (echB [] (H.ws.map (lamK T B))).length == H.ws.length &&
    (H.vas.zip H.ms).all (fun p =>
      Nat.blt p.2 (2 ^ B.length) && Nat.beq (T.eta p.1) (prodMask B p.2)) &&
    H.gs.all coordOK && (H.gs.map (ccT T)).all (fun s => B.all fun b => commK s b)

@[expose] noncomputable def commV (T : Tabs) (K Ki : Nat) (vs : List Nat) : List Nat :=
  vs.map fun v => translK (T.eta v) ^^^ translK (M (M K (T.eta v)) Ki)

@[expose] noncomputable def walkOK (T : Tabs) (B : List Nat) (H : WHd) (e : Nat) (D : List Nat) :
    Bool :=
  let K := T.kel e
  match D with
  | [0, j] => Nat.blt j B.length && !(linC K (B.getD j 0))
  | [1, v, e'] => Nat.blt e' e && Nat.blt v (2 ^ B.length) &&
      Nat.beq (M K (prodMask B v) / 4096) (T.kel e' / 4096)
  | 2 :: Ki :: ce :: m :: l =>
    let is := l.take m
    let cs := is.map fun i => H.vs.getD i 0
    let L := (l.drop m).headD 0
    let X := M (T.eta ce) K
    invK K Ki && Nat.blt ce 2048 && (e != 0 || ce == 0) && is.length == m &&
      is.all (fun i => Nat.blt i H.vs.length) && B.all (fun b => commK X b) &&
      spanAll (H.vas.map (fun c => translK (T.eta c)) ++ commV T K Ki H.vs ++
        cs.map (fun c => translK (T.eta c)) ++ H.ws.map fun c => translK (T.eta c)) &&
      enumOK (wLeaf (H.gs.map (ccT T)) e L) (cs.map fun c => M (M Ki (T.eta c)) K) X 0 0
  | [3] => (echB [] (H.ws.map (lamK T B) ++ [lamX B K])).length == H.ws.length + 1
  | _ => false

end CFSG.KC.J4TreeT

end
