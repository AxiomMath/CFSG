module

public import Certificates.Data.Kernel.J4TreeNode

public section

namespace CFSG.KC.J4TreeT

open CFSG.KC.J4Tree CFSG.KC.J4TreeN CFSG.KC.F2W CFSG.J4Tree.Native

@[expose] def redV : List Nat → Nat → Nat
  | [], v => v
  | b :: B, v => redV B (if Nat.blt (v ^^^ b) v then v ^^^ b else v)

@[expose] def insDesc (v : Nat) : List Nat → List Nat
  | [] => [v]
  | b :: B => if Nat.blt b v then v :: b :: B else b :: insDesc v B

@[expose] def echB : List Nat → List Nat → List Nat
  | B, [] => B
  | B, v :: vs => echB (let r := redV B v; if r = 0 then B else insDesc r B) vs

@[expose] def spanAll (vs : List Nat) : Bool :=
  vs.all (fun v => Nat.blt v 2048) && (echB [] vs).length == 11

@[expose] noncomputable def commE (T : Tabs) (K Ki : Nat) : List Nat :=
  (List.range 11).map fun j => translK (T.eta (2 ^ j)) ^^^ translK (M (M K (T.eta (2 ^ j))) Ki)

@[expose] noncomputable def ecLeaf (e L X I : Nat) : Bool :=
  !(sqOneK X) || (e == 0 && I == 0) || L.testBit I

@[expose] noncomputable def eclassOK (T : Tabs) (z e : Nat) (D : List Nat) : Bool :=
  match D with
  | Ki :: m :: l =>
    let K := T.kel e
    let cs := l.take m
    let L := (l.drop m).headD 0
    invK K Ki && Nat.blt e 1024 && cs.length == m && cs.all (fun c => Nat.blt c 2048) &&
      spanAll (translK (T.eta z) :: commE T K Ki ++ cs.map fun c => translK (T.eta c)) &&
      enumOK (ecLeaf e L) (cs.map fun c => M (M Ki (T.eta c)) K) K 0 0
  | _ => false

end CFSG.KC.J4TreeT

end
