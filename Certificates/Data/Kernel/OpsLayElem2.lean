module

public import Certificates.Data.Kernel.OpsV4
public import CFSG.Sporadic.GLQ.RegisterProgram

public section

namespace CFSG.KC.OpsLayElem2

open CFSG.SectionRank.Native CFSG.Sporadic.GLQ CFSG.KC.LQT CFSG.KC.OpsLayK CFSG.KC.OpsV4

@[expose] noncomputable def forceL (xs : List Nat) : (List Nat → Bool) → Bool :=
  List.rec (motive := fun _ => (List Nat → Bool) → Bool) (fun k => k [])
    (fun x _ ih k => strictB x fun v => ih fun vs => k (v :: vs)) xs

@[expose] noncomputable def elem2K (c : Lay) (A B : Nat) (ws : List (List ℤ)) (tests : List Nat) :
    Bool :=
  tests.all (decide <| · < c.d) &&
    strictB (powK c B 12) fun B' =>
      forceL (ws.map (signedWordN (opsL c) (A, A) (B, B'))) fun xs => elem2OK (opsL c) xs tests

end CFSG.KC.OpsLayElem2

end
