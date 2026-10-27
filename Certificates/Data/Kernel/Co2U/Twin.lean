module

public import Certificates.Data.Kernel.Co2Smith.Rows
public import Certificates.Data.Kernel.F2TriSep
public import Certificates.Data.GF2W1112Co2U

public section

namespace CFSG.KC.Co2U

open CFSG.KC.Loop CFSG.KC.Co2InvS CFSG.KC.Co2Smith CFSG.KC.F2TriSep CFSG.KC.M1F2 CFSG.GF2W1112

@[expose] noncomputable def nthK (P : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun p _ ih i => Nat.rec (motive := fun _ => Nat) p (fun j _ => ih j) i) P

@[expose] noncomputable def evK (P : List Nat) (L : List (Nat × Nat)) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun q _ ih acc => strictN (mulV acc (powK (nthK P q.1) q.2)) ih) L

@[expose] noncomputable def eqCheckK (P : List Nat)
    (eqs : List (List (Nat × Nat) × List (Nat × Nat))) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun q _ ih => (w12UIdxOk q.1 && w12UIdxOk q.2 && eqK (evK P q.1 IDP) (evK P q.2 IDP)) && ih)
    eqs

@[expose] noncomputable def wordsK (A B : Nat) (cs : List (List Char)) : List Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Bool)
    (fun P => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) P)
    (fun c _ ih P => List.rec (motive := fun _ => Bool) false
      (fun p ps _ => eqK (wordB 22 A B (c.map (· == 'a')) (idF 22)) p && ih ps) P) cs

end CFSG.KC.Co2U

end
