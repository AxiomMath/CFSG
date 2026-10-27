module

public import Certificates.Data.Kernel.Co1BBoundN

public section

universe u

namespace CFSG.KC.Co1BBoundP

open CFSG.KC.M1F2 CFSG.KC.Co1F2 CFSG.KLie.CT CFSG.KC.Co1BBound CFSG.KC.Co1BBoundN

@[expose] noncomputable def strictT {α : Sort u} (y : Nat) (k : Nat → α) : α :=
  Nat.rec (motive := fun _ => α) (k (nat_lit 0)) (fun n _ => k (Nat.succ n)) y

@[expose] noncomputable def onesN (n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun _ acc => Nat.lor (Nat.shiftLeft acc (nat_lit 24)) (nat_lit 1)) n

@[expose] noncomputable def ONES : Nat := onesN (nat_lit 840)

@[expose] noncomputable def vmP (O T P : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun j acc => Nat.xor (Nat.mul (Nat.land (Nat.shiftRight P j) O) (rowF (nat_lit 24) T j)) acc)
    (nat_lit 24)

@[expose] noncomputable def vmPn (nb O : Nat) (TL : List Nat) (a P : Nat) : Nat :=
  nIf(Nat.blt a nb, vmP O (getL (nat_lit 0) TL a) P, nat_lit 0)

@[expose] noncomputable def sumP (nb O : Nat) (TL S : List Nat) (P : Nat) : Nat :=
  S.foldl (fun acc a => Nat.xor acc (vmPn nb O TL a P)) (nat_lit 0)

@[expose] noncomputable def packP (nb O : Nat) (TL : List Nat) (P : Nat) (CP : List (List Nat)) :
    (List (Nat × Nat × Nat) → Nat) → Nat :=
  List.rec (motive := fun _ => (List (Nat × Nat × Nat) → Nat) → Nat) (fun kont => kont [])
    (fun c _ ih kont => strictT (sumP nb O TL c.tail.tail P) fun Q =>
      ih fun L => kont ((c.headD 0, c.tail.headD 0, Q) :: L)) CP

@[expose] noncomputable def condsQ (XB : Nat → Nat) (QS : List (Nat × Nat × Nat)) (k : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun q _ ih => andB (Nat.beq (typK XB (Nat.xor q.2.1
      (CFSG.KC.Enum.pg (nat_lit 24) (CFSG.KS.mask (nat_lit 24)) q.2.2 k))) q.1) ih) QS

@[expose] noncomputable def cntChunkP (nb : Nat) (XB : Nat → Nat) (TL : List Nat) (O : Nat)
    (CP CR : List (List Nat)) (P : Nat) : Nat :=
  packP nb O TL P CP fun QS =>
    Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun k acc => Bool.rec (motive := fun _ => Nat) acc (Nat.succ acc)
        (andB (condsQ XB QS k)
          (condsKn nb XB TL CR (CFSG.KC.Enum.pg (nat_lit 24) (CFSG.KS.mask (nat_lit 24)) P k))))
      (nat_lit 840)

@[expose] noncomputable def cntTabP (nb : Nat) (XB : Nat → Nat) (TL : List Nat)
    (CP CR : List (List Nat)) (F : Nat → Nat) (a m : Nat) : Nat :=
  strictT ONES fun O =>
    Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun j acc => Nat.add (strictT (F (Nat.add a j)) fun P => cntChunkP nb XB TL O CP CR P) acc) m

@[expose] noncomputable def lvlChunkP (nb : Nat) (XB : Nat → Nat) (TL : List Nat)
    (CF : List (List (List Nat))) (NP : List Nat) (F : Nat → Nat) (CN : List (List Nat)) (n : Nat) :
    Bool :=
  Nat.beq
    (cntTabP nb XB TL ((CF.getD (Nat.div n 9) []).take (getL 1 NP (Nat.div n 9)))
      ((CF.getD (Nat.div n 9) []).drop (getL 1 NP (Nat.div n 9))) F (Nat.mul 13 (Nat.mod n 9)) 13)
    (getL 0 (CN.getD (Nat.div n 9) []) (Nat.mod n 9))

@[expose] def selC {α : Type u} (conds : List α) (sel : List Nat) : List α :=
  sel.filterMap fun i => conds[i]?

@[expose] noncomputable def storeSel (nb : Nat) (XB : Nat → Nat) (TL b : List Nat) (u : Nat)
    (conds : List (List Nat × List (Nat × Nat))) (sel : List Nat) : List (List Nat) :=
  storeKn nb XB TL b u (selC conds sel)

end CFSG.KC.Co1BBoundP

end
