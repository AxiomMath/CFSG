module

public import Certificates.Data.Kernel.MonsterB.Rep4371XNf

public section

namespace CFSG.KC.Rep4371X

open CFSG.KC CFSG.KC.KDense CFSG.KC.Loop CFSG.KC.Rep4371Row CFSG.KC.BM.Pkt

@[expose] noncomputable def revT (L M : Terms) : Terms :=
  List.rec (motive := fun _ => Terms → Terms) (fun M => M) (fun e _ ih M => ih (List.cons e M)) L M

@[expose] noncomputable def eqI (m m' : Int) : Bool := isZI (Int.sub m m')

@[expose] noncomputable def eqTL (L M : Terms) : Bool :=
  List.rec (motive := fun _ => Terms → Bool) (fun M => nilB M)
    (fun e _ ih M => List.rec (motive := fun _ => Bool) false
      (fun e' M' _ => bAnd(Nat.beq e.1 e'.1, bAnd(eqI e.2 e'.2, ih M'))) M) L M

@[expose] noncomputable def tauStep (st : Nat × Terms × Bool) (v : Nat) : Nat × Terms × Bool :=
  (fun t => Bool.rec (motive := fun _ => Nat × Terms × Bool) (st.1, List.cons t st.2.1, st.2.2)
      (Nat.succ st.1, List.nil, bAnd(st.2.2, eqTL (revT (List.cons t st.2.1) List.nil) (tauT st.1)))
      (Nat.beq (Nat.div v (nat_lit 65536)) (nat_lit 1)))
    (Nat.mod v (nat_lit 8192), numT (Nat.mod (Nat.div v (nat_lit 8192)) (nat_lit 8)))

@[expose] noncomputable def tauScan (N m : Nat) (st : Nat × Terms × Bool) : Nat × Terms × Bool :=
  Nat.rec (motive := fun _ => Nat × Terms × Bool) st (fun j ih => tauStep ih (entV N j)) m

@[expose] noncomputable def tauLineChk (p : Nat × Nat) : Bool :=
  (fun st => bAnd(Nat.beq st.1 (nat_lit 4371), bAnd(nilB st.2.1, st.2.2)))
    (tauScan p.1 (Nat.div p.2 (nat_lit 3)) (nat_lit 0, List.nil, true))

end CFSG.KC.Rep4371X

end
