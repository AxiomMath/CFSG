module

public import CFSG.Certificates.Kernel.BabyMonster.PktCheck

public section

namespace CFSG.KC.BM.Pkt

open CFSG.KC.BM CFSG.KC.YModel

@[expose] noncomputable def shStep (st : Nat × Nat × Bool) (v : Nat) : Nat × Nat × Bool :=
  (fun j ok => Bool.rec (motive := fun _ => Nat × Nat × Bool) (st.1, Nat.succ j, ok)
      (Nat.succ st.1, nat_lit 0, ok) (Nat.beq (Nat.div v (nat_lit 65536)) (nat_lit 1)))
    (Nat.mod v (nat_lit 8192))
    (andB st.2.2 (andB (Nat.blt (Nat.mod v (nat_lit 8192)) (nat_lit 4371))
      (Nat.ble st.2.1 (Nat.mod v (nat_lit 8192)))))

@[expose] noncomputable def shapeOK (p : Nat × Nat) : Bool :=
  (fun st => andB (Nat.beq st.1 (nat_lit 4371)) st.2.2)
    (Nat.rec (motive := fun _ => Nat × Nat × Bool) (nat_lit 0, nat_lit 0, true)
      (fun i ih => shStep ih (entV p.1 i)) (Nat.div p.2 (nat_lit 3)))

@[expose] noncomputable def countOK (CH : List (Nat × Nat)) (S : List Nat) : Bool :=
  Nat.beq (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i ih => Nat.add ih (Nat.div (lineOf CH S i).2 (nat_lit 3))) (nat_lit 48)) (nat_lit 259183)

end CFSG.KC.BM.Pkt

end
