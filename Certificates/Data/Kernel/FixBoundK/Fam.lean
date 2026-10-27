module

public import Certificates.Data.Kernel.FixBoundK.Fix

public section

namespace CFSG.KC.FixBoundK

@[expose] noncomputable def packMs (ms : List Mem) (w M : Nat) (u₀ acc₀ : Nat)
    (k : Nat → Nat → Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat) (fun u acc => k u acc)
    (fun e _ ih u acc => withN (Nat.succ u) (fun u' =>
      withN (Nat.lor acc (Nat.shiftLeft (Nat.lor e.1 M) (Nat.mul w u))) (fun acc' => ih u' acc')))
    ms u₀ acc₀

@[expose] noncomputable def packFam (ch : List (Nat × List Mem)) (i w M : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat) (fun _ acc => acc)
    (fun c _ ih u acc => Bool.rec (motive := fun _ => Nat) (ih u acc)
      (packMs c.2 w M u acc ih) (Nat.beq c.1 i))
    ch (nat_lit 0) (nat_lit 0)

@[expose] noncomputable def slotS (x w u : Nat) : Nat :=
  Nat.land (Nat.shiftRight x (Nat.mul w u)) (Nat.sub (Nat.shiftLeft (nat_lit 1) w) (nat_lit 1))

@[expose] noncomputable def nxtS (m piv j : Nat) : Nat :=
  Nat.land (Nat.succ (Nat.lor j piv)) (Nat.xor (Nat.sub m (nat_lit 1)) piv)

@[expose] noncomputable def covS (m BS A piv : Nat) (zs : List Nat) (acc₀ : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun acc => Nat.beq acc piv)
    (fun z _ ih acc => withN (Nat.land z piv) (fun t =>
      bAnd(Nat.blt z m,
      bAnd(Nat.beq (Nat.land A (slotS BS m z)) A,
      bAnd(Nat.blt (nat_lit 0) t,
      bAnd(Nat.beq (Nat.land t (Nat.sub t (nat_lit 1))) (nat_lit 0),
      bAnd(Nat.beq (Nat.land t acc) (nat_lit 0), ih (Nat.lor acc t))))))))
    zs acc₀

@[expose] noncomputable def lookS (m w M PF BS A piv : Nat) (vs : List Nat) (j₀ : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun j => Nat.beq j (nat_lit 0))
    (fun v _ ih j => bAnd(Nat.blt (nat_lit 0) j,
      bAnd(Nat.beq (slotS PF w v) (Nat.lor (Nat.land A (slotS BS m j)) M),
        withN (nxtS m piv j) ih)))
    vs j₀

abbrev FamC := Nat × List Nat × List Nat

@[expose] noncomputable def famMs (m w M PF BS : Nat) (cs : List FamC) (u₀ : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun c _ ih u => bAnd(
      withN (Nat.land (slotS PF w u) (Nat.sub M (nat_lit 1))) (fun A =>
        bAnd(Nat.beq (Nat.land c.1 (Nat.sub m (nat_lit 1))) c.1,
        bAnd(covS m BS A c.1 c.2.1 (nat_lit 0),
          lookS m w M PF BS A c.1 c.2.2 (nxtS m c.1 (nat_lit 0))))),
      withN (Nat.succ u) ih))
    cs u₀

@[expose] noncomputable def famW (cs : List FamC) (m w M PF BS : Nat) : Bool :=
  withN (lenS cs) (fun n =>
    bAnd(Nat.beq (Nat.shiftRight PF (Nat.mul w n)) (nat_lit 0),
    bAnd(Nat.beq (slotS PF w (Nat.sub n (nat_lit 1))) (Nat.lor (Nat.sub M (nat_lit 1)) M),
      famMs m w M PF BS cs (nat_lit 0))))

@[expose] noncomputable def famRep (p : Rep) (ch : List (Nat × List Mem)) (i : Nat)
    (cs : List FamC) : Bool :=
  withN (lenS p.2.1) (fun m => withN (Nat.succ m) (fun w =>
    withN (Nat.shiftLeft (nat_lit 1) m) (fun M =>
      withN (packFam ch i w M) (fun PF =>
        withN (packS p.2.2.1 m (nat_lit 0)) (fun BS => famW cs m w M PF BS)))))

@[expose] noncomputable def famAt (reps : List Rep) (ch : List (Nat × List Mem))
    (fc : List (List FamC)) (i : Nat) : Bool :=
  famRep (nthS repD reps i) ch i (nthS [] fc i)

end CFSG.KC.FixBoundK

end
