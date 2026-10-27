module

public import Certificates.Data.Kernel.SporCov.F2Kit
public import Certificates.Data.Kernel.SporCov.Census
public import Certificates.Data.Kernel.SporCov.PCl

public section

namespace CFSG.KC.SporCov

open CFSG.KLie.CT CFSG.KC.Loop CFSG.KC.M1F2 CFSG.KC.Co1F2 CFSG.KC.F2W

@[expose] noncomputable def letR (MA MAi MB MBi : Nat) (Ms : List Nat) (c : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (nthN Ms (Nat.sub c (nat_lit 4))) (letF MA MAi MB MBi c)
    (Nat.blt c (nat_lit 4))

@[expose] noncomputable def mwR (d MA MAi MB MBi : Nat) (Ms : List Nat) (w : List Nat)
    (acc : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun c _ ih acc => strictN (mulW d (letR MA MAi MB MBi Ms c) acc) ih) w acc

@[expose] noncomputable def keyR (d MA MAi MB MBi : Nat) (Ms : List Nat) (u : List Nat) : Nat :=
  mwR d MA MAi MB MBi Ms u (idF d)

@[expose] noncomputable def eqR (d MA MAi MB MBi : Nat) (Ms : List Nat) (u v : List Nat) : Bool :=
  Nat.beq (keyR d MA MAi MB MBi Ms u) (keyR d MA MAi MB MBi Ms v)

@[expose] noncomputable def letRL (n c : Nat) : Bool := Nat.blt c (Nat.add (nat_lit 4) n)

@[expose] noncomputable def regOK (d MA MAi MB MBi : Nat) (Ms : List Nat) (Rg : List (List Nat))
    (i : Nat) : Bool :=
  chW (letRL i) (nthW Rg i) && Nat.beq (keyR d MA MAi MB MBi Ms (nthW Rg i)) (nthN Ms i)

@[expose] noncomputable def kitR (d MA MB eA eB : Nat) (Ms : List Nat) (Rg : List (List Nat))
    (n : Nat) (k : (List Nat → List Nat → Bool) → (List Nat → Nat) → Bool) : Bool :=
  strictB (powK d MA (Nat.pred eA)) fun MAi => strictB (powK d MB (Nat.pred eB)) fun MBi =>
    andB (Nat.beq (mulF d MA MAi) (idF d)) (andB (Nat.beq (mulF d MB MBi) (idF d))
      (andB (allLt n (regOK d MA MAi MB MBi Ms Rg))
        (k (eqR d MA MAi MB MBi Ms) (keyR d MA MAi MB MBi Ms))))

end CFSG.KC.SporCov

end
