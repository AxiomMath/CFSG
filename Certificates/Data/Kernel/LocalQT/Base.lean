module

public import Certificates.Data.Kernel.LocalQT.Lat

public section

namespace CFSG.KC.LQT.BC

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.LQT.S CFSG.KC.LQT.L

@[expose] noncomputable def codeL (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun x _ ih => Nat.add x (Nat.shiftLeft ih 5)) l

@[expose] noncomputable def tabL (n : Nat) (l : List Nat) : Bool :=
  andB (Nat.beq (lenA l) n) (allL l fun v => Nat.blt v n)

@[expose] noncomputable def slpOKK (prog : List (Nat × Nat)) (m : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun p _ ih m => andB (andB (Nat.blt p.1 m) (Nat.blt p.2 m)) (ih (Nat.succ m))) prog m

@[expose] noncomputable def nodeK (R : List Nat) (j : Nat) : Nat :=
  getK R (Nat.sub (Nat.sub (lenA R) 1) j)

@[expose] noncomputable def slpK (n a b : Nat) (prog : List (Nat × Nat)) : List Nat :=
  List.rec (motive := fun _ => List Nat → List Nat) (fun acc => acc)
    (fun p _ ih acc => ih (List.cons (mul n (nodeK acc p.1) (nodeK acc p.2)) acc)) prog [b, a]

@[expose] noncomputable def baseQ (n : Nat) (G : List Nat) (z wg wh k fuel d : Nat) : Bool :=
  allBs [closedK n G (bfsK n G d), Nat.beq (bfsK n G d).size (Nat.pow 2 k),
    Nat.ble (bfsK n G d).size fuel,
    allL (bfsK n G d).elems (fun x => impB (allL G fun g => Nat.beq (mul n x g) (mul n g x))
      (orB (Nat.beq x (one n)) (Nat.beq x z))),
    memT (bfsK n G d).t wg, memT (bfsK n G d).t wh,
    notB (Nat.beq (mul n wg wh) (mul n wh wg))]

@[expose] noncomputable def baseR (n : Nat) (R : List Nat) (qp : List (Nat × Nat))
    (zn gn gin hn hin k fuel d : Nat) : Bool :=
  andB (allA qp fun p => andB (Nat.blt p.1 (lenA R)) (Nat.blt p.2 (lenA R)))
  (andB (allBs [Nat.blt zn (lenA R), Nat.blt gn (lenA R), Nat.blt gin (lenA R),
     Nat.blt hn (lenA R), Nat.blt hin (lenA R)])
  (andB (allA qp fun p => Nat.beq (mul n (nodeK R p.2) (nodeK R p.1)) (one n))
  (andB (Nat.beq (mul n (nodeK R gin) (nodeK R gn)) (one n))
  (andB (Nat.beq (mul n (nodeK R hin) (nodeK R hn)) (one n))
  (letB (nodeK R zn) fun z =>
    letB (mul n (nodeK R gin) (mul n z (nodeK R gn))) fun wg =>
    letB (mul n (nodeK R hin) (mul n z (nodeK R hn))) fun wh =>
    baseQ n (List.rec (motive := fun _ => List Nat) [] (fun p _ ih => List.cons (nodeK R p.1) ih)
      qp) z wg wh k fuel d)))))

@[expose] noncomputable def baseK (n : Nat) (ta tb : List Nat) (prog : List (Nat × Nat))
    (qp : List (Nat × Nat)) (zn gn gin hn hin k fuel d : Nat) : Bool :=
  andB (tabL n ta) (andB (tabL n tb) (andB (slpOKK prog 2)
    (baseR n (slpK n (codeL ta) (codeL tb) prog) qp zn gn gin hn hin k fuel d)))

end CFSG.KC.LQT.BC

end
