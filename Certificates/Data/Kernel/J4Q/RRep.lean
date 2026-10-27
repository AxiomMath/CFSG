module

public import Certificates.Data.Kernel.J4Q.QT2A

public section

namespace CFSG.KC.J4RR

open CFSG.KC.Loop CFSG.KC.J4Q

@[expose] noncomputable def getL (l : List (List Nat)) (i : Nat) : List Nat :=
  List.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun m _ ih i => Nat.rec (motive := fun _ => List Nat) m (fun j _ => ih j) i) l i

@[expose] noncomputable def entE (E i : Nat) : Nat :=
  Nat.land (Nat.shiftRight E (Nat.mul (nat_lit 20) i)) (nat_lit 1048575)

@[expose] noncomputable def depE (E i : Nat) : Nat := Nat.mod (entE E i) (nat_lit 16)

@[expose] noncomputable def rrMaskK : List Nat := [0, 503, 3741, 3946]

@[expose] noncomputable def rMaskK : List Nat := [1, 2, 5, 6, 7, 10, 12]

@[expose] noncomputable def isQ8K (m : Nat) : Bool :=
  orB (Nat.beq m (nat_lit 0)) (orB (Nat.beq m (nat_lit 503))
    (orB (Nat.beq m (nat_lit 3741)) (Nat.beq m (nat_lit 3946))))

@[expose] noncomputable def matQ (c rm : Nat) (lo hi : List Nat) (m : Nat) : Nat :=
  mulJ c rm (getN 0 lo (Nat.mod m (nat_lit 64))) (getN 0 hi (Nat.div m (nat_lit 64)))

@[expose] noncomputable def zIf (c rm z : Nat) (b : Bool) (x : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) x (mulJ c rm x z) b

@[expose] noncomputable def rootK (c rm z : Nat) (lo hi : List Nat) (idx rest : Nat) : Bool :=
  andB (Nat.blt rest (nat_lit 56))
    (strictB (Nat.mod rest (nat_lit 8)) fun r =>
      strictB (getN 0 rrMaskK (Nat.mod r (nat_lit 4))) fun m' =>
        Nat.beq (matQ c rm lo hi (Nat.mod idx (nat_lit 4096)))
          (zIf c rm z (notB (Nat.beq (Nat.div idx (nat_lit 4096)) (Nat.div r (nat_lit 4))))
            (mulJ c rm (getN 0 lo (getN 0 rMaskK (Nat.div rest (nat_lit 8)))) (matQ c rm lo hi m'))))

@[expose] noncomputable def stepK (c rm : Nat) (lo hi : List Nat) (gl hg hz : List (List Nat))
    (E idx d rest : Nat) : Bool :=
  strictB (Nat.mod rest (nat_lit 4)) fun g => strictB (Nat.div rest (nat_lit 4)) fun nx =>
    andB (Nat.blt g (nat_lit 3)) (andB (Nat.blt nx (nat_lit 8192))
      (andB (notB (isQ8K (Nat.mod nx (nat_lit 4096))))
        (andB (Nat.beq (Nat.succ (depE E nx)) d)
          (strictB (Nat.mod idx (nat_lit 4096)) fun m => strictB (Nat.mod nx (nat_lit 4096)) fun m' =>
            Nat.beq
              (mulJ c rm (getN 0 (getL gl g) (Nat.mod m (nat_lit 64))) (getN 0 hi (Nat.div m (nat_lit 64))))
              (mulJ c rm (getN 0 lo (Nat.mod m' (nat_lit 64)))
                (getN 0 (getL (Bool.rec (motive := fun _ => List (List Nat)) hz hg
                    (Nat.beq (Nat.div idx (nat_lit 4096)) (Nat.div nx (nat_lit 4096)))) g)
                  (Nat.div m' (nat_lit 64))))))))

@[expose] noncomputable def rrIdxK (c rm z : Nat) (lo hi : List Nat) (gl hg hz : List (List Nat))
    (E idx : Nat) : Bool :=
  orB (isQ8K (Nat.mod idx (nat_lit 4096)))
    (strictB (entE E idx) fun en =>
      strictB (Nat.mod en (nat_lit 16)) fun d => strictB (Nat.div en (nat_lit 16)) fun rest =>
        Bool.rec (motive := fun _ => Bool) (stepK c rm lo hi gl hg hz E idx d rest)
          (rootK c rm z lo hi idx rest) (Nat.beq d (nat_lit 0)))

@[expose] noncomputable def rrBlkK (c rm z : Nat) (lo hi : List Nat) (gl hg hz : List (List Nat))
    (E k : Nat) : Bool :=
  allR (nat_lit 128) fun j => rrIdxK c rm z lo hi gl hg hz E (Nat.add (Nat.mul (nat_lit 128) k) j)

end CFSG.KC.J4RR

end
