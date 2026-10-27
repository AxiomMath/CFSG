module

public import Certificates.Data.Kernel.Misc.Base

public section

namespace CFSG.KC.Misc.E6Std

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc

@[expose] noncomputable def rowStarts : Nat :=
  Nat.div (Nat.sub (Nat.shiftLeft 1 24336) 1) (Nat.sub (Nat.shiftLeft 1 156) 1)

@[expose] noncomputable def fullRow : Nat := Nat.sub (Nat.shiftLeft 1 156) 1

@[expose] noncomputable def oneB : Nat :=
  Nat.div (Nat.sub (Nat.shiftLeft 1 24492) 1) (Nat.sub (Nat.shiftLeft 1 157) 1)

@[expose] noncomputable def mulB (A B : Nat) : Nat :=
  letN A fun A => letN B fun B => letN rowStarts fun R => letN fullRow fun F =>
  Nat.rec (motive := fun _ => Nat) (nat_lit 0) (fun k acc => Nat.xor acc (Nat.land
    (Nat.mul (Nat.land (Nat.shiftRight A k) R) F)
    (Nat.mul (Nat.land (Nat.shiftRight B (Nat.mul (nat_lit 156) k)) F) R))) (nat_lit 156)

@[expose] noncomputable def powB (P n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) oneB (fun _ acc => mulB acc P) n

@[expose] noncomputable def bit (x k : Nat) : Nat := Nat.land (Nat.shiftRight x k) (nat_lit 1)

@[expose] noncomputable def codeK (codes a b : Nat) : Nat :=
  Nat.land (Nat.shiftRight codes (Nat.mul (nat_lit 8) (Nat.add (Nat.mul (nat_lit 78) a) b)))
    (nat_lit 255)

@[expose] noncomputable def maskOfK (e : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (Nat.shiftLeft 1 (Nat.sub e 58)) e (Nat.blt e 64)

@[expose] noncomputable def vsmulK (c₀ c₁ v : Nat) : Nat :=
  letN (Nat.land v (Nat.sub (Nat.shiftLeft 1 78) 1)) fun x => letN (Nat.shiftRight v 78) fun y =>
    Nat.lor (Nat.xor (Nat.mul c₀ x) (Nat.mul c₁ y))
      (Nat.shiftLeft (Nat.xor (Nat.mul c₀ y) (Nat.mul c₁ (Nat.xor x y))) 78)

@[expose] noncomputable def rootColK (codes bits r c₀ c₁ l : Nat) : Nat :=
  Nat.xor (Nat.xor (Nat.shiftLeft 1 l) (vsmulK c₀ c₁ (maskOfK (codeK codes r l))))
    (Nat.mul (bit bits (Nat.add (Nat.mul (nat_lit 78) r) l))
      (vsmulK (Nat.xor c₀ c₁) c₁ (Nat.shiftLeft 1 r)))

@[expose] noncomputable def blowCol (l v acc : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) acc (fun k acc =>
    letN (bit v k) fun x₀ => letN (bit v (Nat.add k 78)) fun x₁ =>
    Bool.rec (motive := fun _ => Nat)
      (Nat.lor (Nat.lor acc (Nat.lor
        (Nat.shiftLeft x₀ (Nat.add (Nat.mul (nat_lit 312) k) (Nat.mul 2 l)))
        (Nat.shiftLeft x₁ (Nat.add (Nat.mul (nat_lit 312) k) (Nat.add (Nat.mul 2 l) 1)))))
        (Nat.lor
          (Nat.shiftLeft x₁ (Nat.add (Nat.add (Nat.mul (nat_lit 312) k) 156) (Nat.mul 2 l)))
          (Nat.shiftLeft (Nat.xor x₀ x₁)
            (Nat.add (Nat.add (Nat.mul (nat_lit 312) k) 156) (Nat.add (Nat.mul 2 l) 1)))))
      acc (Nat.beq (Nat.lor x₀ x₁) 0)) (nat_lit 78)

@[expose] noncomputable def rootB (codes bits r c₀ c₁ : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun l acc => letN acc fun acc => blowCol l (rootColK codes bits r c₀ c₁ l) acc) (nat_lit 78)

@[expose] noncomputable def xB (codes bits j c₀ c₁ : Nat) : Nat := rootB codes bits (Nat.add 6 j) c₀ c₁

@[expose] noncomputable def nB (codes bits j : Nat) : Nat :=
  letN (xB codes bits j 1 0) fun X =>
    mulB (mulB X (rootB codes bits (Nat.add 12 (Nat.mul 2 j)) 1 0)) X

@[expose] noncomputable def letterB (codes bits j : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (
  Bool.rec (motive := fun _ => Nat) (
  Bool.rec (motive := fun _ => Nat) (
  Bool.rec (motive := fun _ => Nat) (
  Bool.rec (motive := fun _ => Nat) (
  Bool.rec (motive := fun _ => Nat) (
  Bool.rec (motive := fun _ => Nat) (
  Bool.rec (motive := fun _ => Nat) (
  Bool.rec (motive := fun _ => Nat) (
  Bool.rec (motive := fun _ => Nat) (
  Bool.rec (motive := fun _ => Nat) (nB codes bits 1)
    (nB codes bits 3) (Nat.beq j 10))
    (mulB (nB codes bits 2) (nB codes bits 4)) (Nat.beq j 9))
    (mulB (nB codes bits 0) (nB codes bits 5)) (Nat.beq j 8))
    (xB codes bits 1 1 0) (Nat.beq j 7))
    (xB codes bits 3 1 0) (Nat.beq j 6))
    (mulB (xB codes bits 2 1 1) (xB codes bits 4 0 1)) (Nat.beq j 5))
    (mulB (xB codes bits 2 0 1) (xB codes bits 4 1 1)) (Nat.beq j 4))
    (mulB (xB codes bits 2 1 0) (xB codes bits 4 1 0)) (Nat.beq j 3))
    (mulB (xB codes bits 0 1 1) (xB codes bits 5 0 1)) (Nat.beq j 2))
    (mulB (xB codes bits 0 0 1) (xB codes bits 5 1 1)) (Nat.beq j 1))
    (mulB (xB codes bits 0 1 0) (xB codes bits 5 1 0)) (Nat.beq j 0)

@[expose] noncomputable def nthLL (L : List (List Nat)) (i : Nat) : List Nat :=
  List.rec (motive := fun _ => Nat → List Nat) (fun _ => List.nil)
    (fun x _ ih i => Nat.rec (motive := fun _ => List Nat) x (fun j _ => ih j) i) L i

@[expose] noncomputable def nthV (l : List Nat) (i : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun x _ ih i => Nat.rec (motive := fun _ => Nat) x (fun j _ => ih j) i) l i

@[expose] noncomputable def lineB (vals line : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun i _ ih acc => ih (mulB acc (nthV vals i))) line oneB

@[expose] noncomputable def slpLine (vals : List Nat) (prog : List (List Nat)) (g t : Nat) : Bool :=
  andB (allL (nthLL prog t) fun i => Nat.blt i (Nat.add g t))
    (Nat.beq (lineB vals (nthLL prog t)) (nthV vals (Nat.add g t)))

@[expose] noncomputable def lenLL (L : List (List Nat)) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun _ _ ih => Nat.succ ih) L

@[expose] noncomputable def codesOK (codes : Nat) : Bool :=
  allN 78 fun r => allN 78 fun l => Nat.blt (codeK codes r l) 136

@[expose] noncomputable def tgtOK (F W tgt : List Nat) : Bool :=
  allN 12 fun j => andB (Nat.blt (nthV tgt j) (lenN W)) (Nat.beq (nthV W (nthV tgt j)) (nthV F j))

@[expose] noncomputable def wordB (A B : Nat) (w : List (Nat × Bool)) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun l _ ih acc => ih (Prod.rec (motive := fun _ => Nat) (fun i s =>
      Bool.rec (motive := fun _ => Nat)
        (Bool.rec (motive := fun _ => Nat) (mulB acc (mulB B B)) (mulB acc B) s)
        (mulB acc A) (Nat.beq i 0)) l)) w oneB

@[expose] noncomputable def ordB (P p : Nat) : Bool :=
  letB P fun P => andB (Nat.beq (powB P p) oneB) (notB (Nat.beq P oneB))

end CFSG.KC.Misc.E6Std

end
