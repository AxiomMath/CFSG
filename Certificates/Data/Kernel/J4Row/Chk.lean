module

public import Certificates.Data.Kernel.J4Q.Mat
public import Certificates.Data.Kernel.J4Q.QT

public section

namespace CFSG.KC.J4Row

open CFSG.KC.Loop CFSG.KC.J4Q

@[expose] noncomputable def getP (one : Nat) (R : List (Nat × Nat)) (d : Nat) : Nat × Nat :=
  List.rec (motive := fun _ => Nat → Nat × Nat) (fun _ => Prod.mk one one)
    (fun p ps ih i => Nat.rec (motive := fun _ => Nat × Nat) p
      (fun j _ => List.rec (motive := fun _ => Nat × Nat) p (fun _ _ _ => ih j) ps) i) R d

@[expose] noncomputable def regP (one : Nat) (R : List (Nat × Nat)) (L i : Nat) : Nat × Nat :=
  getP one R (Nat.sub (Nat.sub L (nat_lit 1)) i)

@[expose] noncomputable def allR {α : Type} (f : α → Bool) (l : List α) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun x _ ih => andB (f x) ih) l

@[expose] noncomputable def memR (x : Nat) (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun y _ ih => orB (Nat.beq x y) ih) l

@[expose] noncomputable def lenR {α : Type} (l : List α) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun _ _ ih => Nat.succ ih) l

@[expose] noncomputable def getLR (l : List (List Nat)) (i : Nat) : List Nat :=
  List.rec (motive := fun _ => Nat → List Nat) (fun _ => List.nil)
    (fun x _ ih i => Nat.rec (motive := fun _ => List Nat) x (fun j _ => ih j) i) l i

@[expose] noncomputable def allBelowR (n : Nat) (f : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun i ih => andB (f i) ih) n

@[expose] noncomputable def pushK (x y : Nat) (R : List (Nat × Nat)) (k : List (Nat × Nat) → Bool) :
    Bool :=
  strictB x fun a => strictB y fun b => k (List.cons (Prod.mk a b) R)

@[expose] noncomputable def stepK (c rm one : Nat) (ins : Nat × Nat × Nat) (R : List (Nat × Nat))
    (L : Nat) (k : List (Nat × Nat) → Bool) : Bool :=
  Prod.rec (motive := fun _ => Bool) (fun t ab => Prod.rec (motive := fun _ => Bool) (fun i j =>
    Bool.rec (motive := fun _ => Bool)
      (Bool.rec (motive := fun _ => Bool)
        (pushK (powJ c rm one (regP one R L i).1 j) (powJ c rm one (regP one R L i).2 j) R k)
        (pushK (regP one R L i).2 (regP one R L i).1 R k)
        (Nat.beq t (nat_lit 1)))
      (strictB (regP one R L i).1 fun x => strictB (regP one R L i).2 fun xi =>
        strictB (regP one R L j).1 fun y => strictB (regP one R L j).2 fun yi =>
          pushK (mulJ c rm x y) (mulJ c rm yi xi) R k)
      (Nat.beq t (nat_lit 0))) ab) ins

@[expose] noncomputable def runK (c rm one : Nat) (fin : List (Nat × Nat) → Nat → Bool)
    (prog : List (Nat × Nat × Nat)) : List (Nat × Nat) → Nat → Bool :=
  List.rec (motive := fun _ => List (Nat × Nat) → Nat → Bool) (fun R L => fin R L)
    (fun ins _ ih R L => stepK c rm one ins R L fun R' => ih R' (Nat.succ L)) prog

@[expose] noncomputable def gensK (one : Nat) (R : List (Nat × Nat)) (L : Nat) (rs : List Nat)
    (k : List Nat → Bool) : Bool :=
  List.rec (motive := fun _ => (List Nat → Bool) → Bool) (fun k => k List.nil)
    (fun r _ ih k => strictB (regP one R L r).1 fun v => ih fun l => k (List.cons v l)) rs k

@[expose] noncomputable def bfsGo (c rm one : Nat) (G : List Nat) (bfs : List (Nat × Nat))
    (k : List Nat → Bool) : List Nat → Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Nat → Bool) (fun acc _ => k acc)
    (fun pg _ ih acc L => Prod.rec (motive := fun _ => Bool) (fun pa ge =>
      strictB (mulJ c rm (getN one acc (Nat.sub (Nat.sub L (nat_lit 1)) pa)) (getN one G ge))
        fun v => ih (List.cons v acc) (Nat.succ L)) pg) bfs

@[expose] noncomputable def invK (c rm one Z Zi e : Nat) : Bool :=
  orB (Nat.beq e one) (orB (neN (mulJ c rm e e) one)
    (strictB (mulJ c rm (mulJ c rm Z e) Zi) fun f => neN (mulJ c rm e f) (mulJ c rm f e)))

@[expose] noncomputable def elK (c rm one Z Zi U N : Nat) (E : List Nat) : Bool :=
  andB (allR (fun e => Nat.beq (mulJ c rm e U) (mulJ c rm U e)) E)
    (andB (distinctK E) (andB (allR (invK c rm one Z Zi) E) (Nat.beq (lenR E) N)))

@[expose] noncomputable def zuK (c rm one : Nat) (Us : List Nat) (p m n : Nat) (cols : List Nat)
    (Z U Ui : Nat) : Bool :=
  andB (Nat.beq (powJ c rm one Z p) one) (andB (neN Z one)
  (andB (Nat.beq (mulJ c rm (mulJ c rm U Z) Ui) (powJ c rm one Z m))
  (andB (Nat.beq (powJ c rm one U n) one)
  (andB (Nat.beq (powJ c rm one U (Nat.div n (nat_lit 2))) (etaK c rm one Us (nat_lit 1)))
    (allBelowR (nat_lit 11) fun j =>
      Nat.beq (mulJ c rm (mulJ c rm U (getN one Us j)) Ui) (etaK c rm one Us (getN (nat_lit 0) cols j)))))))

@[expose] noncomputable def finK (c rm one : Nat) (Us : List Nat) (p m n rz ru : Nat)
    (gens cols : List Nat) (bfs : List (Nat × Nat)) (N : Nat) (R : List (Nat × Nat)) (L : Nat) :
    Bool :=
  strictB (regP one R L rz).1 fun Z => strictB (regP one R L rz).2 fun Zi =>
  strictB (regP one R L ru).1 fun U => strictB (regP one R L ru).2 fun Ui =>
    andB (zuK c rm one Us p m n cols Z U Ui)
      (gensK one R L gens fun G =>
        bfsGo c rm one G bfs (elK c rm one Z Zi U N) (List.cons one List.nil) (nat_lit 1))

@[expose] noncomputable def rowChkK (c rm one : Nat) (Us : List Nat) (A Ai B Bi : Nat)
    (prog : List (Nat × Nat × Nat)) (p m n rz ru : Nat) (gens cols : List Nat)
    (bfs : List (Nat × Nat)) (N : Nat) : Bool :=
  runK c rm one (finK c rm one Us p m n rz ru gens cols bfs N) prog
    (List.cons (Prod.mk B Bi) (List.cons (Prod.mk A Ai) (List.cons (Prod.mk one one) List.nil)))
    (nat_lit 3)

@[expose] noncomputable def rowsXorK (cols : List Nat) (c : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun j acc => Bool.rec (motive := fun _ => Nat) acc (Nat.xor acc (getN (nat_lit 0) cols j))
      (bitB c j)) (nat_lit 11)

@[expose] noncomputable def maskChkK (cols pi : List Nat) (S : List (List Nat)) : Bool :=
  andB (allR (fun c => Nat.blt c (nat_lit 2048)) cols)
  (andB (allBelowR (nat_lit 24) fun i =>
      allR (fun c => memR (rowsXorK cols c) (getLR S (getN (nat_lit 0) pi i))) (getLR S i))
  (andB (allBelowR (nat_lit 24) fun i =>
      orB (notB (memR (nat_lit 1) (getLR S i))) (orB (Nat.beq i (nat_lit 4)) (Nat.beq i (nat_lit 11))))
  (andB (memR (nat_lit 1) (getLR S (nat_lit 4))) (memR (nat_lit 1) (getLR S (nat_lit 11))))))

@[expose] noncomputable def ceCntK (cols : List Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun c acc => Bool.rec (motive := fun _ => Nat) acc (Nat.succ acc)
      (Nat.beq (rowsXorK cols c) c)) (nat_lit 2048)

end CFSG.KC.J4Row

end
