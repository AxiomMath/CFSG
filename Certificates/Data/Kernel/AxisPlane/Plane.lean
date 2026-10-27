module

public import CFSG.Certificates.Kernel.Common.Loop

public section

namespace CFSG.KC.AxisPlane

@[expose] noncomputable def wW : Nat := nat_lit 16777216

@[expose] noncomputable def onesW : Nat := Nat.sub (Nat.shiftLeft (nat_lit 1) wW) (nat_lit 1)

@[expose] noncomputable def allK : Nat := Nat.shiftLeft onesW (nat_lit 64)

@[expose] noncomputable def saltK (k : Nat) : Nat :=
  Nat.land (Nat.mul (Nat.add k (nat_lit 1)) (nat_lit 11400714819323198485))
    (nat_lit 18446744073709551615)

@[expose] noncomputable def repW (w : Nat) : Nat :=
  Nat.div onesW (Nat.sub (Nat.shiftLeft (nat_lit 1) w) (nat_lit 1))

@[expose] noncomputable def bitW (j : Nat) : Nat :=
  Nat.mul (Nat.shiftLeft (Nat.sub (Nat.shiftLeft (nat_lit 1) (Nat.shiftLeft (nat_lit 1) j))
      (nat_lit 1)) (Nat.shiftLeft (nat_lit 1) j))
    (repW (Nat.shiftLeft (nat_lit 1) (Nat.add j (nat_lit 1))))

@[expose] noncomputable def bitK (j : Nat) : Nat :=
  Nat.lor (Nat.shiftLeft (bitW j) (nat_lit 64)) (saltK j)

@[expose] noncomputable def parK (l : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (saltK (nat_lit 64))
    (fun j acc => nIf(Nat.beq (Nat.land (Nat.shiftRight l j) (nat_lit 1)) (nat_lit 1),
      Nat.xor acc (bitK j), acc)) (nat_lit 24)

@[expose] noncomputable def tmaskK (t l : Nat) : Nat := Nat.land (parK l) (Nat.xor allK (bitK t))

@[expose] noncomputable def swK (d m S : Nat) : Nat :=
  (fun u => Nat.xor (Nat.xor S u) (Nat.shiftLeft (Nat.shiftRight u (nat_lit 64))
      (Nat.add (nat_lit 64) d)))
    (Nat.land (Nat.xor (Nat.shiftRight S d) S) m)

@[expose] noncomputable def tvK (c S : Nat) : Nat :=
  swK (Nat.shiftLeft (nat_lit 1) (Nat.land c (nat_lit 31)))
    (tmaskK (Nat.land c (nat_lit 31)) (Nat.shiftRight c (nat_lit 5))) S

@[expose] noncomputable def applyK (ops : List Nat) (S : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun S => S) (fun c _ ih S => ih (tvK c S)) ops S

@[expose] noncomputable def par24 (n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun j acc => Nat.xor acc (Nat.land (Nat.shiftRight n j) (nat_lit 1))) (nat_lit 24)

@[expose] noncomputable def tvV (c v : Nat) : Nat :=
  Nat.xor v (Nat.shiftLeft (par24 (Nat.land (Nat.shiftRight c (nat_lit 5)) v)) (Nat.land c (nat_lit 31)))

@[expose] noncomputable def vecOps (ops : List Nat) (v : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun v => v) (fun c _ ih v => ih (tvV c v)) ops v

@[expose] noncomputable def opValid (c : Nat) : Bool :=
  bAnd(Nat.blt (Nat.land c (nat_lit 31)) (nat_lit 24),
    bAnd(Nat.blt (Nat.shiftRight c (nat_lit 5)) (nat_lit 16777216),
      Nat.beq (Nat.land (Nat.shiftRight (Nat.shiftRight c (nat_lit 5)) (Nat.land c (nat_lit 31)))
        (nat_lit 1)) (nat_lit 0)))

@[expose] noncomputable def opsValid (ops : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun c _ ih => bAnd(opValid c, ih)) ops

@[expose] noncomputable def rowsGo (ops : List Nat) (rows : List Nat) (j : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun j => Nat.beq j (nat_lit 24))
    (fun r _ ih j => bAnd(Nat.beq (vecOps ops (Nat.shiftLeft (nat_lit 1) j)) r, ih (Nat.succ j)))
    rows j

@[expose] noncomputable def opsOK (ops rows : List Nat) : Bool :=
  bAnd(opsValid ops, rowsGo ops rows (nat_lit 0))

@[expose] noncomputable def codeK (Ps : List Nat) (c : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun c => Nat.lor allK (saltK (Nat.add c (nat_lit 128))))
    (fun P _ ih c => Nat.land (nIf(Nat.beq (Nat.land c (nat_lit 1)) (nat_lit 1), P,
      Nat.xor allK P)) (ih (Nat.shiftRight c (nat_lit 1)))) Ps c

@[expose] noncomputable def bitAt (P x : Nat) : Nat :=
  Nat.land (Nat.shiftRight P (Nat.add (nat_lit 64) x)) (nat_lit 1)

@[expose] noncomputable def codeAt (Ps : List Nat) (x : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun P _ ih => Nat.add (bitAt P x) (Nat.shiftLeft ih (nat_lit 1))) Ps

@[expose] noncomputable def subK (X Y : Nat) : Bool :=
  Nat.beq (Nat.land (Nat.land X (Nat.xor allK Y)) allK) (nat_lit 0)

@[expose] noncomputable def invK (ops : List Nat) (P : Nat) : Bool :=
  Nat.beq (Nat.land (Nat.xor (applyK ops P) P) allK) (nat_lit 0)

@[expose] noncomputable def imgEqK (ops : List Nat) (P R : Nat) : Bool :=
  Nat.beq (Nat.land (Nat.xor (applyK ops P) R) allK) (nat_lit 0)

@[expose] noncomputable def incK (Qs Rs : List Nat) (C : Nat) : Nat :=
  List.rec (motive := fun _ => List Nat → Nat → Nat) (fun _ C => Nat.xor allK C)
    (fun Q _ ih Rs C => List.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun R Rs' _ => Nat.land (Nat.xor allK (Nat.xor Q (Nat.xor R C))) (ih Rs' (Nat.land R C)))
      Rs) Qs Rs C

@[expose] noncomputable def anyK (Ps : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun P _ ih => Nat.lor P ih) Ps

@[expose] noncomputable def predK (Qs : List Nat) (Rss : List (List Nat)) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun Rs _ ih => Nat.lor (incK Qs Rs allK) ih) Rss

@[expose] noncomputable def genK (Qs : List Nat) (Rss : List (List Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun _ Qt _ => subK (anyK Qt) (predK Qs Rss)) Qs

@[expose] noncomputable def covK (Ls Qs : List Nat) : Bool := subK (anyK Ls) (anyK Qs)

@[expose] noncomputable def seedsGo (Ls Qs : List Nat) (lams : List Nat) (r₀ : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun x _ ih r => bAnd(Nat.blt x (nat_lit 16777216), bAnd(Nat.beq (codeAt Ls x) (Nat.succ r),
      bAnd(Nat.beq (codeAt Qs x) (nat_lit 1), ih (Nat.succ r))))) lams r₀

@[expose] noncomputable def seedsK (Ls Qs lams : List Nat) : Bool := seedsGo Ls Qs lams (nat_lit 0)

@[expose] noncomputable def seedPl (lams : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun x _ ih => Nat.lor (Nat.shiftLeft (nat_lit 1) (Nat.add (nat_lit 64) x)) ih) lams

@[expose] noncomputable def d0K (Qs lams : List Nat) : Bool := subK (codeK Qs (nat_lit 1)) (seedPl lams)

@[expose] noncomputable def popM (s : Nat) : Nat :=
  Nat.mul (Nat.sub (Nat.shiftLeft (nat_lit 1) (Nat.shiftLeft (nat_lit 1) s)) (nat_lit 1))
    (repW (Nat.shiftLeft (nat_lit 1) (Nat.add s (nat_lit 1))))

@[expose] noncomputable def popStep (s y : Nat) : Nat :=
  Nat.add (Nat.land y (popM s)) (Nat.land (Nat.shiftRight y (Nat.shiftLeft (nat_lit 1) s)) (popM s))

@[expose] noncomputable def popK (x : Nat) : Nat :=
  Nat.mod (Nat.rec (motive := fun _ => Nat) (Nat.land x onesW) (fun s ih => popStep s ih) (nat_lit 5))
    (nat_lit 4294967295)

@[expose] noncomputable def cntK (Ls : List Nat) (c k : Nat) : Bool :=
  Nat.beq (popK (Nat.shiftRight (codeK Ls c) (nat_lit 64))) k

end CFSG.KC.AxisPlane

end
