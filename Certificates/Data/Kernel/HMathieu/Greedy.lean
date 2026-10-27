module

public import CFSG.Certificates.Kernel.Common.Loop

public section

namespace CFSG.KC.HMathieu

@[expose] def mkF (mkR : Nat → Nat) (m i j : Nat) : Nat :=
  if i = m then j else if j = m then i else Nat.land (Nat.shiftRight (mkR i) (8 * j)) 255

@[expose] def startK : List Nat → Nat
  | [] => 0
  | a :: _ => a + 1

@[expose] def extK (m : Nat) (mkR : Nat → Nat) (l S : List Nat) (c : Nat) : List Nat :=
  (List.range' (startK l) (m - startK l)).filter fun x =>
    c.testBit x && !(S.contains x) && S.all fun s => s == m || decide (x < mkF mkR m x s)

@[expose] def gAllS {σ : Type} (m : Nat) (cmR mkR : Nat → Nat) (upd : σ → Nat → σ)
    (pred : List Nat → List Nat → σ → Bool) : Nat → List Nat → List Nat → Nat → σ → Bool
  | 0, l, S, _, st => pred l S st
  | k + 1, l, S, c, st =>
    pred l S st && (extK m mkR l S c).all fun x =>
      gAllS m cmR mkR upd pred k (x :: l) (S ++ S.map (mkF mkR m x)) (Nat.land c (cmR x))
        (upd st x)

@[expose] noncomputable def lAllR (S : List Nat) (f : Nat → Bool) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun s _ ih => bAnd(f s, ih)) S

@[expose] noncomputable def appMapR (S T : List Nat) (g : Nat → Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat)
    (List.rec (motive := fun _ => List Nat) [] (fun t _ ih => g t :: ih) T)
    (fun s _ ih => s :: ih) S

@[expose] noncomputable def candR (m c x r : Nat) (S : List Nat) : Bool :=
  bAnd(Nat.beq (Nat.land (Nat.shiftRight c x) 1) 1,
    lAllR S fun s => bIf(Nat.beq s x, false,
      bIf(Nat.beq s m, true, Nat.blt x (Nat.land (Nat.shiftRight r (Nat.mul 8 s)) 255))))

@[expose] noncomputable def gAllR {σ : Type} (m : Nat) (upd : σ → Nat → σ)
    (pred : List Nat → List Nat → σ → Bool) :
    Nat → List Nat → List Nat → Nat → σ → List (Nat × Nat) → Nat → Bool :=
  Nat.rec (motive := fun _ => List Nat → List Nat → Nat → σ → List (Nat × Nat) → Nat → Bool)
    (fun l S _ st _ _ => pred l S st)
    (fun _ ih l S c st rs x => bAnd(pred l S st,
      List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
        (fun r rest ihs y => bAnd(bIf(candR m c y r.2 S,
            ih (y :: l) (appMapR S S fun s => nIf(Nat.beq s m, y,
              Nat.land (Nat.shiftRight r.2 (Nat.mul 8 s)) 255)) (Nat.land c r.1) (upd st y) rest
              (Nat.succ y),
            true), ihs (Nat.succ y)))
        rs x))

@[expose] def cmD (D : List (Nat × Nat)) (y : Nat) : Nat := (D.getD y (0, 0)).1

@[expose] def mkD (D : List (Nat × Nat)) (y : Nat) : Nat := (D.getD y (0, 0)).2

end CFSG.KC.HMathieu

end
