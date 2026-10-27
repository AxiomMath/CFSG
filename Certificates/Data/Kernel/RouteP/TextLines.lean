module

public section

namespace CFSG.KC.RouteP

abbrev NLL := List (List Nat) × List Nat × Nat × Bool × Bool × Bool

@[expose] def nlStepL (s : NLL) (n : Nat) : NLL :=
  if s.2.2.2.2.1 = true then
    if n = 10 then (s.1, s.2.1, s.2.2.1, s.2.2.2.1, false, true) else s
  else if s.2.2.2.2.2 = true ∧ n = 35 then (s.1, s.2.1, s.2.2.1, s.2.2.2.1, true, s.2.2.2.2.2)
  else if 48 ≤ n ∧ n ≤ 57 then (s.1, s.2.1, s.2.2.1 * 10 + (n - 48), true, s.2.2.2.2.1, false)
  else if s.2.2.2.1 = true then
    if n = 10 then ((s.2.2.1 :: s.2.1).reverse :: s.1, [], 0, false, s.2.2.2.2.1, true)
    else (s.1, s.2.2.1 :: s.2.1, 0, false, s.2.2.2.2.1, false)
  else if n = 10 then
    if s.2.1 ≠ [] then (s.2.1.reverse :: s.1, [], s.2.2.1, s.2.2.2.1, s.2.2.2.2.1, true)
    else (s.1, s.2.1, s.2.2.1, s.2.2.2.1, s.2.2.2.2.1, true)
  else (s.1, s.2.1, s.2.2.1, s.2.2.2.1, s.2.2.2.2.1, false)

@[expose] def nlFinL (s : NLL) : List (List Nat) :=
  if s.2.2.2.1 = true then ((s.2.2.1 :: s.2.1).reverse :: s.1).reverse
  else if s.2.1 ≠ [] then (s.2.1.reverse :: s.1).reverse else s.1.reverse

@[expose] def nlInitL : NLL := ([], [], 0, false, false, true)

@[expose] def nlLines (ns : List Nat) : List (List Nat) := nlFinL (ns.foldl nlStepL nlInitL)

@[expose] noncomputable def forceN {β : Type} (n : Nat) (k : Nat → β) : β :=
  Nat.rec (motive := fun _ => β) (k 0) (fun m _ => k (Nat.succ m)) n

@[expose] noncomputable def bif' (c t e : Bool) : Bool := Bool.rec (motive := fun _ => Bool) e t c

@[expose] noncomputable def nlChk (E : Nat → Nat → Nat) (lens : Nat → Nat) (ns : List Nat) :
    Nat → Nat → Nat → Nat → Nat → Nat → (Nat → Nat → Nat → Nat → Nat → Nat → Bool) → Bool :=
  List.rec (motive := fun _ =>
      Nat → Nat → Nat → Nat → Nat → Nat → (Nat → Nat → Nat → Nat → Nat → Nat → Bool) → Bool)
    (fun L P num iN cm sa fin => fin L P num iN cm sa)
    (fun n _ ih L P num iN cm sa fin =>
      bif' (Nat.blt n 128)
        (bif' (Nat.beq cm 1)
          (bif' (Nat.beq n 10) (ih L P num iN 0 1 fin) (ih L P num iN cm sa fin))
          (bif' (and (Nat.beq sa 1) (Nat.beq n 35)) (ih L P num iN 1 sa fin)
            (bif' (and (Nat.ble 48 n) (Nat.ble n 57))
              (forceN (Nat.add (Nat.mul num 10) (Nat.sub n 48)) fun m => ih L P m 1 cm 0 fin)
              (bif' (Nat.beq iN 1)
                (bif' (Nat.beq (E L P) num)
                  (forceN (Nat.succ P) fun P' =>
                    bif' (Nat.beq n 10)
                      (bif' (Nat.beq P' (lens L))
                        (forceN (Nat.succ L) fun L' => ih L' 0 0 0 cm 1 fin) false)
                      (ih L P' 0 0 cm 0 fin))
                  false)
                (bif' (Nat.beq n 10)
                  (bif' (Nat.beq P 0) (ih L 0 num 0 cm 1 fin)
                    (bif' (Nat.beq P (lens L))
                      (forceN (Nat.succ L) fun L' => ih L' 0 num 0 cm 1 fin) false))
                  (ih L P num 0 cm 0 fin))))))
        false)
    ns

@[expose] noncomputable def nlEnd (nl : Nat) (L P _num iN _cm _at : Nat) : Bool :=
  and (Nat.beq L nl) (and (Nat.beq P 0) (Bool.not (Nat.beq iN 1)))

@[expose] noncomputable def nlAt (L' P' num' iN' cm' sa' : Nat) (L P num iN cm sa : Nat) : Bool :=
  and (Nat.beq L L') (and (Nat.beq P P') (and (Nat.beq num num')
    (and (Nat.beq iN iN') (and (Nat.beq cm cm') (Nat.beq sa sa')))))

end CFSG.KC.RouteP
