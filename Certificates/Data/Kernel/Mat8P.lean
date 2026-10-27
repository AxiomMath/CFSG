module

public import CFSG.Quasithin.H13.L32NMat8Inputs
public import Mathlib

public section

namespace CFSG.KC.Mat8P

open CFSG.Quasithin.H13.Mat8Cert

@[expose] def mulP (X Y : ℕ) : ℕ :=
  Nat.xor (Nat.mul (Nat.land Y (nat_lit 72340172838076673)) (Nat.land X (nat_lit 255))) (Nat.xor
  (Nat.mul (Nat.land (Nat.shiftRight Y (nat_lit 1)) (nat_lit 72340172838076673))
    (Nat.land (Nat.shiftRight X (nat_lit 8)) (nat_lit 255))) (Nat.xor
  (Nat.mul (Nat.land (Nat.shiftRight Y (nat_lit 2)) (nat_lit 72340172838076673))
    (Nat.land (Nat.shiftRight X (nat_lit 16)) (nat_lit 255))) (Nat.xor
  (Nat.mul (Nat.land (Nat.shiftRight Y (nat_lit 3)) (nat_lit 72340172838076673))
    (Nat.land (Nat.shiftRight X (nat_lit 24)) (nat_lit 255))) (Nat.xor
  (Nat.mul (Nat.land (Nat.shiftRight Y (nat_lit 4)) (nat_lit 72340172838076673))
    (Nat.land (Nat.shiftRight X (nat_lit 32)) (nat_lit 255))) (Nat.xor
  (Nat.mul (Nat.land (Nat.shiftRight Y (nat_lit 5)) (nat_lit 72340172838076673))
    (Nat.land (Nat.shiftRight X (nat_lit 40)) (nat_lit 255))) (Nat.xor
  (Nat.mul (Nat.land (Nat.shiftRight Y (nat_lit 6)) (nat_lit 72340172838076673))
    (Nat.land (Nat.shiftRight X (nat_lit 48)) (nat_lit 255)))
  (Nat.mul (Nat.land (Nat.shiftRight Y (nat_lit 7)) (nat_lit 72340172838076673))
    (Nat.land (Nat.shiftRight X (nat_lit 56)) (nat_lit 255)))))))))

@[expose] def unpackM (X : ℕ) : List ℕ :=
  [Nat.land X (nat_lit 255), Nat.land (Nat.shiftRight X (nat_lit 8)) (nat_lit 255),
    Nat.land (Nat.shiftRight X (nat_lit 16)) (nat_lit 255),
    Nat.land (Nat.shiftRight X (nat_lit 24)) (nat_lit 255),
    Nat.land (Nat.shiftRight X (nat_lit 32)) (nat_lit 255),
    Nat.land (Nat.shiftRight X (nat_lit 40)) (nat_lit 255),
    Nat.land (Nat.shiftRight X (nat_lit 48)) (nat_lit 255),
    Nat.land (Nat.shiftRight X (nat_lit 56)) (nat_lit 255)]

@[expose] def code64R (x : List ℕ) : ℕ :=
  x.foldr (fun c acc => Nat.add c (Nat.mul (nat_lit 256) acc)) (nat_lit 0)

@[expose] def oneP : ℕ := nat_lit 9241421688590303745

@[expose] def mv8R (A : List ℕ) (v : ℕ) : ℕ :=
  match A with
  | a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: _ =>
    Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor (Nat.xor
      (Nat.mul a0 (Nat.land v (nat_lit 1)))
      (Nat.mul a1 (Nat.land (Nat.shiftRight v (nat_lit 1)) (nat_lit 1))))
      (Nat.mul a2 (Nat.land (Nat.shiftRight v (nat_lit 2)) (nat_lit 1))))
      (Nat.mul a3 (Nat.land (Nat.shiftRight v (nat_lit 3)) (nat_lit 1))))
      (Nat.mul a4 (Nat.land (Nat.shiftRight v (nat_lit 4)) (nat_lit 1))))
      (Nat.mul a5 (Nat.land (Nat.shiftRight v (nat_lit 5)) (nat_lit 1))))
      (Nat.mul a6 (Nat.land (Nat.shiftRight v (nat_lit 6)) (nat_lit 1))))
      (Nat.mul a7 (Nat.land (Nat.shiftRight v (nat_lit 7)) (nat_lit 1)))
  | _ => mv8 A v

inductive NT (α : Type) where
  | tip (xs : List α)
  | node (l r : NT α)

@[expose] def ntMem {α : Type} [BEq α] (d : ℕ) : ℕ → NT α → α → Bool :=
  Nat.rec (motive := fun _ => ℕ → NT α → α → Bool)
    (fun _ t y => NT.casesOn (motive := fun _ => Bool) t (fun xs => xs.elem y) (fun _ _ => false))
    (fun _ ih k t y => NT.casesOn (motive := fun _ => Bool) t (fun xs => xs.elem y)
      (fun l r => Bool.rec (ih (Nat.shiftRight k (nat_lit 1)) r y)
        (ih (Nat.shiftRight k (nat_lit 1)) l y) (Nat.beq (Nat.land k (nat_lit 1)) (nat_lit 0)))) d

@[expose] def ntIns {α : Type} (d : ℕ) : ℕ → NT α → α → NT α :=
  Nat.rec (motive := fun _ => ℕ → NT α → α → NT α)
    (fun _ t x => NT.casesOn (motive := fun _ => NT α) t (fun xs => .tip (x :: xs))
      (fun _ _ => .tip [x]))
    (fun _ ih k t x => NT.casesOn (motive := fun _ => NT α) t
      (fun xs => Bool.rec (.node (.tip xs) (ih (Nat.shiftRight k (nat_lit 1)) (.tip xs) x))
        (.node (ih (Nat.shiftRight k (nat_lit 1)) (.tip xs) x) (.tip xs))
        (Nat.beq (Nat.land k (nat_lit 1)) (nat_lit 0)))
      (fun l r => Bool.rec (.node l (ih (Nat.shiftRight k (nat_lit 1)) r x))
        (.node (ih (Nat.shiftRight k (nat_lit 1)) l x) r)
        (Nat.beq (Nat.land k (nat_lit 1)) (nat_lit 0)))) d

@[expose] def memP (t : NT ℕ) (y : ℕ) : Bool := ntMem (nat_lit 16) (Nat.mod y (nat_lit 65521)) t y

@[expose] def insP (t : NT ℕ) (y : ℕ) : NT ℕ := ntIns (nat_lit 16) (Nat.mod y (nat_lit 65521)) t y

@[expose] def ofListP (l : List ℕ) : NT ℕ := l.foldl insP (.tip [])

@[expose] def memLR (t : NT (List ℕ)) (y : List ℕ) : Bool :=
  ntMem (nat_lit 16) (Nat.mod (code64R y) (nat_lit 65521)) t y

@[expose] def insLR (t : NT (List ℕ)) (y : List ℕ) : NT (List ℕ) :=
  ntIns (nat_lit 16) (Nat.mod (code64R y) (nat_lit 65521)) t y

@[expose] def ofListLR (L : List (List ℕ)) : NT (List ℕ) := L.foldl insLR (.tip [])

@[expose] def nodupPAux : NT ℕ → List ℕ → Bool
  | _, [] => true
  | t, x :: l => !(memP t x) && nodupPAux (insP t x) l

@[expose] def nodupP (l : List ℕ) : Bool := nodupPAux (.tip []) l

@[expose] def bfsP (gens : List ℕ) (cap : ℕ) : ℕ → NT ℕ → List ℕ → List ℕ → List ℕ
  | 0, _, acc, _ => acc
  | fuel + 1, seen, acc, fr =>
    match fr with
    | [] => acc
    | _ =>
      if cap ≤ acc.length then acc else
      let st := fr.foldl (fun (st : NT ℕ × List ℕ × List ℕ) x =>
          (List.range gens.length).foldl (fun (st : NT ℕ × List ℕ × List ℕ) i =>
            let y := mulP (gens.getD i oneP) x
            if memP st.1 y then st else (insP st.1 y, y :: st.2.1, y :: st.2.2)) st)
        (seen, acc, [])
      bfsP gens cap fuel st.1 st.2.1 st.2.2

@[expose] def elemsP (gens : List ℕ) (cap : ℕ := 100000) : List ℕ :=
  bfsP gens cap 200 (insP (.tip []) oneP) [oneP] [oneP]

@[expose] def elemsF (gens : List (List ℕ)) (cap : ℕ := 100000) : List (List ℕ) :=
  if gens.all validB then (elemsP (gens.map code64R) cap).map unpackM else elemsOf gens cap

@[expose] def mul8F (A B : List ℕ) : List ℕ :=
  if validB A && validB B then unpackM (mulP (code64R A) (code64R B)) else B.map (mv8R A)

end CFSG.KC.Mat8P

end
