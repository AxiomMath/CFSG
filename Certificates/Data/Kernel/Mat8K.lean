module

public import CFSG.Quasithin.H13.L32NMat8Inputs
public import Mathlib

public section

namespace CFSG.KC.Mat8K

open CFSG.Quasithin.H13.Mat8Cert

@[expose] def mv8K (A : List ℕ) (v : ℕ) : ℕ :=
  match A with
  | a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: _ =>
    a0 * (v &&& 1) ^^^ a1 * ((v >>> 1) &&& 1) ^^^ a2 * ((v >>> 2) &&& 1) ^^^
      a3 * ((v >>> 3) &&& 1) ^^^ a4 * ((v >>> 4) &&& 1) ^^^ a5 * ((v >>> 5) &&& 1) ^^^
      a6 * ((v >>> 6) &&& 1) ^^^ a7 * ((v >>> 7) &&& 1)
  | _ => mv8 A v

@[expose] def mul8K (A B : List ℕ) : List ℕ := B.map (mv8K A)

@[expose] def evalWK (gens : List (List ℕ)) (w : List ℕ) : List ℕ :=
  w.foldr (fun i acc => mul8K (gens.getD i one8) acc) one8

inductive BT (α : Type) where
  | tip (xs : List α)
  | node (l r : BT α)

@[expose] def BT.mem {α : Type} [BEq α] : ℕ → ℕ → BT α → α → Bool
  | _, _, .tip xs, y => xs.contains y
  | 0, _, .node _ _, _ => false
  | d + 1, k, .node l r, y => if k % 2 == 0 then BT.mem d (k / 2) l y else BT.mem d (k / 2) r y

@[expose] def BT.ins {α : Type} : ℕ → ℕ → BT α → α → BT α
  | 0, _, .tip xs, x => .tip (x :: xs)
  | 0, _, .node _ _, x => .tip [x]
  | d + 1, k, .tip xs, x =>
    if k % 2 == 0 then .node (BT.ins d (k / 2) (.tip xs) x) (.tip xs)
    else .node (.tip xs) (BT.ins d (k / 2) (.tip xs) x)
  | d + 1, k, .node l r, x =>
    if k % 2 == 0 then .node (BT.ins d (k / 2) l x) r else .node l (BT.ins d (k / 2) r x)

@[expose] def keyL (x : List ℕ) : ℕ := code64 x % 65521

@[expose] def memL (t : BT (List ℕ)) (y : List ℕ) : Bool := BT.mem 16 (keyL y) t y

@[expose] def insL (t : BT (List ℕ)) (x : List ℕ) : BT (List ℕ) := BT.ins 16 (keyL x) t x

@[expose] def ofListL (L : List (List ℕ)) : BT (List ℕ) := L.foldl insL (.tip [])

@[expose] def memN (t : BT ℕ) (y : ℕ) : Bool := BT.mem 16 (y % 65521) t y

@[expose] def insN (t : BT ℕ) (x : ℕ) : BT ℕ := BT.ins 16 (x % 65521) t x

@[expose] def nodupNAux : BT ℕ → List ℕ → Bool
  | _, [] => true
  | t, x :: l => !(memN t x) && nodupNAux (insN t x) l

@[expose] def nodupNT (l : List ℕ) : Bool := nodupNAux (.tip []) l

@[expose] def bfsWT (gens : List (List ℕ)) (cap : ℕ) :
    ℕ → BT (List ℕ) → List (List ℕ × List ℕ) → List (List ℕ × List ℕ) →
      List (List ℕ × List ℕ)
  | 0, _, acc, _ => acc
  | fuel + 1, seen, acc, fr =>
    match fr with
    | [] => acc
    | _ =>
      if cap ≤ acc.length then acc else
      let st := fr.foldl
        (fun (st : BT (List ℕ) × List (List ℕ × List ℕ) × List (List ℕ × List ℕ)) wx =>
          (List.range gens.length).foldl
            (fun (st : BT (List ℕ) × List (List ℕ × List ℕ) × List (List ℕ × List ℕ)) i =>
              let y := mul8K (gens.getD i one8) wx.2
              if memL st.1 y then st
              else (insL st.1 y, (i :: wx.1, y) :: st.2.1, (i :: wx.1, y) :: st.2.2)) st)
        (seen, acc, [])
      bfsWT gens cap fuel st.1 st.2.1 st.2.2

@[expose] def elemsOfT (gens : List (List ℕ)) (cap : ℕ := 100000) : List (List ℕ) :=
  (bfsWT gens cap 200 (insL (.tip []) one8) [([], one8)] [([], one8)]).map Prod.snd

end CFSG.KC.Mat8K

end
