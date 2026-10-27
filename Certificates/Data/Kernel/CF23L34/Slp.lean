module

public import Certificates.Data.Kernel.Spor.Chain

public section

namespace CFSG.KC.CF23L34

open CFSG.KC.Enum CFSG.KS

@[expose] def frz : List Int → List Int
  | [] => []
  | z :: w =>
    match frz w with
    | [] => [z]
    | y :: u => if y = -z then u else z :: y :: u

@[expose] def slpX (prog : List (Int × Int)) (keep : List Nat) : Nat → Int → List Int
  | 0, z => [z]
  | f + 1, z =>
    if z = 0 then []
    else if z.natAbs ≤ 2 ∨ z.natAbs ∈ keep then [z]
    else
      if 0 < z then
        slpX prog keep f (prog.getD (z.natAbs - 3) (0, 0)).1 ++
          slpX prog keep f (prog.getD (z.natAbs - 3) (0, 0)).2
      else
        ((slpX prog keep f (prog.getD (z.natAbs - 3) (0, 0)).1 ++
          slpX prog keep f (prog.getD (z.natAbs - 3) (0, 0)).2).reverse.map Neg.neg)

@[expose] def slpR (prog : List (Int × Int)) (keep : List Nat) (f r : Nat) : List Int :=
  frz (slpX prog keep f (prog.getD (r - 3) (0, 0)).1 ++ slpX prog keep f (prog.getD (r - 3) (0, 0)).2)

@[expose] noncomputable def wzK {α : Type} (n w : Nat) (T : Nat → Nat) (c : α → Nat) (L : List α) :
    Nat :=
  List.rec (motive := fun _ => Nat) (pidn n w)
    (fun a _ acc => strictN acc (fun r => pcomp n w (mask w) (T (c a)) r)) L

@[expose] noncomputable def tzK {α : Type} (w : Nat) (T : Nat → Nat) (c : α → Nat) (L : List α) :
    Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun x => x)
    (fun a _ ih x => strictN (ih x) (fun y => pg w (mask w) (T (c a)) y)) L

end CFSG.KC.CF23L34

end
