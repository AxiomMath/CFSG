module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TC2TableDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.E69Defs

public section

namespace CFSG.KC.TC2Outer

open CFSG.EvenSporadicStandard.Fin76b.TableX

@[expose] def outerCheck0 (n : ℕ) (inn : ℕ → Bool) (mul : ℕ → ℕ → ℕ) (tI : ℕ) : Bool :=
  let K0 := innList n inn
  let R := rootsIn n inn mul tI
  let E := eListX n inn mul tI
  let I := E.filter fun a => mul a a == 0 && a != 0
  decide (n = 256) && decide (tI < n) && inn 0 && inn tI && decide (20 ≤ R.length) &&
    K0.all (fun a => K0.all fun b => inn (mul a b)) &&
    (List.range n).all (fun a => (List.range n).any fun b => mul a b == 0) &&
    (List.range n).all (fun a => mul a tI == mul tI a) &&
    E.contains 0 && E.contains tI && R.all E.contains &&
    E.all (fun a => E.all fun b => E.contains (mul a b)) &&
    E.all (fun a => E.any fun b => mul a b == 0) &&
    E.all (fun a => a == 0 || R.contains a || R.any (fun x => R.any fun y => mul x y == a)) &&
    E.all (fun a => a == 0 || I.contains a || I.any (fun x => I.any fun y => mul x y == a)) &&
    (mul tI tI == 0 && tI != 0) &&
    E.any (fun a => E.any fun b => mul a b != mul b a) &&
    E.all (fun a => E.all fun b => mul a b == mul b a || mul a b == mul (mul b a) tI) &&
    E.all (fun y => (E.any fun f => mul f y != mul y f) || y == 0 || y == tI) &&
    (List.range n).all (fun s => ((List.range n).any fun x => mul x s != mul s x) || s == 0 ||
      s == tI) &&
    (List.range n).all (fun s => (E.any fun e => mul s e != mul e s) || s == 0 || s == tI) &&
    (List.range n).all (fun c => mul c c != 0 || c == 0 || c == tI ||
      decide (((List.range n).filter fun a => mul a a == c).length < 20)) &&
    (List.range n).all (fun a => inn a || mul a a != tI || decide (nbrCount n mul tI a < 19))

end CFSG.KC.TC2Outer
