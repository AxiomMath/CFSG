module

public import CFSG.Quasithin.Background.HF22UInputs

public section

namespace CFSG.Quasithin.H13.Mat

open CFSG.Quasithin.H.Mathieu CFSG.QuasithinUnique.Setup.X1

@[expose] def r2B9 : List ℕ := [707, 369, 254, 68, 60, 19, 14, 3, 1]

@[expose] def r2W8 : List ℕ := [513, 279, 149, 118, 49, 16, 13, 3]

@[expose] def chainCommIn (B : List ℕ) (s : T22s2.Elem) : Bool :=
  (List.range 10).all fun j => (combos B).contains (codeAct22 s (2 ^ j) ^^^ 2 ^ j)

@[expose] def predMB22 (l : List T22s2.Elem) : Bool :=
  predU22 l &&
    (l.length != 5 || (l.all (chainCommIn r2B9) && l.any (fun s => !(chainCommIn r2W8 s))))

end CFSG.Quasithin.H13.Mat
