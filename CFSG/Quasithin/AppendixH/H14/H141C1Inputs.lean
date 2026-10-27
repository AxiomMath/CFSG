module

public import CFSG.Quasithin.AppendixH.H14.H141Tabs
public import CFSG.Quasithin.Background.HMathieuSyl24Base

public section

namespace CFSG.Quasithin.AppendixH.H14

open CFSG.Quasithin.H.Mathieu CFSG.QuasithinUnique.Setup.X1

@[expose] def inTab64 (tab : Array (Array ℕ)) (b : Array ℕ) : Bool :=
  (List.range 64).any fun m => tab[m]! == b

@[expose] def c1Comp (a b : Array ℕ) : Array ℕ := Array.ofFn fun i : Fin 24 => a[b[(i : ℕ)]!]!

@[expose] def c1Conj (a t : Array ℕ) : Array ℕ := c1Comp (c1Comp a t) (invArr a)

@[expose] def c1Fuse : List (Array ℕ × Bool) :=
  [(#[0, 9, 6, 18, 20, 13, 12, 14, 5, 2, 8, 19, 16, 3, 7, 11, 21, 15, 22, 23, 10, 1, 17, 4], true),
    (#[0, 9, 12, 17, 11, 8, 6, 23, 15, 21, 14, 4, 16, 5, 22, 18, 2, 10, 19, 13, 3, 1, 20, 7], true),
    (#[3, 4, 17, 15, 22, 14, 13, 11, 0, 20, 10, 2, 5, 12, 1, 18, 8, 16, 21, 19, 6, 7, 23, 9], false),
    (#[3, 4, 23, 8, 20, 22, 18, 15, 0, 14, 17, 1, 5, 12, 6, 19, 11, 9, 16, 13, 2, 7, 10, 21], false)]

@[expose] def predC1 (l : List T24s2.Elem) : Bool :=
  decide (l.length ≤ 6) &&
    (decide (l.length < 5) ||
      (subprods l).all (fun x => inTab64 tabS (T24s2.arr x)) ||
      (subprods l).all (fun x => inTab64 tabT (T24s2.arr x)) ||
      (l.length == 5 && c1Fuse.any fun cs => (subprods l).all fun x =>
        inTab64 (if cs.2 then tabS else tabT) (c1Conj cs.1 (T24s2.arr x))))

end CFSG.Quasithin.AppendixH.H14
