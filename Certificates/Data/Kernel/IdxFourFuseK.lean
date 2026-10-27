module

public import Certificates.Data.Kernel.IdxFourSiftK

public section

namespace CFSG.KC.IF4F

open CFSG.KC.IF4C CFSG.KC.IF4R

@[expose] noncomputable def eltP (T O : List Nat) (q : Nat) : Nat :=
  mulP (look (nthD 0 T 0) (Nat.div q (nthD 0 O 1))) (look (nthD 0 T 1) (Nat.mod q (nthD 0 O 1)))

@[expose] noncomputable def conjOK (h s l : Nat) : Bool := Nat.beq (mulP h s) (mulP l h)

section
variable (T O ET EO : List Nat) (Q : Nat) (L : List Nat) (W : List (List Nat))

@[expose] noncomputable def fullOK (s : Nat) (w : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false
    (fun m t _ => List.rec (motive := fun _ => Bool) false
      (fun f as _ => Nat.blt f 4 && pathOK EO as && conjOK (mulP (pathP ET as) (look Q f)) s (subP L m))
      t) w

@[expose] noncomputable def recW (s : Nat) (w : List Nat) : Bool :=
  bif Nat.beq (nthD 0 w 0) 0 then fullOK ET EO Q L s (dropN 1 w)
  else Nat.beq (nthD 0 w 0) 1 && Nat.blt (nthD 0 w 1) (Nat.mul (nthD 0 O 0) (nthD 0 O 1)) &&
    Nat.blt (nthD 0 w 2) (Nat.mul (nthD 0 O 0) (nthD 0 O 1)) &&
    Nat.beq (nthD 0 (nthD [] W (nthD 0 w 1)) 0) 0 &&
    conjOK (eltP T O (nthD 0 w 2)) (eltP T O (nthD 0 w 1)) s

@[expose] noncomputable def sqOK (s : Nat) (w : List Nat) : Bool :=
  bif Nat.beq (mulP s s) idP then recW T O ET EO Q L W s w else true

@[expose] noncomputable def witOK (q : Nat) : Bool := sqOK T O ET EO Q L W (eltP T O q) (nthD [] W q)

@[expose] noncomputable def fuseBlk (c : Nat) : Bool :=
  allBelow 32 (fun j => witOK T O ET EO Q L W (Nat.add (Nat.mul 32 c) j))

end

end CFSG.KC.IF4F

end
