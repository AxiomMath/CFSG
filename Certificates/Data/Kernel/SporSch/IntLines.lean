module

public import Certificates.Data.Kernel.LocalQT.CovT

public section

namespace CFSG.KC.IntLines

open CFSG.KC.LQT.Cov

@[expose] noncomputable def intsSK (ts : List (List Char)) : Option (List Int) :=
  List.rec (motive := fun _ => Option (List Int)) (some [])
    (fun t _ ih => List.rec (motive := fun _ => Option (List Int)) ih
      (fun _ _ _ => Option.rec (motive := fun _ => Option (List Int)) none
        (fun x => Option.rec (motive := fun _ => Option (List Int)) none
          (fun xs => some (List.cons x xs)) ih) (intK t)) t) ts

@[expose] noncomputable def lineInts (l : List Char) : List Int :=
  Option.rec (motive := fun _ => List Int) [] (fun xs => xs) (intsSK (tokK l))

@[expose] noncomputable def nonEmpty (l : List Char) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun _ _ _ => true) l

@[expose] noncomputable def linesNE (cs : List Char) : List (List Char) := (linesK cs).filter nonEmpty

@[expose] noncomputable def textOK (cs : List Char) : Bool :=
  (linesNE cs).all fun l => Option.rec (motive := fun _ => Bool) false (fun _ => true) (intsSK (tokK l))

end CFSG.KC.IntLines

end
