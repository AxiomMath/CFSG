module

public section

namespace CFSG.KC.CF23L34

@[expose] def rL (R : List (Nat × Nat)) (l : Int) : Nat × Nat :=
  if 0 < l then R.getD (l.toNat - 1) (0, 0)
  else ((R.getD ((-l).toNat - 1) (0, 0)).2, (R.getD ((-l).toNat - 1) (0, 0)).1)

@[expose] noncomputable def rW1(m : Nat → Nat → Nat) (e : Nat) (R : List (Nat × Nat)) (w : List Int) :
    Nat × Nat :=
  List.rec (motive := fun _ => Nat × Nat) (e, e)
    (fun l t ih => List.rec (motive := fun _ => Nat × Nat) (rL R l)
      (fun _ _ _ => (m (rL R l).1 ih.1, m ih.2 (rL R l).2)) t) w

@[expose] noncomputable def rRun1(m : Nat → Nat → Nat) (e : Nat) (R : List (Nat × Nat))
    (prog : List (List Int)) : List (Nat × Nat) :=
  prog.foldl (fun R w => R ++ [rW1 m e R w]) R

end CFSG.KC.CF23L34

end
