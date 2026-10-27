module

public import Init

public section

namespace CFSG.KC.PtEnum

@[expose] def getF (G : List (Nat → Nat)) (j : Nat) : Nat → Nat := G.getD j id

@[expose] def rowsOKF (n : Nat) (P : List Nat) (G : List (Nat → Nat)) (Ts : Array (List Nat))
    (par lab cl : Array Nat) : Bool :=
  Nat.blt 0 Ts.size && Ts[0]! == P &&
  Ts.toList.all (fun T => T.all fun p => Nat.blt p n) &&
  decide Ts.toList.Nodup &&
  (List.range Ts.size).all (fun i => (List.range G.length).all fun j =>
    Nat.blt cl[i * G.length + j]! Ts.size &&
      Ts[cl[i * G.length + j]!]! == (Ts[i]!).map (getF G j)) &&
  (List.range Ts.size).all (fun i => i == 0 ||
    (Nat.blt par[i]! i && Nat.blt lab[i]! G.length && cl[par[i]! * G.length + lab[i]!]! == i))

end CFSG.KC.PtEnum

end
