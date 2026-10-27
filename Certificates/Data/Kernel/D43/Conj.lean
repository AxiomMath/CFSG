module

public import Certificates.Data.Kernel.D43.Twin

public section

namespace CFSG.KC.D43

open CFSG.KS.ON

@[expose] noncomputable def mvW (RL : List (List Nat)) : List Nat → Nat → Nat
  | [], X => X
  | k :: w, X => mv (RL.getD k []) (mvW RL w X)

@[expose] noncomputable def mvWok (RL : List (List Nat)) : List Nat → Nat → Bool
  | [], X => wf84 X
  | k :: w, X => mvWok RL w X && wf84 (mv (RL.getD k []) (mvW RL w X))

@[expose] noncomputable def conjOK (RL : List (List Nat)) (k : Nat) (w : List Nat) : Bool :=
  (List.range 84).all fun j =>
    wf84 ((RL.getD k []).getD j 0) && mvWok RL w ((RL.getD 8 []).getD j 0) &&
      Nat.beq (mv (RL.getD 8 []) ((RL.getD k []).getD j 0)) (mvW RL w ((RL.getD 8 []).getD j 0))

@[expose] def conjW : List (List Nat) :=
  [[0], [1], [2], [3, 2], [4, 3, 3, 2], [5], [6, 5], [7, 6, 6, 5]]

end CFSG.KC.D43

end
