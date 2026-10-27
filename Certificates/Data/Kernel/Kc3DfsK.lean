module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3SporPermCode
public import Std.Data.HashMap

public section

namespace CFSG.KC.Kc3K

open CFSG.QuasithinUnique.A5.Kc3SporPerm

@[expose] noncomputable def histK (vals : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun v _ ih => Nat.add ih (Nat.shiftLeft 1 (Nat.mul 8 v))) vals

@[expose] def cntK (H v : Nat) : Nat := Nat.land (Nat.shiftRight H (Nat.mul 8 v)) 255

@[expose] def valsK (ct : Nat → Nat → Nat) (el : List Nat) : List Nat :=
  pairsL.map fun p => ct (el.getD p.1 0) (el.getD p.2 0)

@[expose] noncomputable def leafK (pr ct : Nat → Nat → Nat) (i j k l : Nat) : Bool :=
  (fun vals => (fun H => vals.any fun v => !(okSize (cntK H v))) (histK vals))
    (valsK ct ((List.range 16).map (elF pr i j k l)))

@[expose] noncomputable def dfsKI (M : Nat) (pr ct : Nat → Nat → Nat) (nbr : Nat → List Nat)
    (NM : Nat → Nat) (i : Nat) : Bool :=
  (nbr i).all fun j =>
    !(g2 M pr i j) ||
      (fun K => (nbr i).all fun k =>
        !(K.testBit k) || !(g3 M pr i j k) ||
          (fun L => (nbr i).all fun l =>
            !(L.testBit l) || !(g4 M pr i j k l) || leafK pr ct i j k l)
          (K &&& NM k &&& NM (pr i k) &&& NM (pr j k) &&& NM (pr (pr i j) k)))
      (NM i &&& NM j &&& NM (pr i j))

@[expose] noncomputable def dfsKR (M : Nat) (pr ct : Nat → Nat → Nat) (nbr : Nat → List Nat)
    (NM : Nat → Nat) (lo len : Nat) : Bool :=
  (List.range len).all fun t => dfsKI M pr ct nbr NM (lo + t)

end CFSG.KC.Kc3K

end
