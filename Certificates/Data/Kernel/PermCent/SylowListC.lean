module

public import Certificates.Data.Kernel.PermCent.CV

public section

namespace CFSG.Certificates.Kernel.PkCV.SylL

variable {n : Nat} [Small n]

@[expose] noncomputable def wordC (gs : List (CV n)) : List Nat → CV n
  | [] => 1
  | k :: w => gs.getD k 1 * wordC gs w

@[expose] noncomputable def distinctC : List (CV n) → Bool
  | [] => true
  | x :: L => L.all (fun y => !decide (x = y)) && distinctC L

@[expose] noncomputable def closedC (G L : List (CV n)) : Bool :=
  L.any (fun x => decide (x = 1)) && distinctC L &&
    G.all fun g => L.all fun x => L.any fun y => decide (g * x = y)

@[expose] noncomputable def coverAtC (gA R : List (CV n)) (x : CV n) :
    Option (Nat × List Nat) → Bool
  | none => !(decide (x * x = 1) && !decide (x = 1))
  | some (r, w) => match R[r]? with
    | some ρ => decide (wordC gA w * x = ρ * wordC gA w)
    | none => false

@[expose] noncomputable def coverC (gA R : List (CV n)) :
    List (CV n) → List (Option (Nat × List Nat)) → Bool
  | [], _ => true
  | x :: L, c :: cs => coverAtC gA R x c && coverC gA R L cs
  | _ :: _, [] => false

end CFSG.Certificates.Kernel.PkCV.SylL

end
