module

public import Certificates.Data.Kernel.FiveStdKSyl

public section

namespace CFSG.KC.FiveStdK

@[expose] def dedupK (L : List Nat) : List Nat :=
  L.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) []

@[expose] noncomputable def closureAuxK (gens : List Nat) : Nat → List Nat → List Nat
  | 0, L => L
  | fuel + 1, L =>
    let L' := dedupK (L ++ L.flatMap fun x => gens.map fun g => mulK x g)
    if L'.length = L.length then L else closureAuxK gens fuel L'

@[expose] noncomputable def closureK (gens : List Nat) : List Nat := closureAuxK gens 64 [oneK]

@[expose] noncomputable def powersK (g n : Nat) : List Nat := (List.range n).map fun i => powK g i

@[expose] noncomputable def ppK (a b m n : Nat) : List Nat :=
  (powersK a m).flatMap fun x => (powersK b n).map fun y => mulK x y

end CFSG.KC.FiveStdK

end
