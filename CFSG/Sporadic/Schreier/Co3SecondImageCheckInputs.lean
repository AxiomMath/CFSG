module

public import CFSG.Sporadic.Schreier.Co3GenerationCheck
public meta import CFSG.Sporadic.Schreier.Co3GenerationCheck

public section

namespace CFSG.Sporadic.Schreier.Co3

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Sporadic.Schreier.Co3.Native

@[expose] def co3PermClosure (n : Nat) (gens : Array (Array Nat)) (bound : Nat) :
    Array (Array Nat) × Array Nat × Array Nat := Id.run do
  let mut elts : Array (Array Nat) := #[idA n]
  let mut par : Array Nat := #[0]
  let mut lab : Array Nat := #[0]
  let mut head := 0
  for _ in [0:bound] do
    if head < elts.size && elts.size < bound then
      let e := elts[head]!
      for k in [0:gens.size] do
        let t := compA n gens[k]! e
        if elts.size < bound && !(elts.any fun x => eqA n x t) then
          elts := elts.push t
          par := par.push head
          lab := lab.push k
      head := head + 1
  return (elts, par, lab)

@[expose] def co3D0ImgRec : Array (Array Nat) × Array Nat × Array Nat :=
  co3PermClosure 12 co3D0Kappa1 1000

end CFSG.Sporadic.Schreier.Co3
