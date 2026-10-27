module

public import Certificates.Data.Foote82OmegaSixCent
public import Certificates.Data.Foote82InvolAutA6

public section

namespace CFSG.CGT.Foote82.OmegaSix

open CFSG.ClassicalInvolution.Solomon73.Yamaki CFSG.CGT.Foote82.InvolA6

@[expose] def tiWitness (t g gi : Array ℕ) : Bool :=
  let u := compA (compA g t) gi
  let p := compA t u
  compA p p == idA () && (List.range 64).any fun k => t[u[k]! ^^^ k]! != u[k]! ^^^ k

@[expose] def tiCheck (_ : Unit := ()) : Bool :=
  let O := oEnum ()
  let W := omegaEnum ()
  let one := idA ()
  allLt O.elems.size fun i =>
    let t := O.elems[i]!
    compA t t != one || t == one || rank1 t ||
      anyLt W.elems.size fun j =>
        let g := W.elems[j]!
        let k := (W.lookup (invArr g)).getD 0
        decide (k < W.elems.size) && compA g W.elems[k]! == one && tiWitness t g W.elems[k]!

end CFSG.CGT.Foote82.OmegaSix
