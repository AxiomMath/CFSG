module

public import Certificates.Data.Foote82OmegaSixCent

public section

namespace CFSG.CGT.Foote82.OmegaSix

open Matrix CFSG.ClassicalInvolution.Solomon73.Yamaki

@[expose] def classFive (_ : Unit := ()) : Enum :=
  conjEnum (genO ()) (genOInv ()) (marr bMat) 5184

@[expose] def fiveCheck (_ : Unit := ()) : Bool :=
  let gs := genO ()
  let gsInv := genOInv ()
  let one := idA ()
  let E5 := classFive ()
  let E := omegaEnum ()
  conjTreeOK E5 gs gsInv (marr bMat) &&
    E.elems.all fun x => x == one || !(compA x (compA x (compA x (compA x x))) == one) ||
      (E5.lookup x).isSome

@[expose] def pairCheck (_ : Unit := ()) : Bool :=
  let one := idA ()
  let ar := marr aMat
  let br := marr bMat
  let E := omegaEnum ()
  let C := (oEnum ()).elems.filter fun o => compA o br == compA br o
  E.elems.all fun x => x == one || !(relators.all fun w => wordA #[x, br] w == one) ||
    C.any fun o => compA o ar == compA x o

end CFSG.CGT.Foote82.OmegaSix
