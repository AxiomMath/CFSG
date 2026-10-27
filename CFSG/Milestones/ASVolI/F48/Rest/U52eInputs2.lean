module

public import CFSG.Milestones.ASVolI.F48.Rest.U52eInputs

public section

namespace CFSG.ASVolI

open CFSG.ONSchreier.Native CFSG.Sporadic.HNOddCore CFSG.Monster.B.Co2.Native
  CFSG.Certificates.Native

set_option compiler.extract_closed false

@[expose] def burnsideF48t_u52eKLOK (_ : Unit := ()) : Bool :=
  let KL := burnsideF48t_u52KL ()
  allBelowN 4 fun j =>
    let C := burnsideF48t_u52eKL j ()
    (KL.all fun k => !peq 462 k (C.getD 9 (pid 462))) &&
      allBelowN 9 fun m => peq 462 (C.getD m (pid 462)) (KL.getD m (pid 462)) &&
        peq 462 (C.getD (m + 9) (pid 462)) (pcomp 462 (C.getD 9 (pid 462)) (KL.getD m (pid 462)))

end CFSG.ASVolI
