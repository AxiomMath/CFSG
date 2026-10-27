module

public import Certificates.Data.Kernel.Misc.YamakiNA

public section

namespace CFSG.KD.YamakiNA

open CFSG.KD.BfsK CFSG.KD.YamakiA0 CFSG.KD.YamakiCE CFSG.ClassicalInvolution.Sp62Rec
open CFSG.KD.Sp62 (MULF ONE)

@[expose] noncomputable def sylChunk (S RA : Nat → Nat) (L q : Nat) : Bool :=
  CFSG.KD.YamakiRepF.strictY (wordN RA sylMeetWord) fun g =>
  CFSG.KD.YamakiRepF.strictY (wordN RA sylMeetWord.reverse) fun gi =>
    CFSG.KC.Misc.Clos.allR (Nat.mul L q) L fun t => cond (Nat.blt t 512)
      (CFSG.KD.YamakiRepF.strictY (recX S 9 t) fun x =>
        !(memK S 9 512 (MULF (MULF gi x) g)) || memK RA 12 64 x)
      true

end CFSG.KD.YamakiNA

end
