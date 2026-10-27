module

public import Certificates.Data.YamakiZRig
import Certificates.Kernel.Misc.YamakiS0.Final

public section

namespace Certificates

open CFSG.ClassicalInvolution.Solomon73.Yamaki in
theorem certificate550801 :
    (enumOK (enumS0 ()) (gS0 ()) = true)
    ∧ (sqCount (enumS0 ()) (CFSG.ClassicalInvolution.Solomon73.Yamaki.idA ()) = 144)
    ∧ (sqCount (enumS0 ()) (genA ())[5]! = 0)
    ∧ (sqCount (enumS0 ()) (genA ())[4]! = 48)
    ∧ (sqCount (enumS0 ()) (CFSG.ClassicalInvolution.Solomon73.Yamaki.compA (genA ())[5]! (genA ())[4]!) = 32)
    ∧ (CFSG.ClassicalInvolution.Solomon73.Yamaki.commOK (gS0 ()) (genA ())[5]! = true)
    ∧ (CFSG.ClassicalInvolution.Solomon73.Yamaki.commOK (gS0 ()) (genA ())[4]! = true)
    ∧ (centerOK (enumS0 ()) (gS0 ()) (genA ())[5]! (genA ())[4]! = true) :=
  CFSG.KD.YamakiS0.cert550801_ok

end Certificates
