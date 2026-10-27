module

public import CFSG.Sporadic.J4.QTRankWitNative
public meta import CFSG.Sporadic.J4.QTRankWitNative
public import Certificates.Certificate4026

public section

namespace CFSG.Sporadic.J4.QT

open CFSG.Sporadic.J4.Native

theorem X11_pow : eqRows (powRows (X11 ()) 11) idRows = true :=
  Certificates.certificate4026.1

theorem Y11_pow : eqRows (powRows (Y11 ()) 11) idRows = true :=
  Certificates.certificate4026.2.1

theorem Z11_pow : eqRows (powRows (Z11 ()) 11) idRows = true :=
  Certificates.certificate4026.2.2.1

theorem Z11_ne : eqRows (Z11 ()) idRows = false :=
  Certificates.certificate4026.2.2.2.1

theorem Z11_wf : wfRows (Z11 ()) = true ∧ wfRows idRows = true :=
  Certificates.certificate4026.2.2.2.2.1

theorem XZ11_comm :
    eqRows (mulRows (X11 ()) (Z11 ())) (mulRows (Z11 ()) (X11 ())) = true :=
  Certificates.certificate4026.2.2.2.2.2.1

theorem YZ11_comm :
    eqRows (mulRows (Y11 ()) (Z11 ())) (mulRows (Z11 ()) (Y11 ())) = true :=
  Certificates.certificate4026.2.2.2.2.2.2.1

theorem AX11_inv :
    eqRows (mulRows (mulRows rowsA (X11 ())) rowsA) (powRows (X11 ()) 10) = true :=
  Certificates.certificate4026.2.2.2.2.2.2.2.1

theorem AZ11_comm :
    eqRows (mulRows rowsA (Z11 ())) (mulRows (Z11 ()) rowsA) = true :=
  Certificates.certificate4026.2.2.2.2.2.2.2.2.1

theorem C37_pow : eqRows (powRows (C37 ()) 37) idRows = true :=
  Certificates.certificate4026.2.2.2.2.2.2.2.2.2.1

theorem C37_ne : eqRows (C37 ()) idRows = false :=
  Certificates.certificate4026.2.2.2.2.2.2.2.2.2.2.1

theorem C37_wf : wfRows (C37 ()) = true :=
  Certificates.certificate4026.2.2.2.2.2.2.2.2.2.2.2.1

theorem AE5_pow : eqRows (powRows (AE5 ()) 11) idRows = true :=
  Certificates.certificate4026.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem orbit_five : ∃ o ∈ orbits, o.1 = 3 ∧ ∃ p ∈ o.2.1, p.1 = 5 :=
  Certificates.certificate4026.2.2.2.2.2.2.2.2.2.2.2.2.2

end CFSG.Sporadic.J4.QT
