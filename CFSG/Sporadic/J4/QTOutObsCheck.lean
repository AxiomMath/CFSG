module

public import CFSG.Sporadic.J4.QTOutObsNative
public meta import CFSG.Sporadic.J4.QTOutObsNative
public import CFSG.Sporadic.J4.QTOutCocCheck
public import Certificates.Certificate4023
public meta import CFSG.Sporadic.J4.QTRankWitNative

public section

namespace CFSG.Sporadic.J4.QT

open CFSG.Sporadic.J4.Native

theorem obs_wf :
    wfRows e5Rows = true ∧ wfRows gRows = true ∧ wfRows yRows = true :=
  Certificates.certificate4023.1

theorem obs_y_sq : eqRows (mulRows yRows yRows) idRows = true :=
  Certificates.certificate4023.2.1

theorem obs_conj :
    eqRows (mulRows (mulRows yRows e5Rows) yRows) (mulRows (etaR cB) hRows) = true :=
  Certificates.certificate4023.2.2.1

theorem obs_letters : ∀ ℓ ∈ wObs, ℓ ∈ letters :=
  Certificates.certificate4023.2.2.2.1

theorem obs_fixed :
    ∀ f ∈ fvs, (frApply (frTable e5Rows) f).beq f = true :=
  Certificates.certificate4023.2.2.2.2.1

theorem obs_tri_f : triOK fvs fps = true :=
  Certificates.certificate4023.2.2.2.2.2.1

theorem obs_tri_x : triOK ximgs xps = true :=
  Certificates.certificate4023.2.2.2.2.2.2.1

theorem obs_sizes : fvs.size = 62 ∧ xvs.size = 51 :=
  Certificates.certificate4023.2.2.2.2.2.2.2.1

theorem obs_lt : cA < 2 ^ 11 ∧ cB < 2 ^ 11 :=
  Certificates.certificate4023.2.2.2.2.2.2.2.2

end CFSG.Sporadic.J4.QT
