module

public import CFSG.Quasithin.H13.LocDblHeData
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicHe
public import Certificates.Data.CFSGNative.H13.LocDblDc
public meta import CFSG.Quasithin.H13.LocDblHeEdges1
public meta import CFSG.Quasithin.H13.LocDblHeEdges2
public meta import CFSG.Quasithin.H13.LocDblHeEdges3
public meta import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicBaseNative
public meta import Certificates.Data.CFSGNative.He.Certificate
public import CFSG.Quasithin.H13.LocDblHeCheckInputs
public import CFSG.Quasithin.H13.LocDblDcSylow
import CFSG.Blueprint.NativeSporadic
public import Certificates.Certificate3168
public import Certificates.Certificate7030
public import Certificates.Certificate4141
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListMain

public section

namespace CFSG.Quasithin.H13.LocDbl

open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Sporadic.He
open CFSG.Blueprint.NativeSporadic (Carrier)

theorem sylowNoDouble_He_group :
    SylowNoDouble ↥J :=
  Certificates.certificate7030.1

theorem sylowNoDouble_He :
    SylowNoDouble (Carrier .He) := by
  have h : SylowNoDouble CFSG.Blueprint.NativeSporadic.He :=
    SylowNoDouble.of_mulEquiv (A := ↥J) (A' := CFSG.Blueprint.NativeSporadic.He) heEquivJ.symm
      sylowNoDouble_He_group
  exact h

end CFSG.Quasithin.H13.LocDbl
