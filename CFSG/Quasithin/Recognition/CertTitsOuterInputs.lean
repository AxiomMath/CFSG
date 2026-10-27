module

public import CFSG.Quasithin.Recognition.CertPermOuter
public import CFSG.Quasithin.Recognition.CertTitsSimpleMain
public import CFSG.Quasithin.Recognition.CertDataTitsOuter
public import Certificates.Data.CFSGNative.YGroups.ExactCheck
public import Certificates.Data.CFSGNative.Schreier.Check
public meta import CFSG.Quasithin.Recognition.CertTitsSimpleMain
public meta import CFSG.Quasithin.Recognition.CertDataTitsOuter
public meta import Certificates.Data.CFSGNative.YGroups.ExactCheck
public meta import Certificates.Data.CFSGNative.Schreier.Check
public import CFSG.Assembly.QuasithinDefs
public import CFSG.LocalAnalysis.ComponentInitial.FieldUnitaryTrace
public import CFSG.Quasithin.Background.Basic
public import CFSG.Quasithin.Background.F2Equiv
public import CFSG.Quasithin.Recognition.CertU33Outer

public section

namespace CFSG.Quasithin

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native

@[expose] def titsLabelsNontrivial : Bool :=
  (List.range 1755).all fun p => p == 0 ||
    (List.range 1755).any fun q => q != p && titsLabels[q]! == titsLabels[p]!

@[expose] def titsSift (g : Array ℕ) : Bool :=
  siftA 1755 (rawLevels 1755 titsStrong (titsBase.map Fin.val).toArray)
    (titsBase.map Fin.val).toArray 0 g

end CFSG.Quasithin
