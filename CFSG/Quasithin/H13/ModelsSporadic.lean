module

public import CFSG.Quasithin.Recognition.ModelBridgesJ3
public import CFSG.Sporadic.HS
public import CFSG.Sporadic.Ru
public meta import CFSG.Open.QuasithinDefs
public meta import CFSG.Blueprint.NativeSporadic
public meta import CFSG.Quasithin.Recognition.ModelBridgesJ3
import all CFSG.Blueprint.NativeSporadic
public import Certificates.Certificate7033
public import Certificates.Certificate3167
public import Certificates.Certificate3172
public import CFSG.Sporadic.Th.F2Spec

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint.NativeSporadic CFSG.Quasithin

theorem hs_entries₁ : nativeModeOneEntries HSSeed1 = quasithinDigits quasithinHSData1 := by
  decide +kernel

theorem hs_entries₂ : nativeModeOneEntries HSSeed2 = quasithinDigits quasithinHSData2 := by
  decide +kernel

theorem ru_entries₁ :
    nativeModeOneEntries RuSeed1 = quasithinDigits quasithinRuData1 :=
  Certificates.certificate7033.1

theorem ru_entries₂ :
    nativeModeOneEntries RuSeed2 = quasithinDigits quasithinRuData2 :=
  Certificates.certificate7033.2

end CFSG.Quasithin.H13
