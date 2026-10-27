module

public import CFSG.Quasithin.Background.P4InspSp
public import CFSG.Quasithin.Background.P4InspOrth
public import CFSG.Quasithin.Background.P4InspEndSylow
public import CFSG.Quasithin.Background.P4InspEndOuter

public section

namespace CFSG.Quasithin

namespace G11

theorem inspect_simple : InspectSimple :=
  inspectSimple_of_cases inspectSpCase inspectOrthCase inspectD4Case

theorem inspect_sylow : InspectSylow :=
  inspectSylow_of_cases inspectSpCase inspectOrthCase inspectD4Case inspectSylowEnd

theorem inspect_outer : InspectOuter :=
  inspectOuter_of_cases inspectSpCase inspectOrthCase inspectD4Case inspectOuterEnd

end G11

end CFSG.Quasithin
