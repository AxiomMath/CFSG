module

public import CFSG.Quasithin.Background.RonanG1015Free
public import CFSG.Quasithin.Background.G10Three
public import CFSG.Quasithin.Background.G10Four
public import CFSG.Quasithin.Background.G10Comp
public import CFSG.Quasithin.Background.SzG11B49Main
public import CFSG.Quasithin.Background.G12Four
public import CFSG.Quasithin.Background.G12FourB
public import CFSG.Quasithin.Background.G12Main
public import CFSG.Quasithin.Background.P4GLMain

public section

namespace CFSG.Quasithin

namespace RonanG1015

theorem g10_15_of_nonsqt (hNS : NonSQTSylow) (hNO : NonSQTOuter) : G1015Free := by
  have h3 := CFSG.Quasithin.G11.g10_3
  have h4 := CFSG.Quasithin.g10_4 h3 CFSG.Quasithin.G11.SzG11S.b49
  have h10 := CFSG.Quasithin.G11.g10_10_of_g10_4 h4
  have h11 := CFSG.Quasithin.G11.g10_11 h10
  have h12 := CFSG.Quasithin.G11.g10_12 h11
  have h13 := CFSG.Quasithin.G11.g10_13 h10 h11
  have h1212 := CFSG.Quasithin.G11.g12_12_of_four
    (CFSG.Quasithin.G11.g12_1_of_four CFSG.Quasithin.G11.g12_four_fact)
    CFSG.Quasithin.G11.g12_part_four_fact
  exact g10_15_free h10 h11 h12 h13 h1212 CFSG.Quasithin.G11.outerGLInput
    CFSG.Quasithin.G11.inspect_simple (inspectOuterQ_of hNO) (inspectSylowFree_of hNS)

end RonanG1015

end CFSG.Quasithin
