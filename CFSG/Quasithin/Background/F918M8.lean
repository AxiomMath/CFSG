module

public import CFSG.Quasithin.Background.F918L4
public import CFSG.Quasithin.Background.F918M6

public section

namespace CFSG.Quasithin

theorem d36ActsDirect_holds :
    D36ActsDirect :=
  d36ActsDirect_of (d3L38_of_a38 d3A38_holds)

theorem d36Acts_of_glued
    (hG : D36ActsGlued) :
    D36Acts :=
  d36Acts_of_split d36ActsDirect_holds hG

end CFSG.Quasithin
