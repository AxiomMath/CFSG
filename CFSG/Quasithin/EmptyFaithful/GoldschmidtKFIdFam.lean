module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentJ4Three
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1J4OutFinal

public section

namespace CFSG.QuasithinUnique.Id2519

theorem identFamilies_proved :
    IdentFamilies :=
  identFamilies_of_open
    { coverG24 := tabIdentFor_coverG24
      j4 := J4Row.tabIdentFor_j4_of Setup.X1.j4OuterOdd J4Row.centralizerCore_one
        J4Row.centralizerCore_three
      hs := SporHS.tabIdentFor_hs
      he := SporHe.tabIdentFor_he_of HeInner.he_inner_noK
      ru := MathNoLayer.tabIdentFor_ru }

end CFSG.QuasithinUnique.Id2519
