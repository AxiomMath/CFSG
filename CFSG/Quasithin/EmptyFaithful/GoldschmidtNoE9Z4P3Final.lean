module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4P3Main
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4P5Defs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7

theorem e9Fstar_of_inputs (h35 : Lemma1435) (h36 : A36ForSQTK)
    (h37 : A37ForSQTK) (hlist : SQTKList3Dvd) (iS : Input14614NoSz) (iL : Input14614ListsE9) :
    E9Fstar := by
  intro G _ _ T M S H PQ p hred hmax hshape
  exact e9z4_oTwoUpper_le_fstar (stage14614E9_of_inputs h35 h36 h37 hlist iS iL) S hred hmax
    hshape

theorem e9Normalizer_of_inputs (h35 : Lemma1435)
    (h36 : A36ForSQTK) (h37 : A37ForSQTK) (hlist : SQTKList3Dvd) (iS : Input14614NoSz)
    (iL : Input14614ListsE9) : E9Normalizer := by
  intro G _ _ T M S H PQ p hred hmax hshape R₁ R₂ s hdat
  exact e9z4_lemma_14_6_16 h35 h36 hlist iS (stage14614E9_of_inputs h35 h36 h37 hlist iS iL) S
    hred hmax hshape hdat

end CFSG.Quasithin
