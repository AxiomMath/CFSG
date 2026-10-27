module

public import CFSG.Quasithin.EmptyFaithful.Insp7Final4
public import CFSG.Quasithin.EmptyFaithful.Insp7NumJ
public import CFSG.Quasithin.EmptyFaithful.Insp7NumR
public import CFSG.Quasithin.EmptyFaithful.Insp7NumU
public import CFSG.Quasithin.EmptyFaithful.Insp7NumV
public import CFSG.Quasithin.EmptyFaithful.Insp7NumX
public import CFSG.Quasithin.EmptyFaithful.Insp7NumTits
public import CFSG.Quasithin.EmptyFaithful.Insp7NumS

public section

namespace CFSG.Quasithin

namespace Insp7

theorem lemma14320Inspect_cards
    : S143.Lemma14320Inspect :=
  lemma14320Inspect_of_natives (fun _ hs => card_carrier_big hs)
    (fun _ hs => isSimpleGroup_carrier_small hs) numFactAt_m11 numFactAt_m12 numFactAt_m22
    numFactAt_m23 numFactAt_j2 numFactAt_l34 numFactAt_tits

end Insp7

end CFSG.Quasithin
