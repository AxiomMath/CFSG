module

public import CFSG.Quasithin.Background.SmithB45Exc3A7
public import CFSG.Quasithin.Background.SmithB45ExcHS
public import CFSG.Quasithin.Background.SmithB45ExcRu

public section

namespace CFSG.Quasithin

open B45Exc

theorem asB45DichotomyNat_holds :
    AsB45DichotomyNat :=
  asB45DichotomyNat_of_exclusions sporadicExclusion2F_HS sporadicExclusion2F_Ru
    psl3ThreeExclusion2F_holds threeA7Exclusion2F_holds

end CFSG.Quasithin
