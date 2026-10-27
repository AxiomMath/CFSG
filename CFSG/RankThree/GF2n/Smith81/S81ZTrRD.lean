module

public import CFSG.RankThree.GF2n.Smith81.S81ZTr
public import CFSG.RankThree.GF2n.Smith81.S81ZRD

public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81.S81Z

open CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.CurtisTits
  CFSG.RankThree.GF2n.Smith81.XOps CFSG.RankThree.GF2n.Smith81.E7Model
  CFSG.RankThree.GF2n.Smith81.E7X CFSG.RankThree.GF2n.Smith81.S81Z.Tr

variable {K K' : Type} [Field K] [Field K']

theorem twistGp_sN (σ : K ≃+* K') : twistGp σ (sN K) = sN K' := twistGp_nm σ nodeA

end CFSG.RankThree.GF2n.Smith81.S81Z
