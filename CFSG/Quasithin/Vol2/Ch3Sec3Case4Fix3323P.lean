module

public import CFSG.Quasithin.Vol2.Ch3Sec3Setup
public import CFSG.Quasithin.Background.C41PfCorr

public section

namespace CFSG.Quasithin.H13.Ch3Sec3

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

@[expose] def NotCase4Corr3323 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L D : Subgroup G), Hyp331 G T M L D →
    T ≤ Subgroup.normalizer (L : Set G) →
    ∀ α₂ : ↥L →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2)), IsModO2Surj L α₂ →
      ¬ C134CorrLocal.IsC134Case4Corr (L ⊔ T) T L

end CFSG.Quasithin.H13.Ch3Sec3
