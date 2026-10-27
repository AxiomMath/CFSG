module

public import CFSG.Quasithin.Vol2.Ch4Sec3Core

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

@[expose] def Gap437Sp4Z : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L : Subgroup G) (n : ℕ) (I H K : Subgroup G) (t : G),
    Setting432K G T M L n I H K t → CharTwo K → IsSp4Block K →
      C41Case2 H (pCoreOf 2 I) (H ⊓ M) L
        ⁅omegaOneCenterOf (T ⊓ centralizerSection M L (pCoreOf 2 L)), L⁆ K →
      blockZ K = ⊥

end CFSG.Quasithin.H13.Ch4
