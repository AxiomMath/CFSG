module

public import CFSG.Quasithin.Background.C2Blocks
public import CFSG.Quasithin.Background.F1Models
public import CFSG.Quasithin.Vol2.Ch10SecC9Ctx
public import CFSG.Quasithin.Vol2.Ch10SecC9S4c

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC

open CFSG.Open CFSG.Quasithin.H13 CFSG.QuasithinUnique CFSG.Quasithin

@[expose] def Obl10_2_9L32Branch : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G) (t w : G) (J : Subgroup G),
    Conf T L I t w J → ¬ CFSG.Open.IsQuasisimple ↥J →
    CharTwo (J ⊔ (T ⊓ Subgroup.centralizer ({w} : Set G))) →
    ∀ hVe : IsElemAbelian 2 (VI T L I J w), CFSG.Open.IsQuasisimple ↥(autI hVe J) →
    Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) →
    (CFSG.Quasithin.IsExcA7Block J ∧ Nonempty (↥(autI hVe J) ≃* ↥(alternatingGroup (Fin 7))) ∨
      Nonempty (↥(autI hVe J) ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) ∨
      Nonempty (↥(autI hVe J) ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2))) →
    J ⊓ Subgroup.centralizer (VI T L I J w : Set G) = pCoreOf 2 J → False

end CFSG.Quasithin.Vol2.Ch10.SecC
