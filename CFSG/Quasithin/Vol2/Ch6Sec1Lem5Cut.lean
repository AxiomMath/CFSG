module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem5B

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin

structure Cx615B (G : Type) [Group G] [Finite G] (T M L V H : Subgroup G) (n : ℕ) : Prop
    extends Cx615 G T M L V H n where
  V_eq : V = reducedAggregate (L ⊔ T)
  JL : ⁅L, thompsonJ T⁆ = L
  JK : ⁅oTwoUpper H, thompsonJ T⁆ = oTwoUpper H
  nat : IsNatQuotCh5 L V n
  ZL : ¬ quasithinOmegaOneCenter T ⊓ ⁅V, L⁆ ≤ Subgroup.centralizer (L : Set G)
  CZd : ∀ d ∈ borelL T L, Odd (orderOf d) → d ≠ 1 →
    quasithinOmegaOneCenter T ⊓ Subgroup.centralizer ({d} : Set G) ≤
      Subgroup.centralizer (L : Set G)
  CMZ : M ⊓ Subgroup.centralizer ((quasithinOmegaOneCenter T ⊓ ⁅V, L⁆ : Subgroup G) : Set G) ≤
    Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G)
  hU : IsElemAbelian 2 (Cx615.UH T H)
  e23 : E2.E23Concl H T (Cx615.UH T H) hU
  s3 : ∀ I : Finset (Subgroup (MulAut (IntMod (Cx615.UH T H) hU))), (I.card = 1 ∨ I.card = 2) →
    autI hU (thompsonJ H) = ⨆ K ∈ I, K →
    (∀ K ∈ I, (∃ m : ℕ, E2.IsL2Natural K (fixV (autI hU (twoResidual H))) m) ∨
      E2.IsA5Module K) →
    ∀ K ∈ I, E2.IsL2Natural K (fixV (autI hU (twoResidual H))) 1

@[expose] def Res615Cent : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V H : Subgroup G) (n : ℕ),
    Cx615B G T M L V H n → H ⊓ Subgroup.centralizer (Cx615.UH T H : Set G) ≤ pCoreOf 2 H

structure Cx615C (G : Type) [Group G] [Finite G] (T M L V H : Subgroup G) (n : ℕ) : Prop
    extends Cx615B G T M L V H n where
  cent : H ⊓ Subgroup.centralizer (Cx615.UH T H : Set G) = pCoreOf 2 H
  HJT : H = thompsonJ H ⊔ T
  X_O2 : pCoreOf 2 (borelL T L ⊔ H) ≠ ⊥
  faithful : (borelL T L ⊔ T) ⊓ Subgroup.centralizer
    (conjClosure (quasithinOmegaOneCenter T) (borelL T L ⊔ H) : Set G) ≤ T
  QX : pCoreOf 2 (borelL T L ⊔ H) = T ⊓ Subgroup.centralizer
    (conjClosure (quasithinOmegaOneCenter T) (borelL T L ⊔ H) : Set G)

abbrev kStar615 {G : Type} [Group G] (T L H : Subgroup G) : Subgroup G :=
  oTwoUpper H ⊔ (borelL T L ⊔ H) ⊓
    Subgroup.centralizer (conjClosure (quasithinOmegaOneCenter T) (borelL T L ⊔ H) : Set G)

@[expose] def Res615D : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V H : Subgroup G) (n : ℕ),
    Cx615C G T M L V H n →
      ¬ borelL T L ≤ Subgroup.normalizer ((kStar615 T L H : Subgroup G) : Set G)

@[expose] def Res615E : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V H : Subgroup G) (n : ℕ),
    Cx615C G T M L V H n →
      ¬ borelL T L ≤ Subgroup.normalizer ((kStar615 T L H : Subgroup G) : Set G) → False

end CFSG.Quasithin.H13
