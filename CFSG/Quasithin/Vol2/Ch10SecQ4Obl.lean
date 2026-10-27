module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasicBase
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.Blocks
public import CFSG.Quasithin.Background.E1Defs
public import CFSG.Quasithin.Vol2.Ch10StatementsA

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecF

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique

@[expose] def Obl10_2_1E4Nonquasi : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp10 G T L I →
    Ch10.Case10_1_1Two T L I →
    ∀ K : Subgroup G, Ch10.IsLi T L K → IsShort2 K → IsAltType K 5 →
    ∀ X J : Subgroup G, CFSG.SectionRank.IsSQTKCat ↥X → IsSylowTwoOf (Ch10.T1 T L) X →
      J ∈ cComp X → K < J → Ch10.T1 T L ≤ Subgroup.normalizer (J : Set G) →
      Nat.card (Subgroup.center ↥K) = 2 → ¬ CFSG.IsQuasisimple (↥J ⧸ CFSG.pCore 2 ↥J) →
      blockU K ≤ pCoreOf 2 J →
      ∀ z ∈ K, z ∈ Subgroup.centralizer (K : Set G) → z ∉ pCoreOf 2 J → False

@[expose] def FactA314NoSL25Block : Prop :=
  ∀ (Y : Type) [Group Y], Vol2Native.SQTKHypCat Y → CFSG.IsQuasisimple Y →
    ∀ S B : Subgroup Y, IsSylowTwoOf S ⊤ → S ≤ Subgroup.normalizer (B : Set Y) →
      IsShort2 B → IsAltType B 5 → blockZ B = ⊥ → Nat.card (Subgroup.center ↥B) = 2 →
      blockQ B = blockU B ⊔ (Subgroup.center ↥B).map B.subtype → False

@[expose] def FactA314B45 : Prop :=
  ∀ (Y : Type) [Group Y], Vol2Native.SQTKHypCat Y → CFSG.IsQuasisimple Y →
    ∀ S B : Subgroup Y, IsSylowTwoOf S ⊤ → S ≤ Subgroup.normalizer (B : Set Y) → B ≠ ⊤ →
      IsAlt 5 ↥B →
      ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
      ∀ ρ : Y →* MulAut W, ρ.ker ≤ Subgroup.center Y →
      ∀ b ∈ B, orderOf b = 2 → Nat.card ↥(commV (Subgroup.zpowers (ρ b))) ≤ 4 →
        Nonempty (Y ≃* alternatingGroup (Fin 7)) ∨
          (IsHat Y ↥(alternatingGroup (Fin 7)) ∧ Subgroup.center Y ≤ ρ.ker)

end CFSG.Quasithin.Vol2.Ch10.SecF
