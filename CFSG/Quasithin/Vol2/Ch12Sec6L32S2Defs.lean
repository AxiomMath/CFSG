module

public import CFSG.Quasithin.Vol2.Ch12Sec6L32NoFF
public import CFSG.Quasithin.EmptyFaithful.LRed3Four

public section

namespace CFSG.Quasithin.H13.L1232S2

open CFSG.Open CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique S126

attribute [local instance] commGroupOfFact

structure Inputs32 : Prop where
  d310 : D310
  d391 : D391
  insp4 : Insp4
  a21 : AsA21SQTKSection
  g2 : FactG2Cayley
  b42 : AsB42
  b45 : AsB45
  noff : NoFF12632

structure Ctx32 {G : Type} [Group G] [Finite G] (T L V : Subgroup G) [IsMulCommutative ↥V]
    (F : Frame126 T L V) (H K : Subgroup G) : Prop where
  hyp : Hyp126 G T L V
  hZ : V ⊓ Subgroup.centralizer (L : Set G) = ⊥
  isHK : IsHK T L F.V1 H K
  case1 : Case1 T L H K
  f918 : HypF918 T V L F.V1 F.V5 H K

abbrev KQ {G : Type} [Group G] (K : Subgroup G) : Type := ↥K ⧸ CFSG.pCore 2 ↥K

@[expose] def LeafKer : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T V L V₁ Vp H K : Subgroup G)
    (h : HypF918 T V L V₁ Vp H K), (toAutI h Vp).ker = CFSG.pCore 2 ↥K

@[expose] def LeafCenter : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) [IsMulCommutative ↥V]
    (F : Frame126 T L V) (H K : Subgroup G), Ctx32 T L V F H K →
      IsPSL 3 2 2 (KQ K ⧸ Subgroup.center (KQ K)) ∧ Nat.card (Subgroup.center (KQ K)) ∣ 3 ∧
        (Nat.card (Subgroup.center (KQ K)) = 3 →
          H = K ⊔ T ∧ ∀ l ∈ Li L F.V1, ∀ hl : l ∈ H,
            (QuotientGroup.mk ⟨l, hl⟩ : S126.HStar H) ∈ S126.star H K)

@[expose] def NoFFK {G : Type} [Group G] (X C K₀ : Subgroup G) : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) → ∀ ρ : ↥X →* MulAut W,
    (∀ x : ↥X, (x : G) ∈ C → ρ x = 1) →
    (∀ x : ↥X, (x : G) ∈ K₀ → ρ x = 1 → ∀ k ∈ K₀, x * k * x⁻¹ * k⁻¹ ∈ C) →
    ¬ IsFFModule ρ.range

@[expose] def LeafF7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T V L V₁ Vp H K : Subgroup G)
    (_ : HypF918 T V L V₁ Vp H K) (I : Subgroup G),
    V₁ ≤ I → I ≤ conjClosure Vp H → IsIrrPlusTilde V₁ (conjClosure K T) I →
    NoFFK (conjClosure K T ⊔ T) (pCoreOf 2 H) (conjClosure K T) →
    tildeOf V₁ (conjClosure I H) = tildeOf V₁ ⁅conjClosure Vp H, conjClosure K T⁆

@[expose] def LeafComm : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) [IsMulCommutative ↥V]
    (F : Frame126 T L V) (H K : Subgroup G) (_ : HypF918 T V L F.V1 F.V5 H K),
    (∀ l ∈ Li L F.V1, ∀ hl : l ∈ H,
      (QuotientGroup.mk ⟨l, hl⟩ : S126.HStar H) ∈ S126.star H (conjClosure K T)) →
    tildeOf F.V1 ⁅conjClosure F.V5 H, conjClosure K T⁆ = tildeOf F.V1 (conjClosure F.V5 H)

@[expose] def LeafModule (_inp : Inputs32) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) [IsMulCommutative ↥V]
    (F : Frame126 T L V) (H K : Subgroup G) (h : HypF918 T V L F.V1 F.V5 H K),
    SQTKGroup ↥H → conjClosure K T = K → (toAutI h F.V5).ker = CFSG.pCore 2 ↥K →
    IsPSL 3 2 2 (KQ K ⧸ Subgroup.center (KQ K)) → Nat.card (Subgroup.center (KQ K)) ∣ 3 →
    (Nat.card (Subgroup.center (KQ K)) = 3 → H = K ⊔ T) →
    ∃ I : Subgroup G, F.V1 ≤ I ∧ ∃ hIU : I ≤ conjClosure F.V5 H,
      IsIrrPlusTilde F.V1 K I ∧ K ≤ Subgroup.normalizer (I : Set G) ∧
      Nat.card (Subgroup.center (KQ K)) = 3 ∧
      (∀ k ∈ K, (∀ u ∈ conjClosure I H, k * u * k⁻¹ * u⁻¹ ∈ F.V1) → k ∈ pCoreOf 2 H) ∧
      (haveI := factElem h hIU
       ((H ≤ Subgroup.normalizer (I : Set G) ∧
          BinaryNaturalSL (autIH F.V1 I H K) ⊤ ⊥ 3 2) ∨
        ∃ t ∈ autIH F.V1 I H T,
          BinaryNaturalSL (autIH F.V1 I H K) (subM F.V1 (conjClosure I H) I) ⊥ 3 2 ∧
          subM F.V1 (conjClosure I H) I ⊓ (subM F.V1 (conjClosure I H) I).map t.toMonoidHom = ⊥ ∧
          subM F.V1 (conjClosure I H) I ⊔ (subM F.V1 (conjClosure I H) I).map t.toMonoidHom = ⊤))

@[expose] def LeafNoNat : Prop :=
  NoFF12632 → ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) [IsMulCommutative ↥V]
    (F : Frame126 T L V) (H K : Subgroup G) (c : Ctx32 T L V F H K) (I : Subgroup G),
    F.V1 ≤ I → ∀ hIU : I ≤ conjClosure F.V5 H,
    (∀ k ∈ K, (∀ u ∈ conjClosure I H, k * u * k⁻¹ * u⁻¹ ∈ F.V1) → k ∈ pCoreOf 2 H) →
    H ≤ Subgroup.normalizer (I : Set G) →
    haveI := factElem c.f918 hIU
    ¬ BinaryNaturalSL (autIH F.V1 I H K) ⊤ ⊥ 3 2

@[expose] def LeafBridge : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) [IsMulCommutative ↥V]
    (F : Frame126 T L V) (H K : Subgroup G) (h : HypF918 T V L F.V1 F.V5 H K) (I : Subgroup G),
    F.V1 ≤ I → ∀ hIU : I ≤ conjClosure F.V5 H, conjClosure I H = conjClosure F.V5 H →
    (haveI := factElem h hIU
     ∃ t ∈ autIH F.V1 I H T,
        BinaryNaturalSL (autIH F.V1 I H K) (subM F.V1 (conjClosure I H) I) ⊥ 3 2 ∧
        subM F.V1 (conjClosure I H) I ⊓ (subM F.V1 (conjClosure I H) I).map t.toMonoidHom = ⊥ ∧
        subM F.V1 (conjClosure I H) I ⊔ (subM F.V1 (conjClosure I H) I).map t.toMonoidHom = ⊤) →
    ∃ t ∈ T, tildeOf F.V1 I ⊓ tildeOf F.V1 (conjSub t I) = ⊥ ∧
      tildeOf F.V1 I ⊔ tildeOf F.V1 (conjSub t I) = tildeOf F.V1 (conjClosure F.V5 H) ∧
      @BinaryNaturalSL _ (commGroupOfElemAbelian h.toHypF98.toHypF91.isElemAbelian_tilde)
        (autOn (tildeOf F.V1 K) (tildeOf F.V1 (conjClosure F.V5 H)))
        ((tildeOf F.V1 I).subgroupOf (tildeOf F.V1 (conjClosure F.V5 H))) ⊥ 3 2

end CFSG.Quasithin.H13.L1232S2
