module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight56Spine
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.UniquenessCase.UCFront07
public import CFSG.Monster.B.Fischer.Fi22Order

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.RankThreeUC (uniqueSet)
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC22.F08
open CFSG.LocalAnalysis.UniquenessCase.UC22.F07 (PPrimeCoreIn)

@[expose] noncomputable def K889 {G : Type} [Group G] [Finite G] (L : Subgroup G) (ω : G) : Subgroup G :=
  DerInf8 (L ⊓ centralizer ({ω} : Set G))

structure Set889 {G : Type} [Group G] [Finite G] (D : Data G) (L P : Subgroup G) (ω : G) :
    Prop where
  set880 : Set880 D L P
  notLe : ¬ P ≤ L
  mem : ω ∈ P ⊓ centralizer (P : Set G)
  order : orderOf ω = 3
  fac : ∃ z ∈ ZOf (P ⊓ L), ∃ y ∈ CentOverO2 D.M L, ω = z * y
  notZ : ω ∉ ZOf (P ⊓ L)
  notC : ω ∉ CentOverO2 D.M L
  notM : ¬ centralizer ({ω} : Set G) ≤ D.M
  sylow3 : IsSylowOf 3 P ⊤
  normP : normalizer (P : Set G) ≤ D.M
  zcentral : ZOf (P ⊓ L) ≤ centralizer (P : Set G)

structure Facts889 {G : Type} [Group G] [Finite G] (D : Data G) (L P : Subgroup G) (ω : G) :
    Prop where
  perfect : ⁅K889 L ω, K889 L ω⁆ = K889 L ω
  alt6 : IsA6Z3 (Bar2 (K889 L ω))
  imageAlt6 : IsA6Z3 ↥(((K889 L ω).subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)))
  qLe : P ⊓ L ≤ K889 L ω
  centerEq : ((ZOf (P ⊓ L)).subgroupOf (K889 L ω)).map
      (QuotientGroup.mk' (CFSG.pCore 2 ↥(K889 L ω))) = Subgroup.center (Bar2 (K889 L ω))

@[expose] def AllFacts889 {G : Type} [Group G] [Finite G] (D : Data G) : Prop :=
  ∀ L P : Subgroup G, ∀ ω : G, Set889 D L P ω → Facts889 D L P ω

structure Y889 {G : Type} [Group G] [Finite G] (D : Data G) (L P Y : Subgroup G) : Prop where
  card : Nat.card Y = 3
  mem : Y ≤ P ⊓ centralizer (P : Set G)
  zcentral : ZOf (P ⊓ L) ≤ centralizer (P : Set G)
  cent : Y ≤ CentOverO2 D.M L
  disj : Disjoint Y L
  normY : normalizer (Y : Set G) ≤ D.M
  normE : normalizer ((ZOf (P ⊓ L) ⊔ Y : Subgroup G) : Set G) ≤ D.M
  sylow3 : IsSylowOf 3 P ⊤
  normP : normalizer (P : Set G) ≤ D.M

@[expose] def Rank889 {G : Type} [Group G] [Finite G] (D : Data G) : Prop :=
  ∀ L P : Subgroup G, Set880 D L P → ∀ X : Subgroup G, IsTwoLocal X →
    CFSG.Open.pRank 3 X ≤ 3 ∧ ∀ q : ℕ, q.Prime → 7 ≤ q → CFSG.Open.pRank q X ≤ 2

@[expose] def S889Omega {G : Type} [Group G] [Finite G] (D : Data G) : Prop :=
  ∀ L P : Subgroup G, Set880 D L P → ¬ P ≤ L → ∃ ω, Set889 D L P ω

@[expose] def S889Five {G : Type} [Group G] [Finite G] (D : Data G) : Prop :=
  ∀ (L P : Subgroup G) (ω : G), Set889 D L P ω → ∀ X : Subgroup G, X ≠ ⊤ → K889 L ω ≤ X →
    ¬ X ≤ D.M → CFSG.Open.pRank 5 (X ⊓ D.M) ≤ 1

@[expose] def S889Split {G : Type} [Group G] [Finite G] (D : Data G) : Prop :=
  ∀ (L P : Subgroup G) (ω : G), Set889 D L P ω → ∀ X : Subgroup G, X ≠ ⊤ → K889 L ω ≤ X →
    ¬ X ≤ D.M → X ≤ PPrimeCoreIn 3 X ⊔ (X ⊓ D.M)

@[expose] def S889OddCore {G : Type} [Group G] [Finite G] (D : Data G) : Prop :=
  ∀ (L P : Subgroup G) (ω : G), Set889 D L P ω → ∀ X : Subgroup G, X ≠ ⊤ → K889 L ω ≤ X →
    ¬ X ≤ D.M → ¬ 5 ∣ Nat.card (PPrimeCoreIn 3 X) ∧ Group.IsSolvable ↥(PPrimeCoreIn 3 X)

@[expose] def S889O2 {G : Type} [Group G] [Finite G] (D : Data G) : Prop :=
  ∀ (L P : Subgroup G) (ω : G), Set889 D L P ω → ∀ N ∈ calNOf (centralizer ({ω} : Set G)),
    pCoreOf 2 N ≠ ⊥

@[expose] def S889Chief {G : Type} [Group G] [Finite G] (D : Data G) : Prop :=
  ∀ (L P : Subgroup G) (ω : G), Set889 D L P ω → ∀ X ∈ calMOf (K889 L ω), X ≠ D.M →
    X ≤ pCoreOf 2 X ⊔ (X ⊓ D.M)

@[expose] def S889J2Aut {G : Type} [Group G] [Finite G] (D : Data G) : Prop :=
  ∀ (L P : Subgroup G) (ω : G), Set889 D L P ω → ∀ R : Subgroup G, IsPGroup 2 R → R ≤ D.M →
    K889 L ω ≤ normalizer (R : Set G) → pCoreOf 2 L ≤ R →
      ∀ r ∈ R, ∀ l ∈ L, r * l * r⁻¹ * l⁻¹ ∈ pCoreOf 2 L

@[expose] def S889Mod2 {G : Type} [Group G] [Finite G] (D : Data G) : Prop :=
  ∀ (L P : Subgroup G) (ω : G), Set889 D L P ω → ∀ U : Subgroup G, IsPGroup 2 U → U ≠ ⊥ →
    K889 L ω ≤ normalizer (U : Set G) → U ⊓ D.M ≠ ⊥

@[expose] def S889WeakClosed {G : Type} [Group G] [Finite G] (D : Data G) : Prop :=
  ∀ (L P : Subgroup G) (ω : G), Set889 D L P ω → ∀ g : G,
    (ZOf (P ⊓ L)).map (MulAut.conj g).toMonoidHom ≤ normalizer (ZOf (P ⊓ L) : Set G) →
      (ZOf (P ⊓ L)).map (MulAut.conj g).toMonoidHom = ZOf (P ⊓ L)

@[expose] def S889Act : Prop :=
  ∀ (K : Type) [Group K] [Finite K], ⁅(⊤ : Subgroup K), (⊤ : Subgroup K)⁆ = ⊤ →
    IsA6Z3 (K ⧸ CFSG.pCore 2 K) → ∀ (A : Type) [Group A] (φ : K →* A), φ.range ≠ ⊥ →
      ∃ (V : Subgroup ↥φ.range) (_ : V.Normal), IsAlt (↥φ.range ⧸ V) 6

@[expose] def S889Module : Prop :=
  ∀ (q : ℕ), q.Prime → 7 ≤ q → ∀ (K : Type) [Group K] [Finite K],
    ⁅(⊤ : Subgroup K), (⊤ : Subgroup K)⁆ = ⊤ → IsA6Z3 (K ⧸ CFSG.pCore 2 K) →
    ∀ (V : Type) [AddCommGroup V] [Module (ZMod q) V] [Finite V] [Nontrivial V]
      (ρ : K →* Module.End (ZMod q) V), Function.Injective ρ →
      (∀ W : Submodule (ZMod q) V, (∀ k : K, ∀ w ∈ W, ρ k w ∈ W) → W = ⊥ ∨ W = ⊤) →
      ∀ z : K, orderOf z = 3 →
        QuotientGroup.mk' (CFSG.pCore 2 K) z ∈ Subgroup.center (K ⧸ CFSG.pCore 2 K) →
        (∀ v : V, ρ z v = v → v = 0) → ∀ e : K, orderOf e = 5 → (∀ v : V, ρ e v = v → v = 0) →
        (∀ t : K, orderOf t = 2 →
          Module.finrank (ZMod q) (LinearMap.ker (ρ t - 1)) ≤ 2) → False

@[expose] def S889QMin : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (q : ℕ), q.Prime → q ≠ 2 → ∀ A D₀ : Subgroup G,
    IsPGroup q D₀ → ¬ q ∣ Nat.card A → A ≤ normalizer (D₀ : Set G) → ⁅D₀, A⁆ ≠ ⊥ →
    ∃ D : Subgroup G, D ≤ D₀ ∧ A ≤ normalizer (D : Set G) ∧ (∀ x ∈ D, x ^ q = 1) ∧
      ⁅⁅D, D⁆, D⁆ = ⊥ ∧ ¬ ⁅D, A⁆ ≤ ⁅D, D⁆ ∧
      ∀ W : Subgroup G, ⁅D, D⁆ ≤ W → W ≤ D → A ≤ normalizer (W : Set G) → W = ⁅D, D⁆ ∨ W = D

@[expose] def S889QRank : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (q : ℕ), q.Prime → q ≠ 2 → ∀ D : Subgroup G,
    (∀ x ∈ D, x ^ q = 1) → ⁅⁅D, D⁆, D⁆ = ⊥ → CFSG.Open.pRank q D ≤ 2 →
      (⁅D, D⁆.subgroupOf D).index ≤ q ^ 2

@[expose] def S889Dickson : Prop :=
  ∀ (q : ℕ), q.Prime → 7 ≤ q → ∀ (K : Type) [Group K] [Finite K],
    ⁅(⊤ : Subgroup K), (⊤ : Subgroup K)⁆ = ⊤ → IsA6Z3 (K ⧸ CFSG.pCore 2 K) →
    ∀ (V : Type) [AddCommGroup V] [Module (ZMod q) V] [Finite V],
      Module.finrank (ZMod q) V ≤ 2 → ∀ ρ : K →* Module.End (ZMod q) V, ∀ k : K, ρ k = 1

@[expose] def J2AutCore : Prop :=
  ∀ (J : Type) [Group J] [Finite J], IsSpor J .J2 → ∀ K : Subgroup J, IsA6Z3 ↥K →
    ∀ S : Subgroup (MulAut J), IsPGroup 2 S →
      (∀ k ∈ K, MulAut.conj k ∈ normalizer (S : Set (MulAut J))) → S = ⊥

@[expose] def Alt6ModTwoCore : Prop :=
  ∀ (K : Type) [Group K] [Finite K], IsA6Z3 K →
    ∀ (W : Type) [AddCommGroup W] [Module (ZMod 2) W] [Finite W] [Nontrivial W]
      (ρ : K →* Module.End (ZMod 2) W) (z : K), z ∈ Subgroup.center K → z ≠ 1 →
      (∀ w : W, ρ z w = w → w = 0) → ∀ e : K, orderOf e = 5 → ∃ w : W, w ≠ 0 ∧ ρ e w = w

@[expose] def Alt6CharCore : Prop :=
  ∀ (q : ℕ), q.Prime → 7 ≤ q → ∀ (K : Type) [Group K] [Finite K], IsQuasisimple K →
    (Nat.card (Subgroup.center K) = 3 ∨ Nat.card (Subgroup.center K) = 6) →
    IsAlt (K ⧸ Subgroup.center K) 6 →
    ∀ (V : Type) [AddCommGroup V] [Module (ZMod q) V] [Finite V] [Nontrivial V]
      (ρ : K →* Module.End (ZMod q) V) (z : K), z ∈ Subgroup.center K → orderOf z = 3 →
      (∀ v : V, ρ z v = v → v = 0) → ∀ e : K, orderOf e = 5 → ∃ v : V, v ≠ 0 ∧ ρ e v = v

@[expose] def G2FiveRankCore : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (r f : ℕ), r.Prime → CFSG.Blueprint.LieModel Y .G2 0 r f →
    5 ∣ Nat.card Y → 2 ≤ CFSG.Open.pRank 5 (⊤ : Subgroup Y)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
