module

public import CFSG.LocalAnalysis.WeakClosure81.SevenDefs
public import CFSG.Quasithin.Background.E3Defs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def IsGConj (V B : Subgroup G) : Prop := ∃ g : G, B = conjSubgroup V g

@[expose] def nineFrattini (X : Subgroup G) : Subgroup G := (frattini ↥X).map X.subtype

@[expose] def nineFrattiniR (K X : Subgroup G) : Subgroup G := nineFrattini X ⊔ pCoreOf 2 K

@[expose] def IrredOnFrattiniQuot (S X : Subgroup G) : Prop :=
  nineFrattini X < X ∧
    ∀ Y : Subgroup G, nineFrattini X ≤ Y → Y ≤ X →
      (∀ s ∈ S ⊓ normalizer (X : Set G), ∀ y ∈ Y, s * y * s⁻¹ ∈ Y) →
        Y = nineFrattini X ∨ Y = X

@[expose] def calP (V : Subgroup G) : Set (Subgroup G) :=
  {X | ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ IsPGroup p X ∧ X ≤ normalizer (V : Set G) ∧
      rankThreeGamma 1 p X ≤ normalizer (V : Set G) ∧
      ∀ g : G, g ∉ normalizer (V : Set G) → conjSubgroup V g ≤ normalizer (V : Set G) →
        X ⊓ conjSubgroup (normalizer (V : Set G)) g = ⊥}

@[expose] def calPMTA (V T A : Subgroup G) : Set (Subgroup G) :=
  {K | E1.IsEAny (normalizer (V : Set G)) T A K ∧
      ∃ X ∈ calP V, (K : Set G) = ((T ⊓ K : Subgroup G) : Set G) * (X : Set G)}

@[expose] def nineE (V K : Subgroup G) : Subgroup G :=
  omegaOneCenterOf (E3.wClos V 1 (pCoreOf 2 K))

@[expose] def omegaIn (V H E : Subgroup G) : Set (Subgroup G) :=
  {U | U ∈ omegaSet V H E ∧ U ≤ H}

@[expose] def nineOmegaIn (V K S : Subgroup G) : Set (Subgroup G) :=
  {B | B ∈ omegaSet V K (nineE V K) ∧ B ≤ S}

structure TwoPTwo (K S X : Subgroup G) (p : ℕ) : Prop where
  prime : p.Prime
  odd : p ≠ 2
  oTwoPTwo : E1.oTwoPTwo ↥K p = ⊤
  sylowTwo : IsSylowIn 2 S K
  sylowP : IsSylowIn p X K

structure TwoPTwoIrred (K S X : Subgroup G) (p : ℕ) : Prop extends TwoPTwo K S X p where
  irred : IrredOnFrattiniQuot S X

structure Nine1Hyp (V K S X : Subgroup G) (p : ℕ) : Prop extends TwoPTwoIrred K S X p where
  le : K ≤ normalizer (V : Set G)

structure Nine2Hyp (V K S X : Subgroup G) (p : ℕ) : Prop where
  base : Nine1Hyp V K S X p
  mem : X ∈ calP V
  notW : ¬ K ≤ normalizer (E3.wClos V 0 S : Set G)
  notC : ⁅twoResidual K, E3.cClos V 1 S⁆ ≠ ⊥

@[expose] def NineOneThree (V K : Subgroup G) : Prop :=
  (∀ B : Subgroup G, IsGConj V B → B ≤ K →
      B ∈ omegaIn V K (nineE V K) ∨ B ≤ pCoreOf 2 K) ∧
    ∀ B : Subgroup G, IsGConj V B → B ≤ pCoreOf 2 K → ⁅B, twoResidual K⁆ = ⊥

structure Hyp9 (V T : Subgroup G) : Prop where
  hyp7 : Hyp7 V
  sylow : IsSylowIn 2 T (normalizer (V : Set G))
  ne : V ≠ E3.wClos V 0 T
  rk_gt : 2 < rk ↥V

@[expose] def Thm93 (V T : Subgroup G) : Prop :=
  Hyp9 V T → ∀ A : Subgroup G, IsGConj V A → A ≤ T →
    IsSylowIn 2 (T ⊓ centralizer (A : Set G))
      (normalizer (V : Set G) ⊓ centralizer (A : Set G)) →
    normalizer (E3.wClos V 1 T : Set G) ≤ normalizer (V : Set G) ∨ calPMTA V T A = ∅

@[expose] def SevenSixThreeAbelian (V : Subgroup G) : Prop :=
  Hyp7 V → ∀ (H E J A Y : Subgroup G) (p : ℕ), p.Prime → p ≠ 2 →
    E ≤ H → (E.subgroupOf H).Normal → IsMulCommutative E →
    iSub V H E ≤ J → J ≤ pCoreOf 2 H → (J.subgroupOf H).Normal →
    A ∈ omegaSet V H E → A ≤ H → J.relIndex A = 2 →
    J ≤ Y → Y ≤ H → A ≤ normalizer (Y : Set G) → Y ≤ ⁅Y, A⁆ ⊔ J →
    (∀ a ∈ A, (∀ y ∈ Y, ⁅a, y⁆ ∈ J) → a ∈ J) →
    (∀ y ∈ Y, y ^ p ∈ J) → (∀ y ∈ Y, ∀ z ∈ Y, ⁅y, z⁆ ∈ J) →
    J.relIndex Y = p

end CFSG.LocalAnalysis.WeakClosure81
