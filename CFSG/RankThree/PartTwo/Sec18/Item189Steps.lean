module

public import CFSG.RankThree.PartTwo.Sec18.Statements

public section

namespace CFSG.RankThree.PartTwo.Sec18

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late
open CFSG.Assembly.RankThreeEven (projSL projSU)

section Notation

variable {G : Type} [Group G]

noncomputable abbrev s189 (M H : Subgroup G) : Subgroup G :=
  CFSG.Open.pCoreOf 2 (H ⊓ M)

noncomputable abbrev n189 (H : Subgroup G) : Subgroup G :=
  Subgroup.normalizer (inSubgroup perfectResidual H : Set G)

noncomputable abbrev sk189 (M H : Subgroup G) (c : G) : Subgroup G :=
  s189 M H ⊔ normalClosureIn M c

noncomputable abbrev theta189 (M H : Subgroup G) (c : G) : Subgroup G :=
  inSubgroup (aschbacherSolvableCore 3) (sk189 M H c)

abbrev SKAlpha189 (M H : Subgroup G) (c : G) : Type :=
  ↥(sk189 M H c) ⧸ aschbacherSolvableCore 3 ↥(sk189 M H c)

noncomputable abbrev alpha189 (M H : Subgroup G) (c : G) :
    ↥(sk189 M H c) →* SKAlpha189 M H c :=
  QuotientGroup.mk' _

noncomputable abbrev kAlpha189 (M H : Subgroup G) (c : G) : Subgroup (SKAlpha189 M H c) :=
  ((normalClosureIn M c).subgroupOf (sk189 M H c)).map (alpha189 M H c)

noncomputable abbrev sAlpha189 (M H : Subgroup G) (c : G) : Subgroup (SKAlpha189 M H c) :=
  ((s189 M H).subgroupOf (sk189 M H c)).map (alpha189 M H c)

@[expose] def omegaOneTwo189 (S : Subgroup G) : Subgroup G :=
  Subgroup.closure {x | x ∈ S ∧ x ^ 2 = 1}

@[expose] def CoveredMod189 (M H : Subgroup G) (c : G) (X : Subgroup G) : Prop :=
  normalClosureIn M c ≤
    (normalClosureIn M c ⊓ Subgroup.normalizer (X : Set G)) ⊔ theta189 M H c

@[expose] def CoveredTwoMod189 (M H : Subgroup G) (c : G) (X : Subgroup G) : Prop :=
  normalClosureIn M c ≤
    ((normalClosureIn M c ⊓ Subgroup.normalizer (X : Set G)) ⊔
      (normalClosureIn M c ⊓ Subgroup.normalizer (Subgroup.zpowers c : Set G))) ⊔
      theta189 M H c

noncomputable abbrev imAlpha189 (M H : Subgroup G) (c : G) (X : Subgroup G) :
    Subgroup (SKAlpha189 M H c) :=
  (X.subgroupOf (sk189 M H c)).map (alpha189 M H c)

@[expose] def GeneratedModAlpha189 (M H : Subgroup G) (c : G) (X : Subgroup G) : Prop :=
  kAlpha189 M H c ≤
    (kAlpha189 M H c ⊓ Subgroup.normalizer (imAlpha189 M H c X : Set (SKAlpha189 M H c))) ⊔
      (kAlpha189 M H c ⊓ Subgroup.normalizer
        (imAlpha189 M H c (Subgroup.zpowers c) : Set (SKAlpha189 M H c)))

end Notation

@[expose] def IsRankOneType189 (X : Type) [Group X] : Prop :=
  (∃ (p f : ℕ) (_ : Fact p.Prime), p ≠ 3 ∧ 1 ≤ f ∧
      Nonempty (X ≃* projSL 2 (GaloisField p f))) ∨
  (∃ (p f : ℕ) (_ : Fact p.Prime), 1 ≤ f ∧ p ^ f % 3 = 2 ∧
      Nonempty (X ≃* projSL 3 (GaloisField p f))) ∨
  (∃ (p f : ℕ) (_ : Fact p.Prime), 1 ≤ f ∧ p ^ f % 3 = 1 ∧
      Nonempty (X ≃* projSU 3 p f)) ∨
  Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.J1)

section Cases

variable {G : Type} [Group G]

@[expose] def Case189i (M H : Subgroup G) (c : G) : Prop :=
  CFSG.ABGLocalTools.IsSylowOf 2 (sAlpha189 M H c) ⊤

@[expose] def Case189ii (M H : Subgroup G) (c : G) : Prop :=
  (∃ n : ℕ, Odd n ∧ Nonempty (↥(kAlpha189 M H c) ≃* projSL 2 (GaloisField 2 n))) ∧
    sAlpha189 M H c = ⊥

@[expose] def InnerFree189 (M H : Subgroup G) (c : G) : Prop :=
  sAlpha189 M H c ⊓
      (kAlpha189 M H c ⊔ Subgroup.centralizer (kAlpha189 M H c : Set (SKAlpha189 M H c))) ≤
    Subgroup.centralizer (kAlpha189 M H c : Set (SKAlpha189 M H c))

noncomputable abbrev outOrder189 {G : Type} [Group G] (M H : Subgroup G) (c : G) : ℕ :=
  (kAlpha189 M H c ⊔ Subgroup.centralizer (kAlpha189 M H c : Set (SKAlpha189 M H c))).index

@[expose] def Case189iii (M H : Subgroup G) (c : G) : Prop :=
  ∃ n e m : ℕ, 1 ≤ e ∧ Odd m ∧ n = 2 ^ e * m ∧ InnerFree189 M H c ∧
    ((Nonempty (↥(kAlpha189 M H c) ≃* projSL 2 (GaloisField 2 n)) ∧
        outOrder189 M H c = 2 ^ e) ∨
      (Nonempty (↥(kAlpha189 M H c) ≃* projSU 3 2 n) ∧ outOrder189 M H c = 2 ^ (e + 1)))

@[expose] def Case189iv (M H : Subgroup G) (c : G) : Prop :=
  (∃ n : ℕ, Odd n ∧ Nonempty (↥(kAlpha189 M H c) ≃* projSL 3 (GaloisField 2 n))) ∧
    ∃ K₁ : Subgroup (SKAlpha189 M H c), K₁ ≤ kAlpha189 M H c ∧
      IsMaxParabolicRankTwo (K₁.subgroupOf (kAlpha189 M H c)) ∧
      sAlpha189 M H c = CFSG.Open.pCoreOf 2 K₁

@[expose] def Case189v (M H : Subgroup G) (c : G) : Prop :=
  (∃ n : ℕ, Odd n ∧ Nonempty (↥(kAlpha189 M H c) ≃* projSL 3 (GaloisField 2 n))) ∧
    Nat.card (sAlpha189 M H c) = 2 ∧
    sAlpha189 M H c ⊓
        (kAlpha189 M H c ⊔ Subgroup.centralizer (kAlpha189 M H c : Set (SKAlpha189 M H c))) =
      ⊥

@[expose] def Case189vi (M H : Subgroup G) (c : G) : Prop :=
  (∃ (p f : ℕ) (_ : Fact p.Prime), p ≠ 2 ∧ 9 < p ^ f ∧
      Nonempty (↥(kAlpha189 M H c) ≃* projSL 2 (GaloisField p f))) ∨
  (∃ (p : ℕ) (_ : Fact p.Prime), 3 < p ∧
      ((p % 3 = 2 ∧ Nonempty (↥(kAlpha189 M H c) ≃* projSL 3 (GaloisField p 1))) ∨
        (p % 3 = 1 ∧ Nonempty (↥(kAlpha189 M H c) ≃* projSU 3 p 1))))

@[expose] def Cases1411189 (M H : Subgroup G) (c : G) : Prop :=
  (Case189iii M H c ∧ ¬ Nonempty (↥(kAlpha189 M H c) ≃* projSL 2 (GaloisField 2 2))) ∨
    Case189v M H c ∨ Case189vi M H c

end Cases

structure Setting189 (G : Type) [Group G] [Finite G] (A M H : Subgroup G) (c : G) : Prop
    extends Sec18H G A M H c where
  hyp187 : Hyp187 A M H c
  mem_thetaComponentsIn : normalClosureIn M c ∈ thetaComponentsIn M
  pRank_eq : CFSG.Open.pRank 3 (normalClosureIn M c) = 1
  rankOne : IsRankOneType189
    (↥(normalClosureIn M c) ⧸ aschbacherSolvableCore 3 ↥(normalClosureIn M c))
  not_le : ¬ normalClosureIn M c ≤ n189 H
  three : ∀ i j : Fin 4, i ≠ j →
    Subgroup.normalizer (fourChar (s189 M H) i : Set G) ≤ n189 H ∨
      Subgroup.normalizer (fourChar (s189 M H) j : Set G) ≤ n189 H
  sAlpha_ne : sAlpha189 M H c ≠ ⊥

@[expose] def Step189K0 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M H : Subgroup G) (c : G), Sec18H G A M H c →
    Hyp187 A M H c →
      normalClosureIn M c ∈ thetaComponentsIn M ∧ CFSG.Open.pRank 3 (normalClosureIn M c) = 1

@[expose] def Step189Two : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M H : Subgroup G) (c : G), Sec18H G A M H c →
    CFSG.Open.pRank 3 (normalClosureIn M c) = 1 →
      Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G)

@[expose] def Step189KType : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M H : Subgroup G) (c : G), Sec18H G A M H c →
    Hyp187 A M H c → normalClosureIn M c ∈ thetaComponentsIn M →
    CFSG.Open.pRank 3 (normalClosureIn M c) = 1 →
      IsRankOneType189
        (↥(normalClosureIn M c) ⧸ aschbacherSolvableCore 3 ↥(normalClosureIn M c))

@[expose] def Step189O2Bound : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M H : Subgroup G) (c : G), Sec18H G A M H c →
    Hyp187 A M H c → CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({c} : Set G)) = ⊥ →
      Nat.card ↥(CFSG.Open.pCoreOf 2 M ⊓ Subgroup.centralizer ({c} : Set G)) ≤ 2

@[expose] def Step189Q : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M H : Subgroup G) (c : G), Sec18H G A M H c →
    Hyp187 A M H c → normalClosureIn M c ∈ thetaComponentsIn M →
    CFSG.Open.pRank 3 (normalClosureIn M c) = 1 →
    CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({c} : Set G)) = ⊥ →
      inSubgroup (CFSG.pPrimeCore 3) (normalClosureIn M c) =
          CFSG.Open.pCoreOf 2 (normalClosureIn M c) ∧
        ∃ (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod 2) V) (_ : Finite V)
          (_ : Nontrivial V) (ρ : Representation (ZMod 2)
            (↥(normalClosureIn M c) ⧸ CFSG.pCore 2 ↥(normalClosureIn M c)) V),
          ∀ k : ↥(normalClosureIn M c), (k : G) = c → ∀ v : V,
            ρ (k : ↥(normalClosureIn M c) ⧸ CFSG.pCore 2 ↥(normalClosureIn M c)) v = v → v = 0

@[expose] def Step189List : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M H : Subgroup G) (c : G), Setting189 G A M H c →
    Case189i M H c ∨ Case189ii M H c ∨ Case189iii M H c ∨ Case189iv M H c ∨
      Case189v M H c ∨ Case189vi M H c

@[expose] def Step189NotNL : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M H : Subgroup G) (c : G), Sec18H G A M H c →
    Hyp187 A M H c → normalClosureIn M c ∈ thetaComponentsIn M →
    CFSG.Open.pRank 3 (normalClosureIn M c) = 1 → ¬ normalClosureIn M c ≤ n189 H

@[expose] def Step189FourNe : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M H : Subgroup G) (c : G), Sec18H G A M H c →
    Hyp187 A M H c → ∀ i : Fin 4, fourChar (s189 M H) i ≠ ⊥

@[expose] def Step189TwoRank : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M H : Subgroup G) (c : G), Sec18H G A M H c →
    Hyp187 A M H c → 3 ≤ CFSG.pRank 2 ↥(s189 M H)

@[expose] def Step189Three : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M H : Subgroup G) (c : G), Sec18H G A M H c →
    Hyp187 A M H c → ∀ i j : Fin 4, i ≠ j →
      Subgroup.normalizer (fourChar (s189 M H) i : Set G) ≤ n189 H ∨
        Subgroup.normalizer (fourChar (s189 M H) j : Set G) ≤ n189 H

@[expose] def Step189SNe : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M H : Subgroup G) (c : G), Sec18H G A M H c →
    Hyp187 A M H c → ¬ normalClosureIn M c ≤ n189 H → sAlpha189 M H c ≠ ⊥

@[expose] def Step189OddL2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M H : Subgroup G) (c : G), Setting189 G A M H c →
    ∀ n : ℕ, Odd n → ¬ Nonempty (↥(kAlpha189 M H c) ≃* projSL 2 (GaloisField 2 n))

@[expose] def Step189InspectI : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M H : Subgroup G) (c : G), Setting189 G A M H c →
    Case189i M H c → CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({c} : Set G)) ≠ ⊥ →
      GeneratedModAlpha189 M H c (s189 M H)

@[expose] def Step189IndexI : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M H : Subgroup G) (c : G), Setting189 G A M H c →
    Case189i M H c → CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({c} : Set G)) = ⊥ →
    (∃ n : ℕ, Nonempty (↥(kAlpha189 M H c) ≃* projSL 2 (GaloisField 2 n))) →
      ¬ 4 ∣ (M ⊓ n189 H).relIndex M

@[expose] def Asc82Item1411And1412 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M H : Subgroup G) (c : G), Setting189 G A M H c →
    Cases1411189 M H c →
      (∃ i j : Fin 4, i ≠ j ∧ CoveredMod189 M H c (fourChar (s189 M H) i) ∧
          CoveredMod189 M H c (fourChar (s189 M H) j)) ∨
        (Nonempty (↥(kAlpha189 M H c) ≃* projSL 2 (GaloisField 2 4)) ∧
          2 < Nat.card ↥(CFSG.Open.pCoreOf 2 M ⊓ Subgroup.centralizer ({c} : Set G)))

@[expose] def Step189L16 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M H : Subgroup G) (c : G), Setting189 G A M H c →
    Cases1411189 M H c → Nonempty (↥(kAlpha189 M H c) ≃* projSL 2 (GaloisField 2 4)) →
    2 < Nat.card ↥(CFSG.Open.pCoreOf 2 M ⊓ Subgroup.centralizer ({c} : Set G)) →
      CoveredTwoMod189 M H c (omegaOneTwo189 (s189 M H))

@[expose] def Step189L4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M H : Subgroup G) (c : G), Setting189 G A M H c →
    Case189iii M H c → Nonempty (↥(kAlpha189 M H c) ≃* projSL 2 (GaloisField 2 2)) →
      ¬ 4 ∣ (M ⊓ n189 H).relIndex M

@[expose] def Step189O3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M H : Subgroup G) (c : G), Setting189 G A M H c →
    ((∃ n : ℕ, Even n ∧ 0 < n ∧
        Nonempty (↥(kAlpha189 M H c) ≃* projSL 2 (GaloisField 2 n))) ∨
      Case189iv M H c) →
      inSubgroup (CFSG.pPrimeCore 3) (normalClosureIn M c) =
        CFSG.Open.pCoreOf 2 (normalClosureIn M c)

end CFSG.RankThree.PartTwo.Sec18
