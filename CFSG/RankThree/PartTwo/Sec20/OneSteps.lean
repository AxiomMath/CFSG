module

public import CFSG.RankThree.PartTwo.Sec20.One

public section

namespace CFSG.RankThree.PartTwo.Sec20

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late
open CFSG.Assembly.RankThreeEven (projSL)

@[expose] def Step189O2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M H : Subgroup G) (c : G), Sec18.Sec18H G A M H c →
    Sec18.Hyp187 A M H c → CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({c} : Set G)) = ⊥ →
      ∃ n : ℕ, 0 < n ∧ Nonempty (normalClosureIn M c ⧸ CFSG.pCore 2 (normalClosureIn M c) ≃*
        projSL 2 (GaloisField 2 n))

@[expose] def Step2051Index : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M L N : Subgroup G) (c : G) (T : Subgroup G),
    Ctx20One G A M L N c T →
    (∃ n : ℕ, Odd n ∧ Nonempty (kTwenty M c ⧸ CFSG.pCore 2 (kTwenty M c) ≃*
        projSL 3 (GaloisField 2 n)) ∧
      Sec18.IsMaxParabolicRankTwo (((kTwenty M c ⊓ N).subgroupOf (kTwenty M c)).map
        (QuotientGroup.mk' (CFSG.pCore 2 (kTwenty M c))))) →
      ¬ 4 ∣ (M ⊓ N).relIndex M

@[expose] def Step2051Sylow : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M L N : Subgroup G) (c : G) (T : Subgroup G),
    Ctx20One G A M L N c T → ∀ R : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 2 R N →
      CFSG.ABGLocalTools.IsSylowOf 2 (R ⊓ M) (M ⊓ N) → (R ⊓ M).relIndex R = 8

@[expose] def Step2053L2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M L N : Subgroup G) (c : G) (T : Subgroup G),
    Ctx20One G A M L N c T →
    (∀ C : Subgroup T, C.Characteristic → C ≠ ⊥ →
      ¬ kTwenty M c ⊔ T ≤ Subgroup.normalizer ((C.map T.subtype : Subgroup G) : Set G)) →
    ∀ n : ℕ, Even n → 0 < n →
      Nonempty (kTwenty M c ⧸ CFSG.pCore 2 (kTwenty M c) ≃* projSL 2 (GaloisField 2 n)) →
      ¬ 4 ∣ (M ⊓ N).relIndex M → False

@[expose] def Step204Normal : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M L N : Subgroup G) (c : G) (T : Subgroup G),
    Ctx20One G A M L N c T →
    M ≤ Subgroup.normalizer (((A ⊓ L) ⊔ CFSG.Open.pCoreOf 2 M : Subgroup G) : Set G) →
    Sec4.HasSection (Sec4.autIn M (A ⊓ L)) (QuaternionGroup 2) →
      ∃ i j : Fin 4, i ≠ j ∧ i ≠ 3 ∧ j ≠ 3 ∧
        Sec18.fourChar (CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T)) i ≠ ⊥ ∧
        Sec18.fourChar (CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T)) j ≠ ⊥ ∧
        kTwenty M c ⊔ A ⊔ T ≤ Subgroup.normalizer
          (Sec18.fourChar (CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T)) i : Set G) ∧
        kTwenty M c ⊔ A ⊔ T ≤ Subgroup.normalizer
          (Sec18.fourChar (CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T)) j : Set G)

noncomputable abbrev yTwenty {G : Type} [Group G] (X : Subgroup G) (c : G) : Subgroup G :=
  normalClosureIn X c

noncomputable abbrev oThreePrimeYR {G : Type} [Group G] (M X T : Subgroup G) (c : G) :
    Subgroup G :=
  inSubgroup (CFSG.pPrimeCore 3) (yTwenty X c ⊔ CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T))

noncomputable abbrev yAlpha {G : Type} [Group G] (M X T : Subgroup G) (c : G) :
    haveI := CFSG.pPrimeCore_normal (p := 3)
      (G := ↥(yTwenty X c ⊔ CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T)))
    Subgroup (↥(yTwenty X c ⊔ CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T)) ⧸
      CFSG.pPrimeCore 3 ↥(yTwenty X c ⊔ CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T))) :=
  haveI := CFSG.pPrimeCore_normal (p := 3)
    (G := ↥(yTwenty X c ⊔ CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T)))
  ((yTwenty X c).subgroupOf (yTwenty X c ⊔ CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T))).map
    (QuotientGroup.mk' (CFSG.pPrimeCore 3
      ↥(yTwenty X c ⊔ CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T))))

structure Setting204 (G : Type) [Group G] [Finite G] (A M L N : Subgroup G) (c : G)
    (T : Subgroup G) (i j : Fin 4) (P : Subgroup G) : Prop extends Ctx20 G A M L N c T where
  ne : i ≠ j
  ne_three_left : i ≠ 3
  ne_three_right : j ≠ 3
  normal_left : kTwenty M c ⊔ A ⊔ T ≤ Subgroup.normalizer
    (Sec18.fourChar (CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T)) i : Set G)
  normal_right : kTwenty M c ⊔ A ⊔ T ≤ Subgroup.normalizer
    (Sec18.fourChar (CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T)) j : Set G)
  normalizer_left : Subgroup.normalizer
    (Sec18.fourChar (CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T)) i : Set G) ≤ M
  normalizer_right : Subgroup.normalizer
    (Sec18.fourChar (CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T)) j : Set G) ≤ M
  maxInvariant : CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T) ∈
    maxInvariantPiSubgroups ⊤ (kTwenty M c ⊔ T) (piOf 2)
  normalizer_le : Subgroup.normalizer (CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T) : Set G) ≤
    Subgroup.normalizer (kTwenty M c : Set G)
  mem_oTwoComponentsIn : kTwenty M c ∈ oTwoComponentsIn M
  not_le : ¬ kTwenty M c ≤ N
  kType : (∃ n : ℕ, Odd n ∧ Nonempty (kTwenty M c ⧸ CFSG.pCore 2 (kTwenty M c) ≃*
      projSL 3 (GaloisField 2 n))) ∨
    (∃ n : ℕ, Even n ∧ 0 < n ∧ Nonempty (kTwenty M c ⧸ CFSG.pCore 2 (kTwenty M c) ≃*
      projSL 2 (GaloisField 2 n)))
  sylow_normalizer : CFSG.ABGLocalTools.IsSylowOf 3 P (Subgroup.normalizer (A : Set G))
  sylow_top : CFSG.ABGLocalTools.IsSylowOf 3 P ⊤
  conjugatesIn_eq : Sec18.conjugatesIn (Subgroup.zpowers c) P = {Subgroup.zpowers c}
  normalizer_A : Subgroup.normalizer (A : Set G) ≤
    Subgroup.normalizer (Subgroup.zpowers c : Set G)
  omegaOne : IsE27 (Sec18.omegaOneThree P) ∨ Sec18.IsZ3TimesHeis (Sec18.omegaOneThree P)
  not_mem_frattini : c ∉ (frattini (Sec18.omegaOneThree P)).map (Sec18.omegaOneThree P).subtype
  one_of_L2 : (∃ X ∈ scriptM ((kTwenty M c ⊔ T : Subgroup G) : Set G), X ≠ M ∧
      CFSG.Open.pRank 3 (yTwenty X c) ≤ 1 ∧
      ∃ m : ℕ, Nonempty (↥(yAlpha M X T c) ≃* projSL 2 (GaloisField 2 m))) →
    ∃ H ∈ scriptHStar A M, CFSG.Open.pCoreOf 2 H ≠ ⊥ ∧ L = inSubgroup perfectResidual H ∧
      N = Subgroup.normalizer (L : Set G) ∧
      (CFSG.Open.pCoreOf 2 (Subgroup.centralizer {c}) ≠ ⊥ →
        Subgroup.normalizer (Subgroup.zpowers c : Set G) ≤ N)

@[expose] def CoveredByNormalizer {G : Type} [Group G] (M X T : Subgroup G) (c : G) (k : Fin 4) :
    Prop :=
  yTwenty X c ≤ (yTwenty X c ⊓ Subgroup.normalizer
    (Sec18.fourChar (CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T)) k : Set G)) ⊔ oThreePrimeYR M X T c

@[expose] def Step204Cyclic : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M L N : Subgroup G) (c : G) (T : Subgroup G)
    (i j : Fin 4) (P : Subgroup G), Setting204 G A M L N c T i j P →
      ∀ X ∈ scriptM ((kTwenty M c ⊔ T : Subgroup G) : Set G), X ≠ M →
        CFSG.Open.pRank 3 (yTwenty X c) ≤ 1

@[expose] def Step204Asc1411 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M L N : Subgroup G) (c : G) (T : Subgroup G)
    (i j : Fin 4) (P : Subgroup G), Setting204 G A M L N c T i j P →
      ∀ X ∈ scriptM ((kTwenty M c ⊔ T : Subgroup G) : Set G), X ≠ M →
        CFSG.Open.pRank 3 (yTwenty X c) ≤ 1 →
        (∀ m : ℕ, ¬ Nonempty (↥(yAlpha M X T c) ≃* projSL 2 (GaloisField 2 m))) →
          CoveredByNormalizer M X T c i ∨ CoveredByNormalizer M X T c j

@[expose] def Step204Final : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M L N : Subgroup G) (c : G) (T : Subgroup G)
    (i j : Fin 4) (P : Subgroup G), Setting204 G A M L N c T i j P →
      ∀ X ∈ scriptM ((kTwenty M c ⊔ T : Subgroup G) : Set G), X ≠ M →
        CFSG.Open.pRank 3 (yTwenty X c) ≤ 1 →
        (CoveredByNormalizer M X T c i ∨ CoveredByNormalizer M X T c j ∨
          ∃ m : ℕ, Nonempty (↥(yAlpha M X T c) ≃* projSL 2 (GaloisField 2 m))) → False

@[expose] def Step204Rest : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M L N : Subgroup G) (c : G) (T : Subgroup G)
    (i j : Fin 4) (P : Subgroup G), Setting204 G A M L N c T i j P →
      ∀ X ∈ scriptM ((kTwenty M c ⊔ T : Subgroup G) : Set G), X = M

@[expose] def Step209V : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M L N : Subgroup G) (c : G) (T : Subgroup G),
    Ctx20One G A M L N c T → T ≤ N →
    kTwenty M c ⊓ Subgroup.centralizer (zTwenty T : Set G) ≤ N →
    (IsBlock M (kTwenty M c) ∧ vTwenty M c T = CFSG.Open.pCoreOf 2 (kTwenty M c) ∧
      ∃ n : ℕ, Odd n ∧ IsNaturalL3Module (kTwenty M c) (vTwenty M c T) n) →
      vTwenty M c T ≤ normalClosureIn (kTwenty M c ⊓ N) c

@[expose] def Step209L : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M L N : Subgroup G) (c : G) (T : Subgroup G),
    Ctx20One G A M L N c T → T ≤ N →
    kTwenty M c ⊓ Subgroup.centralizer (zTwenty T : Set G) ≤ N →
    (IsBlock M (kTwenty M c) ∧ vTwenty M c T = CFSG.Open.pCoreOf 2 (kTwenty M c) ∧
      ∃ n : ℕ, Odd n ∧ IsNaturalL3Module (kTwenty M c) (vTwenty M c T) n) →
      ⁅L, normalClosureIn (kTwenty M c ⊓ N) c⁆ = ⊥

end CFSG.RankThree.PartTwo.Sec20
