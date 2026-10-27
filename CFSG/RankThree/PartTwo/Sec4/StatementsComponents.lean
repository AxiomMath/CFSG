module

public import CFSG.RankThree.PartTwo.Sec4.Vocabulary
public import CFSG.RankThree.PartTwo.KFacts.AutKindsStd
public import CFSG.RankThree.PartTwo.Sec4.Statements

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.KFacts
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

@[expose] def IsChevTwoRankTwoModel (X : Type) [Group X] : Prop :=
  (∃ n : ℕ, 1 ≤ n ∧
    (Nonempty (X ≃* projSL 2 (GaloisField 2 n)) ∨ Nonempty (X ≃* projSL 3 (GaloisField 2 n)) ∨
      Nonempty (X ≃* projSU 3 2 n) ∨ Nonempty (X ≃* projSp 2 (GaloisField 2 n)) ∨
      Nonempty (X ≃* projSU 4 2 n))) ∨
  ∃ f : ℕ, Blueprint.ChevalleyExceptionalModel X .G2 2 f ∨
    Blueprint.ChevalleyExceptionalModel X .trialityD4 2 f ∨ Blueprint.SuzukiModel X 2 f ∨
    Blueprint.ReeTitsModel X .twistedF4 2 f ∨ Blueprint.ReeTitsModel X .Tits 2 f

@[expose] def IsHeisThree (P : Type) [Group P] : Prop :=
  IsExtraspecialPGroup 3 P ∧ Nat.card P = 27 ∧ Monoid.exponent P = 3

@[expose] def sporadics46 : List TauCeti.SporadicName :=
  [.M11, .M12, .M22, .M23, .M24, .J1, .J2, .J3, .J4, .McL, .HS, .He, .Ru]

@[expose] def sporadicCovers46 : List TauCeti.SporadicName :=
  [.M22, .J3, .McL, .ONan]

@[expose] def IsList46 (X : Type) [Group X] : Prop :=
  (∃ (p e : ℕ) (_ : Fact p.Prime), p ≠ 2 ∧ 1 ≤ e ∧
      Nonempty (X ≃* projSL 2 (GaloisField p e))) ∨
  (∃ (p e : ℕ) (_ : Fact p.Prime), 3 < p ∧ 1 ≤ e ∧ e ≤ 2 ∧
      (IsSLThreeEpsAt X (p ^ e) ∨ Nonempty (X ≃* projSL 3 (GaloisField p e)) ∨
        Nonempty (X ≃* projSU 3 p e))) ∨
  (∃ (p : ℕ) (_ : Fact p.Prime), 3 < p ∧
      (Blueprint.ChevalleyExceptionalModel X .G2 p 1 ∨
        Nonempty (X ≃* projSp 2 (GaloisField p 1)) ∨
        (p % 3 = 1 ∧ Nonempty (X ≃* projSU 4 p 1)) ∨
        (p % 3 = 2 ∧ Nonempty (X ≃* projSL 4 (GaloisField p 1))))) ∨
  ((∃ n : ℕ, n ≤ 9 ∧ Nonempty (X ≃* alternatingGroup (Fin n))) ∨
      IsExtOf X (alternatingGroup (Fin 6)) (Multiplicative (ZMod 3)) ∨
      IsExtOf X (alternatingGroup (Fin 7)) (Multiplicative (ZMod 3))) ∨
  ((∃ s ∈ sporadics46, Nonempty (X ≃* Blueprint.NativeSporadic.Carrier s)) ∨
      ∃ s ∈ sporadicCovers46,
        IsExtOf X (Blueprint.NativeSporadic.Carrier s) (Multiplicative (ZMod 3))) ∨
  (IsChevTwoRankTwoModel X ∨ ∃ n : ℕ, 1 ≤ n ∧ IsSLThreeEpsAt X (2 ^ n)) ∨
  (Nonempty (X ≃* projSL 5 (GaloisField 2 1)) ∨ Nonempty (X ≃* projSp 3 (GaloisField 2 1)) ∨
      Nonempty (X ≃* projSU 5 2 2)) ∨
  ((∃ e : ℕ, 1 ≤ e ∧ e ≤ 2 ∧
        (Nonempty (X ≃* projSL 3 (GaloisField 3 e)) ∨ Nonempty (X ≃* projSU 3 3 e))) ∨
      Nonempty (X ≃* projSL 4 (GaloisField 3 1)) ∨
      (Nat.card (Subgroup.center X) ≤ 3 ∧
        (Blueprint.ChevalleyExceptionalModel (X ⧸ Subgroup.center X) .G2 3 1 ∨
          Nonempty (X ⧸ Subgroup.center X ≃* projSU 4 3 1))))

@[expose] def Item4_6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], SectionFourHyp G → 3 ∣ Nat.card (Subgroup.center G) →
    ∀ L ∈ thetaComponents 3 G, IsList46 (L ⧸ aschbacherSolvableCore 3 L)

@[expose] def IsTriple413 {G : Type} [Group G] (L A E : Subgroup G) (c : G) : Prop :=
  Maximal (fun B : Subgroup G => CFSG.Assembly.IsElemAbelian 3 B) A ∧
    A ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers c ∧ orderOf c = 3 ∧
    Late.IsE27 E ∧ E ≤ A ∧
    ∃ T ∈ invariantPiSubgroups ⊤ E (piOf 2), ¬ T ≤ Subgroup.centralizer (E : Set G)

@[expose] def Alt413 {G : Type} [Group G] [Finite G] (L A E : Subgroup G) (c : G) : Prop :=
  (∃ e ∈ E, ∃ m : ℕ, 2 < m ∧ Nonempty (L ≃* projSL 2 (GaloisField 3 (3 * m))) ∧
      InducesStdKind L e .field) ∨
  (A ≤ L ∧ ∃ (K : Subgroup L) (_ : K.Normal), K.map L.subtype = Subgroup.zpowers c ∧
      (Nonempty (L ⧸ K ≃* projSU 4 3 1) ∨ Nonempty (L ⧸ K ≃* Blueprint.NativeSporadic.McL))) ∨
  (A = Subgroup.zpowers c ⊔ (A ⊓ L) ∧ Subgroup.zpowers c ⊓ (A ⊓ L) = ⊥ ∧
      (Blueprint.ChevalleyExceptionalModel L .G2 3 1 ∨
        Nonempty (L ≃* Blueprint.NativeSporadic.McL) ∨
        Nonempty (L ≃* projSL 4 (GaloisField 3 1)) ∨ Nonempty (L ≃* projSU 4 3 1)))

@[expose] def Item4_13 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], SectionFourHyp G → ∀ L : Subgroup G, IsComponent L →
    ((∃ (A E : Subgroup G) (c : G), IsTriple413 L A E c ∧ 4 < CFSG.Open.pRank 3 A) ↔
      ∃ (A E : Subgroup G) (c : G), IsTriple413 L A E c ∧ Alt413 L A E c)

@[expose] def Item4_13_forward : Prop :=
  ∀ (G : Type) [Group G] [Finite G], SectionFourHyp G → ∀ L : Subgroup G, IsComponent L →
    ∀ (A E : Subgroup G) (c : G), IsTriple413 L A E c → 4 < CFSG.Open.pRank 3 A →
      Alt413 L A E c

@[expose] def Item4_29 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], SectionFourHyp G → aschbacherSolvableCore 3 G = ⊥ →
    partTwoE G = partTwoF G → ∀ A : Subgroup G, Late.IsE27 A → ∀ c ∈ A, c ≠ 1 →
    ∀ L : Subgroup G, IsComponent L →
    ∀ K : Subgroup (L ⊓ Subgroup.centralizer {c} : Subgroup G), IsComponent K →
    ∀ K' : Subgroup G, K' = K.map (L ⊓ Subgroup.centralizer {c}).subtype →
      ((∃ (p e : ℕ) (_ : Fact p.Prime), 1 ≤ e ∧ IsoLThreePi (K ⧸ CFSG.pCore 2 K) p e) ∨
        Nonempty (K ⧸ CFSG.pCore 2 K ≃* alternatingGroup (Fin 7)) ∨
        Nonempty (K ⧸ CFSG.pCore 2 K ≃* Blueprint.NativeSporadic.M12) ∨
        Nonempty (K ⧸ CFSG.pCore 2 K ≃* Blueprint.NativeSporadic.M22) ∨
        Nonempty (K ⧸ CFSG.pCore 2 K ≃* Blueprint.NativeSporadic.J2)) →
      Subgroup.zpowers c = A ⊓ Subgroup.centralizer (K' : Set G) →
      K' = L ∨
      (Nonempty (K ≃* alternatingGroup (Fin 7)) ∧ Nonempty (L ≃* alternatingGroup (Fin 10))) ∨
      (∃ n : ℕ, 1 ≤ n ∧ IsoLThreePi K 2 n ∧ IsoLThreePi L 2 (3 * n) ∧
        InducesStdKind L c .field) ∨
      (∃ n : ℕ, 1 ≤ n ∧ IsoLThreePi K 2 n ∧ Blueprint.ChevalleyExceptionalModel L .trialityD4 2 n ∧
        InducesStdKind L c .graphField)

end CFSG.RankThree.PartTwo.Sec4
