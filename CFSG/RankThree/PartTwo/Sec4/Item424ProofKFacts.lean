module

public import CFSG.RankThree.PartTwo.Sec4.Item424ProofStatement
public import CFSG.RankThree.PartTwo.Sec11.Item119

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projImage projSL projSU projSp)
open CFSG.GorensteinWalter (PSL2)

@[expose] def IsSLThreePiAny (X : Type) [Group X] : Prop :=
  IsSLThreePi X ∨ ∃ (p e : ℕ) (_ : Fact p.Prime), 1 ≤ e ∧ IsoLThreePi X p e

@[expose] def IsFieldCent424 (X : Type) [Group X] : Prop :=
  (∃ (K : Type) (_ : Field K) (_ : Finite K), (3 : K) ≠ 0 ∧ Nonempty (X ≃* PSL2 K)) ∨
    ∃ n : ℕ, 1 ≤ n ∧ Sec8.IsoLThreeMinusPi X 2 (3 * n)

@[expose] def IsList46One (X : Type) [Group X] : Prop :=
  ∃ (p e : ℕ) (_ : Fact p.Prime), p ≠ 2 ∧ 1 ≤ e ∧ Nonempty (X ≃* projSL 2 (GaloisField p e))

@[expose] def IsList46Two (X : Type) [Group X] : Prop :=
  ∃ (p e : ℕ) (_ : Fact p.Prime), 3 < p ∧ 1 ≤ e ∧ e ≤ 2 ∧
    (IsSLThreeEpsAt X (p ^ e) ∨ Nonempty (X ≃* projSL 3 (GaloisField p e)) ∨
      Nonempty (X ≃* projSU 3 p e))

@[expose] def IsList46Three (X : Type) [Group X] : Prop :=
  ∃ (p : ℕ) (_ : Fact p.Prime), 3 < p ∧
    (Blueprint.ChevalleyExceptionalModel X .G2 p 1 ∨
      Nonempty (X ≃* projSp 2 (GaloisField p 1)) ∨
      (p % 3 = 1 ∧ Nonempty (X ≃* projSU 4 p 1)) ∨
      (p % 3 = 2 ∧ Nonempty (X ≃* projSL 4 (GaloisField p 1))))

@[expose] def IsList46Four (X : Type) [Group X] : Prop :=
  (∃ n : ℕ, n ≤ 9 ∧ Nonempty (X ≃* alternatingGroup (Fin n))) ∨
    IsExtOf X (alternatingGroup (Fin 6)) (Multiplicative (ZMod 3)) ∨
    IsExtOf X (alternatingGroup (Fin 7)) (Multiplicative (ZMod 3))

@[expose] def IsList46Five (X : Type) [Group X] : Prop :=
  (∃ s ∈ sporadics46, Nonempty (X ≃* Blueprint.NativeSporadic.Carrier s)) ∨
    ∃ s ∈ sporadicCovers46,
      IsExtOf X (Blueprint.NativeSporadic.Carrier s) (Multiplicative (ZMod 3))

@[expose] def IsList46Six (X : Type) [Group X] : Prop :=
  IsChevTwoRankTwoModel X ∨ ∃ n : ℕ, 1 ≤ n ∧ IsSLThreeEpsAt X (2 ^ n)

@[expose] def IsList46Seven (X : Type) [Group X] : Prop :=
  Nonempty (X ≃* projSL 5 (GaloisField 2 1)) ∨ Nonempty (X ≃* projSp 3 (GaloisField 2 1)) ∨
    Nonempty (X ≃* projSU 5 2 2)

@[expose] def IsList46Eight (X : Type) [Group X] : Prop :=
  (∃ e : ℕ, 1 ≤ e ∧ e ≤ 2 ∧
      (Nonempty (X ≃* projSL 3 (GaloisField 3 e)) ∨ Nonempty (X ≃* projSU 3 3 e))) ∨
    Nonempty (X ≃* projSL 4 (GaloisField 3 1)) ∨
    (Nat.card (Subgroup.center X) ≤ 3 ∧
      (Blueprint.ChevalleyExceptionalModel (X ⧸ Subgroup.center X) .G2 3 1 ∨
        Nonempty (X ⧸ Subgroup.center X ≃* projSU 4 3 1)))

theorem isList46_iff (X : Type) [Group X] :
    IsList46 X ↔ IsList46One X ∨ IsList46Two X ∨ IsList46Three X ∨ IsList46Four X ∨
      IsList46Five X ∨ IsList46Six X ∨ IsList46Seven X ∨ IsList46Eight X :=
  Iff.rfl

structure Config424 (G : Type) [Group G] [Finite G] (A L : Subgroup G) (a c : G)
    (K : Subgroup G) : Prop where
  sectionFourHyp : SectionFourHyp G
  maximal : Maximal (fun B : Subgroup G => CFSG.Assembly.IsElemAbelian 3 B) A
  card_eq : Nat.card A = 27
  mem_thetaComponents : L ∈ thetaComponents 3 G
  orderOf_a : orderOf a = 3
  a_mem_center : a ∈ Subgroup.center G
  sectionCentralizer_eq : Late.sectionCentralizer A L ((aschbacherSolvableCore 3 L).map L.subtype) =
    (Subgroup.zpowers a : Set G)
  c_mem : c ∈ A
  c_not_mem : c ∉ Subgroup.zpowers a
  mem_thetaComponentsIn : K ∈ thetaComponentsIn (L ⊓ Subgroup.centralizer ({c} : Set G))
  isType424 : Sec11.IsType424 (K ⧸ aschbacherSolvableCore 3 K)
  normalizer_le : Subgroup.normalizer (A : Set G) ≤
    Subgroup.normalizer ((A ⊓ K : Subgroup G) : Set G)

structure InnerConfig424 (X : Type) [Group X] [Finite X] (D : Subgroup X) (c d : X)
    (K : Subgroup X) : Prop where
  maximal : Maximal (fun B : Subgroup X => CFSG.Assembly.IsElemAbelian 3 B) D
  card_eq : Nat.card D = 9
  c_mem : c ∈ D
  c_ne_one : c ≠ 1
  d_mem : d ∈ D
  d_not_mem : d ∉ Subgroup.zpowers c
  mem_thetaComponentsIn : K ∈ thetaComponentsIn (Subgroup.centralizer ({c} : Set X))
  d_mem_K : d ∈ K
  isType424 : Sec11.IsType424 (K ⧸ aschbacherSolvableCore 3 K)
  normalizer_le : Subgroup.normalizer (D : Set X) ≤
    Subgroup.normalizer (Subgroup.zpowers d : Set X)

@[expose] def Census424 (X : Type) [Group X] [Finite X] : Prop :=
  ∀ (D : Subgroup X) (c d : X) (K : Subgroup X), InnerConfig424 X D c d K →
    IsList424 X ∧ (Nonempty (autIn (⊤ : Subgroup X) D ≃* Equiv.Perm (Fin 3)) ∨
      Nonempty (autIn (⊤ : Subgroup X) D ≃* DihedralGroup 6))

@[expose] def K424TrialityOuter : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L K : Subgroup G) (c : G) (n : ℕ),
    Blueprint.ChevalleyExceptionalModel (L ⧸ aschbacherSolvableCore 3 L) .trialityD4 2 n →
    InducesOuterTheta c L → c ^ 3 = 1 →
    K ∈ thetaComponentsIn (L ⊓ Subgroup.centralizer ({c} : Set G)) →
      ¬ Sec11.IsType424 (K ⧸ aschbacherSolvableCore 3 K)

@[expose] def K424CoverCent : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L K : Subgroup G) (c : G),
    IsList46 (L ⧸ aschbacherSolvableCore 3 L) → IsQuasisimple (L ⧸ aschbacherSolvableCore 3 L) →
    Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) ≠ ⊥ →
    ¬ IsSLThreePi (L ⧸ aschbacherSolvableCore 3 L) →
    c ∈ Subgroup.normalizer (L : Set G) → c ^ 3 = 1 → ¬ InducesOuterTheta c L →
    c ∉ thetaQuotCentralizer L →
    K ∈ thetaComponentsIn (L ⊓ Subgroup.centralizer ({c} : Set G)) →
      ¬ Sec11.IsType424 (K ⧸ aschbacherSolvableCore 3 K)

@[expose] def K424Inner46One : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsList46One X → IsQuasisimple X →
    Subgroup.center X = ⊥ → ¬ IsSLThreePiAny X → Census424 X

@[expose] def K424Inner46Two : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsList46Two X → IsQuasisimple X →
    Subgroup.center X = ⊥ → ¬ IsSLThreePiAny X → Census424 X

@[expose] def K424Inner46Three : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsList46Three X → IsQuasisimple X →
    Subgroup.center X = ⊥ → ¬ IsSLThreePiAny X → Census424 X

@[expose] def K424Inner46Four : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsList46Four X → IsQuasisimple X →
    Subgroup.center X = ⊥ → ¬ IsSLThreePiAny X → Census424 X

@[expose] def K424Inner46Five : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsList46Five X → IsQuasisimple X →
    Subgroup.center X = ⊥ → ¬ IsSLThreePiAny X → Census424 X

@[expose] def K424Inner46Six : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsList46Six X → IsQuasisimple X →
    Subgroup.center X = ⊥ → ¬ IsSLThreePiAny X → Census424 X

@[expose] def K424Inner46Seven : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsList46Seven X → IsQuasisimple X →
    Subgroup.center X = ⊥ → ¬ IsSLThreePiAny X → Census424 X

@[expose] def K424Inner46Eight : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsList46Eight X → IsQuasisimple X →
    Subgroup.center X = ⊥ → ¬ IsSLThreePiAny X → Census424 X

@[expose] def K424InnerCensus : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsList46 X → IsQuasisimple X →
    Subgroup.center X = ⊥ → ¬ IsSLThreePiAny X → Census424 X

theorem k424InnerCensus_of (h1 : K424Inner46One) (h2 : K424Inner46Two) (h3 : K424Inner46Three)
    (h4 : K424Inner46Four) (h5 : K424Inner46Five) (h6 : K424Inner46Six)
    (h7 : K424Inner46Seven) (h8 : K424Inner46Eight) : K424InnerCensus := by
  intro X _ _ hX hq hZ hSL
  rcases (isList46_iff X).mp hX with h | h | h | h | h | h | h | h
  · exact h1 X h hq hZ hSL
  · exact h2 X h hq hZ hSL
  · exact h3 X h hq hZ hSL
  · exact h4 X h hq hZ hSL
  · exact h5 X h hq hZ hSL
  · exact h6 X h hq hZ hSL
  · exact h7 X h hq hZ hSL
  · exact h8 X h hq hZ hSL

section Kinds


@[expose] def K424FieldCent : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L K : Subgroup G) (c : G),
    KFacts.InducesStdKind L c .field → c ^ 3 = 1 →
    K ∈ thetaComponentsIn (L ⊓ Subgroup.centralizer ({c} : Set G)) →
    Sec11.IsType424 (K ⧸ aschbacherSolvableCore 3 K) →
      IsFieldCent424 (L ⧸ aschbacherSolvableCore 3 L)

@[expose] def K424SLThree : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A L : Subgroup G) (a c : G) (K : Subgroup G),
    Config424 G A L a c K → IsSLThreePiAny (L ⧸ aschbacherSolvableCore 3 L) →
    (¬ InducesOuterTheta c L ∨ KFacts.InducesStdKind L c .diagonal) →
      Nonempty (autIn L A ≃* Equiv.Perm (Fin 3)) ∧
        (Sec8.IsZ3LThreePi (thetaImage (L ⊔ A)) ∨ Sec8.IsZ3PGLThreePi (thetaImage (L ⊔ A)))

end Kinds

end CFSG.RankThree.PartTwo.Sec4
