module

public import CFSG.RankThree.PartTwo.Sec8.Groups
public import CFSG.RankThree.PartTwo.Sec8.Pairs
public import CFSG.RankThree.PartTwo.Sec8.Statements

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

variable {G : Type} [Group G]

@[expose] def Cases83 [Finite G] (L : Subgroup G) (a : G) (A₀ : Subgroup G) (d : G) (n : ℕ) :
    Prop :=
  ((IsoTrialityD4 (L ⧸ aschbacherSolvableCore 3 L) n ∨
        IsoGTwoEven (L ⧸ aschbacherSolvableCore 3 L) (3 * n)) ∧
      Nonempty (imageModTheta L (inSubgroup perfectResidual (L ⊓ Subgroup.centralizer {d})) ≃*
        projSL 2 (GaloisField 2 (3 * n))) ∧
      (IsoGTwoEven (barCentralizer (Subgroup.zpowers a) L) n ∨
        (IsoTrialityD4 (L ⧸ aschbacherSolvableCore 3 L) n ∧
          IsoPGUThree (barCentralizer (Subgroup.zpowers a) L) (2 ^ n) ∧
          ∃ a₀ ∈ A₀, a₀ ≠ 1 ∧ KFacts.InducesStdKind L a₀ .graphField ∧
            IsoGTwoEven (barCentralizer (Subgroup.zpowers a₀) L) n))) ∨
    (IsoReeF4 (L ⧸ aschbacherSolvableCore 3 L) (3 * n) ∧
      IsoReeF4 (barCentralizer (Subgroup.zpowers a) L) n ∧
      IsoSUThree (imageModTheta L (inSubgroup perfectResidual (L ⊓ Subgroup.centralizer {d})))
        (2 ^ (3 * n))) ∨
    (IsoSUThree (L ⧸ aschbacherSolvableCore 3 L) (2 ^ (3 * n)) ∧
      IsoSUThree (barCentralizer (Subgroup.zpowers a) L) (2 ^ n) ∧
      Nonempty (imageModTheta L (inSubgroup perfectResidual (L ⊓ Subgroup.centralizer {d})) ≃*
        projSL 2 (GaloisField 2 (3 * n)))) ∨
    (Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* projSU 3 2 (3 * n)) ∧
      IsoPGUThree (barCentralizer (Subgroup.zpowers a) L) (2 ^ n) ∧
      Nonempty (imageModTheta L (inSubgroup perfectResidual (L ⊓ Subgroup.centralizer {d})) ≃*
        projSL 2 (GaloisField 2 (3 * n)))) ∨
    (Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* projSp 2 (GaloisField 2 (3 * n))) ∧
      Nonempty (barCentralizer (Subgroup.zpowers a) L ≃* projSp 2 (GaloisField 2 n)) ∧
      Nonempty (imageModTheta L (inSubgroup perfectResidual (L ⊓ Subgroup.centralizer {d})) ≃*
        projSL 2 (GaloisField 2 (3 * n))))

structure Data83 (G : Type) [Group G] [Finite G] (c : G) (L : Subgroup G) (a : G)
    (A₀ : Subgroup G) (d : G) (n : ℕ) : Prop where
  le_normalizer : A₀ ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G)
  c_mem : c ∈ A₀
  a_mem : a ∈ A₀
  isElemAbelian : CFSG.Assembly.IsElemAbelian 3 A₀
  card_eq : Nat.card A₀ = 81
  sectionCentralizer_eq :
    Late.sectionCentralizer A₀ L ((aschbacherSolvableCore 3 L).map L.subtype) =
      (Subgroup.zpowers c : Set G)
  d_mem : d ∈ A₀
  d_ne_one : d ≠ 1
  innerDiag : KFacts.InducesStdKind L d .inner ∨ KFacts.InducesStdKind L d .diagonal
  odd : Odd n
  ne_bot : inSubgroup perfectResidual (L ⊓ Subgroup.centralizer {d}) ≠ ⊥
  cases : Cases83 L a A₀ d n

@[expose] def Item83 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G),
    Hyp81 G A c L a → 27 < Nat.card A → ∃ (A₀ : Subgroup G) (d : G) (n : ℕ), Data83 G c L a A₀ d n

@[expose] def Item83After : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G),
    Hyp81 G A c L a → 27 < Nat.card A → ∀ (A₀ : Subgroup G) (d : G) (n : ℕ),
      Data83 G c L a A₀ d n →
        Subgroup.closure {c, a, d} ∈ partTwoE G ∧ A₀ ∈ partTwoF G ∧
          ∃ a' ∈ A₀, Hyp81 G A₀ c L a' ∧ Data83 G c L a' A₀ d n ∧
            (IsoTrialityD4 (L ⧸ aschbacherSolvableCore 3 L) n ∨
                IsoGTwoEven (L ⧸ aschbacherSolvableCore 3 L) (3 * n) →
              IsoGTwoEven (barCentralizer (Subgroup.zpowers a') L) n)

structure Sec8Std (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G)
    (a d : G) (n : ℕ) : Prop extends Hyp81 G A c L a where
  data83 : Data83 G c L a A d n
  gTwo : IsoTrialityD4 (L ⧸ aschbacherSolvableCore 3 L) n ∨
      IsoGTwoEven (L ⧸ aschbacherSolvableCore 3 L) (3 * n) →
    IsoGTwoEven (barCentralizer (Subgroup.zpowers a) L) n

@[expose] def Item84 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a d : G) (n : ℕ),
    Sec8Std G A c L a d n → ∀ (f : G) (Lf : Subgroup G), PairRel A c L f Lf →
      (f, Lf) ∈ pairOmega A ∧
        (∀ e ∈ Subgroup.closure {c, f}, e ∉ Subgroup.zpowers f → IsGammaIndex A Lf e n) ∧
        (KFacts.InducesStdKind Lf a .field ∨ KFacts.InducesStdKind Lf a .graphField) ∧
        PairRel A f Lf c L

@[expose] def Item85 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a d : G) (n : ℕ),
    Sec8Std G A c L a d n →
      ∀ S ∈ invariantPiSubgroups L (Subgroup.closure {c, a, d}) (piOf 2), S ≠ ⊥ →
        ∀ d' ∈ gammaSet A L, d' ∈ Subgroup.closure {c, a, d} →
          (∃ b ∈ Subgroup.closure {c, d'}, b ≠ 1 ∧
            ⁅inSubgroup (CFSG.pCore 2) (Subgroup.centralizer (S : Set G)) ⊓
              Subgroup.centralizer {b}, Subgroup.zpowers c⁆ ≠ ⊥) ∧
          ∀ b ∈ Subgroup.closure {c, d'}, b ≠ 1 →
            ⁅inSubgroup (CFSG.pCore 2) (Subgroup.centralizer (S : Set G)) ⊓
              Subgroup.centralizer {b}, Subgroup.zpowers c⁆ ≠ ⊥ →
            ∃! X : Subgroup G, PairRel A c L b X

@[expose] def IsUnitaryTwo (X : Type) [Group X] (m : ℕ) : Prop :=
  Nonempty (X ≃* projSU 3 2 m) ∨ IsoSUThree X (2 ^ m)

@[expose] def IsList86 (X : Type) [Group X] (n : ℕ) : Prop :=
  IsoTrialityD4 X n ∨ IsoGTwoEven X (3 * n) ∨ Nonempty (X ≃* projSp 2 (GaloisField 2 (3 * n)))

@[expose] def Item86 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a d : G) (n : ℕ),
    Sec8Std G A c L a d n → IsUnitaryTwo (L ⧸ aschbacherSolvableCore 3 L) (3 * n) →
      ∀ d' ∈ gammaSet A L,
        (∃ b ∈ Subgroup.closure {c, d'}, b ∉ Subgroup.zpowers c ∧ ∃ X : Subgroup G,
          PairRel A c L b X ∧ IsList86 (X ⧸ aschbacherSolvableCore 3 X) n) ∧
        ∀ b ∈ Subgroup.closure {c, d'}, b ∉ Subgroup.zpowers c → ∀ X : Subgroup G,
          PairRel A c L b X → IsList86 (X ⧸ aschbacherSolvableCore 3 X) n →
            IsoGTwoEven (barCentralizer (Subgroup.zpowers a) X) n ∨
            (IsoTrialityD4 (X ⧸ aschbacherSolvableCore 3 X) n ∧
              IsoPGUThree (barCentralizer (Subgroup.zpowers a) X) (2 ^ n) ∧
              ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
                IsoGTwoEven (barCentralizer (Subgroup.zpowers (a * c ^ ε)) X) n) ∨
            (Nonempty (X ⧸ aschbacherSolvableCore 3 X ≃* projSp 2 (GaloisField 2 (3 * n))) ∧
              Nonempty (barCentralizer (Subgroup.zpowers a) X ≃* projSp 2 (GaloisField 2 n)))

@[expose] def Sec8PairGTwo [Finite G] (L : Subgroup G) (a : G) (n : ℕ) : Prop :=
  IsoTrialityD4 (L ⧸ aschbacherSolvableCore 3 L) n ∨
      IsoGTwoEven (L ⧸ aschbacherSolvableCore 3 L) (3 * n) →
    IsoGTwoEven (barCentralizer (Subgroup.zpowers a) L) n

structure Sec8Pair (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G)
    (a b : G) (X : Subgroup G) (n : ℕ) : Prop extends Hyp81 G A c L a where
  card_eq : Nat.card A = 81
  pairRel : PairRel A c L b X
  isGammaIndex : IsGammaIndex A L b n
  mem_pairOmega : (b, X) ∈ pairOmega A
  not_unitary : ∀ m : ℕ, ¬ IsUnitaryTwo (X ⧸ aschbacherSolvableCore 3 X) m
  centralizer_of_unitary : (∃ m : ℕ, IsUnitaryTwo (L ⧸ aschbacherSolvableCore 3 L) m) →
    IsoGTwoEven (barCentralizer (Subgroup.zpowers a) X) n ∨
      Nonempty (barCentralizer (Subgroup.zpowers a) X ≃* projSp 2 (GaloisField 2 n))
  gTwo : Sec8PairGTwo L a n
  gTwoPartner : ∀ m : ℕ, Sec8PairGTwo X a m

@[expose] def Choice86 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a d : G) (n : ℕ),
    Sec8Std G A c L a d n → ∃ (c' : G) (L' : Subgroup G) (b : G) (X : Subgroup G),
      ((c' = c ∧ L' = L) ∨ PairRel A c L c' L') ∧ Sec8Pair G A c' L' a b X n

@[expose] noncomputable def sec8I [Finite G] (L : Subgroup G) (a : G) : Subgroup G :=
  open scoped _root_.Classical in
  if IsUnitaryTwo (L ⧸ aschbacherSolvableCore 3 L) 3 then
    Subgroup.closure {y | y ∈ L ⊓ Subgroup.centralizer {a} ∧ ∃ k : ℕ, y ^ 2 ^ k = 1}
  else inSubgroup perfectResidual (L ⊓ Subgroup.centralizer {a})

@[expose] def sec8J (X : Subgroup G) (a : G) : Subgroup G :=
  inSubgroup perfectResidual (X ⊓ Subgroup.centralizer {a})

@[expose] noncomputable def sec8B [Finite G] (A X : Subgroup G) : Subgroup G :=
  A ⊓ (X ⊔ Sec4.thetaQuotCentralizer X)

@[expose] def Item87 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a b : G)
    (X : Subgroup G) (n : ℕ), Sec8Pair G A c L a b X n →
      ∃ Y ∈ thetaComponentsAt 3 a, sec8I L a ⊔ sec8J X a ≤ Y

@[expose] def Item88 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a b : G)
    (X : Subgroup G) (n : ℕ), Sec8Pair G A c L a b X n →
      ∀ Y ∈ thetaComponentsAt 3 a, sec8I L a ⊔ sec8J X a ≤ Y →
        ¬ (KFacts.InducesStdKind Y c .field ∨ KFacts.InducesStdKind Y c .graphField) ∧
          ¬ (KFacts.InducesStdKind Y b .field ∨ KFacts.InducesStdKind Y b .graphField)

@[expose] def Item89 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a b : G)
    (X : Subgroup G) (n : ℕ), Sec8Pair G A c L a b X n →
      ∀ Y ∈ thetaComponentsAt 3 a, sec8I L a ⊔ sec8J X a ≤ Y →
        Nonempty (X ⧸ aschbacherSolvableCore 3 X ≃* projSp 2 (GaloisField 2 3)) ∧
        (Nonempty (Y ⧸ aschbacherSolvableCore 3 Y ≃* alternatingGroup (Fin 9)) ∨
          Nonempty (Y ⧸ aschbacherSolvableCore 3 Y ≃* projSp 3 (GaloisField 2 1))) ∧
        ∀ p ∈ pairOmega A, IsUnitaryTwo (p.2 ⧸ aschbacherSolvableCore 3 p.2) 3 ∨
          Nonempty (p.2 ⧸ aschbacherSolvableCore 3 p.2 ≃* projSp 2 (GaloisField 2 3))

@[expose] def Item810 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a b : G)
    (X : Subgroup G) (n : ℕ), Sec8Pair G A c L a b X n →
      ∀ e ∈ sec8B A X, e ∉ Subgroup.zpowers b → e ∈ gammaSet A X

@[expose] def Item811 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a b : G)
    (X : Subgroup G) (n : ℕ), Sec8Pair G A c L a b X n →
      ∀ (e : G) (Le : Subgroup G), PairRel A e Le b X → sec8B A X = sec8B A Le

@[expose] def Sec8Never : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a b : G)
    (X : Subgroup G) (n : ℕ), ¬ Sec8Pair G A c L a b X n

theorem item812_of
    (h83 : Item83) (h83a : Item83After)
    (h86 : Choice86) (hnever : Sec8Never) : Item812 := by
  intro G _ _ A c L a h
  obtain ⟨E, hE, hEA⟩ := h.mem_partTwoF.2.2
  have hle : 27 ≤ Nat.card A := hE.2.1 ▸ Subgroup.card_le_of_le hEA
  rcases hle.lt_or_eq with hbig | h27
  · exfalso
    obtain ⟨A₀, d, n, hd⟩ := h83 G A c L a h hbig
    obtain ⟨-, -, a', -, h81', hd', hg2⟩ := h83a G A c L a h hbig A₀ d n hd
    obtain ⟨c', L', b, X, -, hpair⟩ :=
      h86 G A₀ c L a' d n { h81' with data83 := hd', gTwo := hg2 }
    exact hnever G A₀ c' L' a' b X n hpair
  · exact h27.symm

end CFSG.RankThree.PartTwo.Sec8
