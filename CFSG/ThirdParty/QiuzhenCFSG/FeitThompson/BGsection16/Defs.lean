module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection15.corollary_15_9
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection2.PFsection2_1
import Mathlib.GroupTheory.Schreier
import Mathlib.Order.Preorder.Finite

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

/-!
# Definitions from BG Section 16

This file records a statement-only scaffold for Section 16 of
`Local Analysis for the Odd Order Theorem`.

Sections 13--15 are not present in this checkout, so the notation from
those sections that is needed to state the main results is encoded here as
Section 16 predicates.
-/

section Notation

variable {G : Type*} [Group G] [Finite G]

/-- The nonidentity elements of a subset, denoted `X#` in the text. -/
@[expose] public def CFSG.section16NonidentityElements (X : Set G) : Set G :=
  {x | x ∈ X ∧ x ≠ 1}

/-- The conjugate of a subset by an element. -/
@[expose] public def CFSG.section16ConjugateSet (X : Set G) (g : G) : Set G :=
  {y | ∃ x ∈ X, y = g * x * g⁻¹}

/-- The set `C_Y(X) = {x^y | x in X, y in Y}` from Section 16. -/
@[expose] public def CFSG.section16ConjugatesOfSetBySet (X Y : Set G) : Set G :=
  {z | ∃ x ∈ X, ∃ y ∈ Y, z = y * x * y⁻¹}


/-- The centralizer of an arbitrary subset inside a subgroup. -/
@[expose] public def CFSG.section16CentralizerInSet (H : Subgroup G) (X : Set G) :
    Subgroup G :=
  H ⊓ Subgroup.centralizer X

/-- Setwise commutativity for subsets that need not be subgroups. -/
@[expose] public def CFSG.section16SetCommutative (X : Set G) : Prop :=
  ∀ x ∈ X, ∀ y ∈ X, x * y = y * x

/-- A subset is a trivial-intersection subset of `G`. -/
@[expose] public def CFSG.section16TISubset (X : Set G) : Prop :=
  ∀ g : G, section16ConjugateSet X g = X ∨
    X ∩ section16ConjugateSet X g ⊆ ({1} : Set G)

/-- A `TI` subset with a specified normalizer. -/
@[expose] public def CFSG.section16TISubsetWithNormalizer
    (X : Set G) (N : Subgroup G) : Prop :=
  section16TISubset X ∧ Subgroup.normalizer X = N

/-- Two elements are conjugate by an element of a specified subgroup. -/
@[expose] public def CFSG.section16ConjugateInSubgroup
    (H : Subgroup G) (x y : G) : Prop :=
  ∃ h : G, h ∈ H ∧ y = h * x * h⁻¹

/-- Two subgroups are conjugate by an element of a specified subgroup. -/
@[expose] public def CFSG.section16ConjugateSubgroupsIn
    (H A B : Subgroup G) : Prop :=
  ∃ h : G, h ∈ H ∧ B = A.conjBy h

/-- A subgroup has prime order. -/
@[expose] public def CFSG.section16HasPrimeOrder (H : Subgroup G) : Prop :=
  ∃ p : Nat.Primes, Nat.card H = p.val

/-- A prime-order subgroup of a specified overgroup. -/
@[expose] public def CFSG.section16PrimeOrderSubgroupOf
    (X H : Subgroup G) : Prop :=
  X ≤ H ∧ section16HasPrimeOrder X

/-- A finite group has abelian Sylow subgroups of rank at most two. -/
@[expose] public def CFSG.section16HasAbelianSylowRankAtMostTwo
    (H : Type*) [Group H] [Finite H] : Prop :=
  ∀ p : Nat.Primes, ∀ P : Sylow p.val H,
    IsMulCommutative (P : Subgroup H) ∧ generatorRank (P : Subgroup H) ≤ 2

/-- `H` is a Hall subgroup of `K`, with the set of primes inferred from `H`. -/
@[expose] public def CFSG.section16HallSubgroupOf
    (H K : Subgroup G) : Prop :=
  ∃ _hHK : H ≤ K, IsHallSubgroup (subgroupPrimeSet H) (H.subgroupOf K)

/-- A nilpotent normal Hall subgroup of `M`, viewed in the ambient group. -/
@[expose] public def CFSG.section16NilpotentNormalHallIn
    (H M : Subgroup G) : Prop :=
  ∃ _hHM : H ≤ M, (H.subgroupOf M).Normal ∧ Group.IsNilpotent H ∧
    IsHallSubgroup (subgroupPrimeSet H) (H.subgroupOf M)

/-- `M_F`: the largest nilpotent normal Hall subgroup of `M`. -/
@[expose] public def CFSG.section16MFSubgroup
    (M MF : Subgroup G) : Prop :=
  section16NilpotentNormalHallIn MF M ∧
    ∀ H : Subgroup G, section16NilpotentNormalHallIn H M → H ≤ MF

omit [Finite G] in
/-- The subgroup `M_F` is unique when it exists. -/
public theorem CFSG.section16MFSubgroup_unique
    {M MF NF : Subgroup G}
    (hMF : section16MFSubgroup M MF)
    (hNF : section16MFSubgroup M NF) :
    MF = NF :=
  le_antisymm (hNF.2 MF hMF.1) (hMF.2 NF hNF.1)

/-- The set `kappa(M)` from Section 16. -/
@[expose] public def CFSG.section16KappaPrimes (M : Subgroup G) : Set Nat.Primes :=
  section14KappaPrimes M

/-- The ambient `p`-core of a subgroup. -/
@[expose] public def CFSG.section16PCoreIn
    (p : Nat.Primes) (H : Subgroup G) : Subgroup G := by
  letI : Fact p.val.Prime := ⟨p.property⟩
  exact (pCore p.val H).map H.subtype

/-- The set `pi*` from Section 16. -/
@[expose] public def CFSG.section16PiStarPrimes
    (G : Type*) [Group G] [Finite G] : Set Nat.Primes :=
  {p | p ∈ subgroupPrimeSet (⊤ : Subgroup G) ∧
    ∃ P : Sylow p.val G,
      IsCyclic (P : Subgroup G) ∨
        ∃ A B : Subgroup G,
          A ≤ (P : Subgroup G) ∧ Nat.card A = p.val ∧ B ≤ (P : Subgroup G) ∧
            IsCyclic B ∧
              subgroupCentralizerIn (P : Subgroup G) A = A ⊔ B ∧
                section12InternalDirectProduct A B (subgroupCentralizerIn (P : Subgroup G) A)}

/-- The second derived subgroup `M''`, viewed in the ambient group. -/
@[expose] public def CFSG.section16SecondDerivedSubgroup (M : Subgroup G) :
    Subgroup G :=
  ambientDerivedSubgroup (ambientDerivedSubgroup M)

/-- The subgroup `K* = C_{M_sigma}(K)`. -/
@[expose] public def CFSG.section16Kstar (M K : Subgroup G) : Subgroup G :=
  subgroupCentralizerIn (section10Msigma M) K

/-- The subgroup generated by `K` and `M_sigma`. -/
@[expose] public def CFSG.section16KMsigma (M K : Subgroup G) : Subgroup G :=
  K ⊔ section10Msigma M

/-- The Section 16 choices of `K` and `U` attached to `M`. -/
@[expose] public def CFSG.section16KUData
    (M K U : Subgroup G) : Prop :=
  section15KUData M K U

/-- Case `(F)`: `K = 1` and `U != 1`. -/
@[expose] public def CFSG.section16CaseF (K U : Subgroup G) : Prop :=
  K = ⊥ ∧ U ≠ ⊥

/-- Case `(P_1)`: `K != 1` and `U = 1`. -/
@[expose] public def CFSG.section16CaseP1 (K U : Subgroup G) : Prop :=
  K ≠ ⊥ ∧ U = ⊥

/-- Case `(P_2)`: `K != 1` and `U != 1`. -/
@[expose] public def CFSG.section16CaseP2 (K U : Subgroup G) : Prop :=
  K ≠ ⊥ ∧ U ≠ ⊥

/-- Maximal subgroups in case `(F)`. -/
@[expose] public def CFSG.section16MaximalTypeF (M : Subgroup G) : Prop :=
  M ∈ section14MFamilyF G


/-- Maximal subgroups in case `(P_2)`. -/
@[expose] public def CFSG.section16MaximalTypeP2 (M : Subgroup G) : Prop :=
  M ∈ section14MFamilyP2 G

/-- Maximal subgroups in case `(P_1)` or `(P_2)`. -/
@[expose] public def CFSG.section16MaximalTypeP (M : Subgroup G) : Prop :=
  M ∈ section14MFamilyP G

/-- The subgroup `Z = K x K*`, represented as an internal product. -/
@[expose] public def CFSG.section16ZSubgroup (K Kstar : Subgroup G) : Subgroup G :=
  K ⊔ Kstar

/-- The set `hat Z = Z - (K union K*)`. -/
@[expose] public def CFSG.section16HatZ (K Kstar : Subgroup G) : Set G :=
  (section16ZSubgroup K Kstar : Set G) \ ((K : Set G) ∪ (Kstar : Set G))

/-- The set `hat W = W_1 W_2 - (W_1 union W_2)`. -/
@[expose] public def CFSG.section16HatW (W1 W2 : Subgroup G) : Set G :=
  ((W1 ⊔ W2 : Subgroup G) : Set G) \ ((W1 : Set G) ∪ (W2 : Set G))

/-- The set `hat M_sigma = {a in M | C_{M_sigma}(a) != 1}`. -/
@[expose] public def CFSG.section16HatMsigmaSet (M : Subgroup G) : Set G :=
  {a | a ∈ M ∧ elementCentralizerIn (section10Msigma M) a ≠ ⊥}


@[expose] public def CFSG.section16ASet (M U : Subgroup G) : Set G :=
  {a | a ∈ section16HatMsigmaSet M ∧
    a ∈ (U : Set G) * (section10Msigma M : Set G) ∧
    a ≠ 1}


@[expose] public def CFSG.section16AZeroSet (M K : Subgroup G) : Set G :=
  {a | a ∈ section16HatMsigmaSet M ∧
    a ∉ section16ConjugatesOfSetBySet
      (section16NonidentityElements (K : Set G)) (M : Set G) ∧
    a ≠ 1}

/-- The set `xR`. -/
@[expose] public def CFSG.section16LeftCosetSet (x : G) (R : Subgroup G) : Set G :=
  {y | ∃ r ∈ R, y = x * r}

/-- The set `tilde M = union_{x in M_sigma#} xR(x)`. -/
@[expose] public def CFSG.section16TildeM
    (M : Subgroup G) (R : G → Subgroup G) : Set G :=
  {y | ∃ x : G, x ∈ section10Msigma M ∧ x ≠ 1 ∧ y ∈ section16LeftCosetSet x (R x)}

/-- A list of sets is a disjoint union of `U`. -/
@[expose] public def CFSG.section16ListDisjointUnion {α : Type*}
    (sets : List (Set α)) (U : Set α) : Prop :=
  (∀ x : α, x ∈ U ↔ ∃ i : Fin sets.length, x ∈ sets.get i) ∧
    ∀ i j : Fin sets.length, i ≠ j → Disjoint (sets.get i) (sets.get j)

/-- A list of maximal subgroups representing conjugacy classes exactly once. -/
@[expose] public def CFSG.section16MaximalConjugacyRepresentatives
    (Ms : List (Subgroup G)) : Prop :=
  (∀ M ∈ Ms, M ∈ section9MaximalSubgroups G) ∧
    (Ms.Nodup ∧
    ∀ N : Subgroup G, N ∈ section9MaximalSubgroups G →
      ∃! M : Subgroup G, M ∈ Ms ∧ ∃ g : G, N = M.conjBy g
    )

/-- The union of the conjugacy closures of all `tilde M_i`. -/
@[expose] public def CFSG.section16TildeGForRepresentatives
    (Ms : List (Subgroup G)) (R : Subgroup G → G → Subgroup G) : Set G :=
  {y | ∃ M : Subgroup G, M ∈ Ms ∧
    y ∈ section16ConjugatesOfSetBySet (section16TildeM M (R M)) Set.univ}

/-- A normal complement relation inside a specified overgroup. -/
@[expose] public def CFSG.section16NormalComplementIn
    (H K R : Subgroup G) : Prop :=
  ∃ _hHK : H ≤ K, ∃ _hRK : R ≤ K,
    (R.subgroupOf K).Normal ∧ (H.subgroupOf K).IsComplement' (R.subgroupOf K)

/-- The conjugates of `M` that contain the element `x`. -/
@[expose] public def CFSG.section16ConjugatesContainingElement
    (M : Subgroup G) (x : G) : Set (Subgroup G) :=
  {N | ∃ g : G, N = M.conjBy g ∧ x ∈ N}

/-- `R` acts sharply transitively by conjugation on the conjugates of `M` containing `x`. -/
@[expose] public def CFSG.section16ActsSharplyTransitivelyOnConjugates
    (R M : Subgroup G) (x : G) : Prop :=
  ∀ N₁ ∈ section16ConjugatesContainingElement M x,
    ∀ N₂ ∈ section16ConjugatesContainingElement M x,
      ∃! r : R, N₂ = N₁.conjBy (r : G)

/-- The complement `R(x)` from Theorem D. -/
@[expose] public def CFSG.section16TheoremDComplement
    (M : Subgroup G) (x : G) (R : Subgroup G) : Prop :=
  section16HallSubgroupOf (elementCentralizerIn M x) (Subgroup.centralizer ({x} : Set G)) ∧
    section16NormalComplementIn (elementCentralizerIn M x)
      (Subgroup.centralizer ({x} : Set G)) R ∧
        section16ActsSharplyTransitivelyOnConjugates R M x

/-- `M` is a Frobenius group with kernel `MF` and cyclic complement. -/
@[expose] public def CFSG.section16FrobeniusWithCyclicComplement
    (M MF : Subgroup G) : Prop :=
  ∃ E : Subgroup G,
    section12ComplementIn M MF E ∧ section12FrobeniusJoinWithKernel MF E ∧
      IsCyclic E

/-- The exponent of `M/H` divides a specified natural number. -/
@[expose] public def CFSG.section16QuotientExponentDvd
    (H M : Subgroup G) (n : ℕ) : Prop :=
  ∃ _hHM : H ≤ M, ∃ _hNorm : (H.subgroupOf M).Normal,
    Monoid.exponent (M ⧸ H.subgroupOf M) ∣ n

/-- The quotient `M/H` has abelian Sylow subgroups of rank at most two. -/
@[expose] public def CFSG.section16QuotientHasAbelianSylowRankAtMostTwo
    (H M : Subgroup G) : Prop :=
  ∃ _hHM : H ≤ M, ∃ _hNorm : (H.subgroupOf M).Normal,
    section16HasAbelianSylowRankAtMostTwo (M ⧸ H.subgroupOf M)

/-- The type-I alternative (Iv)(c). -/
@[expose] public def CFSG.section16TypeIConditionC
    (M H : Subgroup G) : Prop :=
  (∀ p : Nat.Primes, p ∈ subgroupPrimeSet H →
    p ∈ section16PiStarPrimes G ∧ section16QuotientExponentDvd H M (p.val - 1)) ∧
      ∃ p : Nat.Primes, p ∈ subgroupPrimeSet H ∧ p ∈ section16PiStarPrimes G ∧
        IsCyclic (section10PPrimeCore p H)

/-- `M` is of Type I, with `H = M_F`. -/
@[expose] public def CFSG.section16TypeI
    (M H : Subgroup G) : Prop :=
  ⊥ < H ∧ H < M ∧
    (∀ E : Subgroup G, section12ComplementIn M H E →
      ∃ A : Subgroup G, A ≤ E ∧ IsMulCommutative A ∧ section10NormalIn A E ∧
        ∀ x : G, x ∈ H → x ≠ 1 → elementCentralizerIn E x ≤ A) ∧
    (∀ E : Subgroup G, section12ComplementIn M H E →
      ∃ E₀ : Subgroup G, E₀ ≤ E ∧ Monoid.exponent E₀ = Monoid.exponent E ∧
        section12FrobeniusJoinWithKernel H E₀) ∧
    (∀ K : Subgroup G, section12HallSubgroupIn (section16KappaPrimes M) K M →
      K ≠ ⊥ → subgroupCentralizerIn H K = ⊥) ∧
    section16QuotientHasAbelianSylowRankAtMostTwo H M ∧
    (section16TISubset (H : Set G) ∨
      (IsMulCommutative H ∧ groupRank H = 2) ∨
        section16TypeIConditionC M H)

/-- The common conditions (T1)--(T6) in the definitions of Types II--V. -/
@[expose] public def CFSG.section16TypeCommon
    (M H V W1 W2 : Subgroup G) : Prop :=
  section16HallSubgroupOf (ambientDerivedSubgroup M) M ∧
    H ≤ ambientDerivedSubgroup M ∧
    section12ComplementIn (ambientDerivedSubgroup M) H V ∧
    Group.IsNilpotent V ∧
    W1 ≤ subgroupNormalizerIn M (V : Set G) ∧ IsCyclic W1 ∧
    Nat.card W1 = (ambientDerivedSubgroup M).relIndex M ∧
    ¬ IsCyclic H ∧
    section16SecondDerivedSubgroup M ≤ H ⊔ subgroupCentralizerIn M H ∧
    section8FittingSubgroup M = H ⊔ subgroupCentralizerIn M H ∧
    section8FittingSubgroup M ≤ ambientDerivedSubgroup M ∧
    W2 ≤ H ∧ W2 ≠ ⊥ ∧ IsCyclic W2 ∧
    (∀ x : G, x ∈ W1 → x ≠ 1 → elementCentralizerIn (ambientDerivedSubgroup M) x = W2) ∧
    (∀ W0 : Set G, W0.Nonempty → W0 ⊆ section16HatW W1 W2 →
      Subgroup.normalizer W0 = W1 ⊔ W2) ∧
    (∀ A0 A1 : Subgroup G,
      section16PrimeOrderSubgroupOf A0 V →
        section16PrimeOrderSubgroupOf A1 V →
          section16ConjugateSubgroupsIn ⊤ A0 A1 →
            ¬ section16ConjugateSubgroupsIn M A0 A1 →
              subgroupCentralizerIn H A0 = ⊥ ∨ subgroupCentralizerIn H A1 = ⊥) ∧
    W2 ≤ section16SecondDerivedSubgroup M

/-- The common extra condition (T7) for Types II--IV. -/
@[expose] public def CFSG.section16TypeIIToIVExtra
    (M W1 : Subgroup G) : Prop :=
  section16HasPrimeOrder W1 ∧ section16TISubset (section8FittingSubgroup M : Set G)

/-- `M` is of Type II, with `H = M_F`. -/
@[expose] public def CFSG.section16TypeII
    (M H : Subgroup G) : Prop :=
  ∃ V W1 W2 : Subgroup G,
    section16TypeCommon M H V W1 W2 ∧ section16TypeIIToIVExtra M W1 ∧
      IsMulCommutative V ∧ groupRank V ≤ 2 ∧ V ≠ ⊥ ∧
      ¬ Subgroup.normalizer (V : Set G) ≤ M ∧
        ∀ A : Set G, A.Nonempty → A ⊆ ambientDerivedSubgroup M →
          A ⊆ section16NonidentityElements (V : Set G) →
            section16CentralizerInSet H A ≠ ⊥ → Subgroup.normalizer A ≤ M

/-- `M` is of Type III, with `H = M_F`. -/
@[expose] public def CFSG.section16TypeIII
    (M H : Subgroup G) : Prop :=
  ∃ V W1 W2 : Subgroup G,
    section16TypeCommon M H V W1 W2 ∧ section16TypeIIToIVExtra M W1 ∧
      IsMulCommutative V ∧ Subgroup.normalizer (V : Set G) ≤ M

/-- `M` is of Type IV, with `H = M_F`. -/
@[expose] public def CFSG.section16TypeIV
    (M H : Subgroup G) : Prop :=
  ∃ V W1 W2 : Subgroup G,
    section16TypeCommon M H V W1 W2 ∧ section16TypeIIToIVExtra M W1 ∧
      ¬ IsMulCommutative V ∧ Subgroup.normalizer (V : Set G) ≤ M

/-- The Type V alternatives. -/
@[expose] public def CFSG.section16TypeVAlternative
    (M H W1 : Subgroup G) : Prop :=
  (ambientDerivedSubgroup M = H ∧ section16TISubset (H : Set G)) ∨
    (∃ p : Nat.Primes, p ∈ subgroupPrimeSet H ∧ p ∈ section16PiStarPrimes G ∧
      IsCyclic (section10PPrimeCore p H) ∧ Nat.card W1 ∣ p.val - 1) ∨
    ∃ p : Nat.Primes, p ∈ subgroupPrimeSet H ∧ p ∈ section16PiStarPrimes G ∧
      IsCyclic (section10PPrimeCore p H) ∧
        Nat.card (section16PCoreIn p H) = p.val ^ 3 ∧ Nat.card W1 ∣ p.val + 1

/-- `M` is of Type V, with `H = M_F`. -/
@[expose] public def CFSG.section16TypeV
    (M H : Subgroup G) : Prop :=
  ∃ V W1 W2 : Subgroup G,
    section16TypeCommon M H V W1 W2 ∧ V = ⊥ ∧
      section16TypeVAlternative M H W1


/-- `X` is one of the two Section 16 sets `A(M)` or `A_0(M)`. -/
@[expose] public def CFSG.section16AChoice
    (M K U : Subgroup G) (X : Set G) : Prop :=
  X = section16ASet M U ∨ X = section16AZeroSet M K

/-- The set `D = {x in X# | C_G(x) is not contained in M}` from Theorem II. -/
@[expose] public def CFSG.section16TheoremIIDSet
    (M : Subgroup G) (X : Set G) : Set G :=
  {x | x ∈ X ∧ x ≠ 1 ∧ ¬ Subgroup.centralizer ({x} : Set G) ≤ M}

/-- One supporting subgroup datum `(M_i, H_i, K_i, U_i)` for Theorem II. -/
public structure CFSG.Section16SupportData (G : Type*) [Group G] where
  M : Subgroup G
  H : Subgroup G
  K : Subgroup G
  U : Subgroup G

/-- A supporting system for the tamely-imbedded subset assertion in Theorem II. -/
@[expose] public def CFSG.section16TheoremIISupportingSystem
    (M : Subgroup G) (X D : Set G) (support : List (Section16SupportData G)) :
    Prop :=
  (∀ P ∈ support,
    P.M ∈ section9MaximalSubgroups G ∧
      section16MFSubgroup P.M P.H ∧
        section16KUData P.M P.K P.U ∧
          (section16TypeI P.M P.H ∨ section16TypeII P.M P.H) ∧
            P.H ≤ ambientDerivedSubgroup P.M) ∧
  (∀ P ∈ support, ∀ Q ∈ support, P ≠ Q →
    Nat.Coprime (Nat.card P.H) (Nat.card Q.H)) ∧
  (∀ P ∈ support, P.M = P.H ⊔ (M ⊓ P.M) ∧ M ⊓ P.H = ⊥) ∧
  (∀ P ∈ support,
    ∀ x : G, x ∈ section16NonidentityElements X →
      Nat.Coprime (Nat.card P.H) (Nat.card (elementCentralizerIn M x))) ∧
  (∀ P ∈ support,
    (section16AZeroSet P.M P.K \ (P.H : Set G)).Nonempty ∧
      section16TISubsetWithNormalizer
        (section16AZeroSet P.M P.K \ (P.H : Set G)) P.M) ∧
  ∀ x : G, x ∈ D →
    ∃ y : G, ∃ P : Section16SupportData G,
      y ∈ D ∧ section16ConjugateInSubgroup ⊤ x y ∧
        P ∈ support ∧
          ((Subgroup.centralizer ({y} : Set G) : Subgroup G) : Set G) =
            (section16CentralizerInSet P.H ({y} : Set G) : Set G) *
              (elementCentralizerIn M y : Set G) ∧
          Subgroup.centralizer ({y} : Set G) ≤ P.M

/-- Some subgroup in a supporting system has Type II. -/
@[expose] public def CFSG.section16SomeSupportingSubgroupTypeII
    (support : List (Section16SupportData G)) : Prop :=
  ∃ P : Section16SupportData G, P ∈ support ∧ section16TypeII P.M P.H

end Notation
