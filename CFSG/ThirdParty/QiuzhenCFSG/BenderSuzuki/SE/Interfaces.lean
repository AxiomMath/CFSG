module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Lemma83
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Models
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Theorem6
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Cardinalities
public import Mathlib.GroupTheory.IsSubnormal

namespace CFSG
end CFSG
open CFSG

/-!
# Source-facing interfaces for the backward proof of Theorem SE

This module fixes the exact statements used by the backward assembly of
Theorem SE.  It contains no source theorem as an assumption.  In particular,
`Proposition84Conclusion` records every part of Proposition 8.4 used later;
the normalizer factorization is not treated as a substitute for the
proposition.
-/

noncomputable section

namespace CFSG.BenderSuzuki

open PFAppendixIII PFchapter1section1
open scoped Pointwise

universe u

/-! ## Shared action notation -/

/-- The stabilizer of `omega` inside the subgroup `F`. -/
@[expose] public def pointStabilizerIn
    {X Ω : Type*} [Group X] [MulAction X Ω]
    (F : Subgroup X) (omega : Ω) : Subgroup F :=
  (MulAction.stabilizer X omega).comap F.subtype

/-- The source notation `H° = <I(H)>`, embedded back in the ambient group. -/
@[expose] public def involutionCoreIn
    {X : Type*} [Group X] (H : Subgroup X) : Subgroup X :=
  (involutionCore H).map H.subtype

/-- A point stabilizer inside `F` contains an involution. -/
@[expose] public def HasStabilizerInvolution
    {X Ω : Type*} [Group X] [MulAction X Ω]
    (F : Subgroup X) (omega : Ω) : Prop :=
  ∃ s : X, s ∈ F ∧ IsInvolution s ∧ s • omega = omega

/-- Transitivity of `F` on a specified subset. -/
@[expose] public def IsTransitiveOn
    {X Ω : Type*} [Group X] [MulAction X Ω]
    (F : Subgroup X) (S : Set Ω) : Prop :=
  ∀ ⦃alpha beta : Ω⦄, alpha ∈ S → beta ∈ S →
    ∃ f : F, (f : X) • alpha = beta

/-- Double transitivity of `F` on a specified subset. -/
@[expose] public def IsTwoTransitiveOn
    {X Ω : Type*} [Group X] [MulAction X Ω]
    (F : Subgroup X) (S : Set Ω) : Prop :=
  ∀ ⦃alpha beta gamma delta : Ω⦄,
    alpha ∈ S → beta ∈ S → gamma ∈ S → delta ∈ S →
    alpha ≠ beta → gamma ≠ delta →
      ∃ f : F,
        (f : X) • alpha = gamma ∧ (f : X) • beta = delta

/-- Regularity of `F` on a specified subset. -/
@[expose] public def IsRegularOn
    {X Ω : Type*} [Group X] [MulAction X Ω]
    (F : Subgroup X) (S : Set Ω) : Prop :=
  ∀ ⦃alpha beta : Ω⦄, alpha ∈ S → beta ∈ S →
    ∃! f : F, (f : X) • alpha = beta

/-- Membership in the orbit of `alpha` under `F`. -/
@[expose] public def InOrbit
    {X Ω : Type*} [Group X] [MulAction X Ω]
    (F : Subgroup X) (alpha beta : Ω) : Prop :=
  ∃ f : F, (f : X) • alpha = beta

/-! ## Lemma 8.1 and Proposition 8.2 -/

/-- Exact conclusion of Lemma 8.1 for the canonical conjugate action. -/
@[expose] public def Lemma81Conclusion
    {X : Type u} [Group X] [Finite X]
    (M F : Subgroup X) (delta zeta : conjugateCosetSpace M) : Prop :=
  (∃ r : F,
      IsInvolution (r : X) ∧
        (r : X) • delta = zeta ∧ (r : X) • zeta = delta) ∧
    IsStronglyEmbedded (pointStabilizerIn F delta)

/-- Proposition 8.2(a), with its involution located at each fixed point. -/
@[expose] public def Proposition82aConclusion
    {X : Type u} [Group X] [Finite X]
    (M Y : Subgroup X) : Prop :=
  ∀ (omega : conjugateCosetSpace M),
    omega ∈ fixedPointsOfSubgroup X (conjugateCosetSpace M) Y →
    3 ≤ Nat.card (theorem4bFixedPoints M Y) →
      ∃ u : X,
        u ∈ MulAction.stabilizer X omega ∧
          IsInvolution u ∧ Y ≤ Subgroup.centralizer ({u} : Set X)

/-- Proposition 8.2(b), stated without introducing a separate restricted
action instance on the fixed-point subtype. -/
@[expose] public def Proposition82bConclusion
    {X : Type u} [Group X] [Finite X]
    (M Y : Subgroup X) : Prop :=
  ∀ (F : Subgroup X),
    involutionCoreIn (Subgroup.centralizer (Y : Set X)) ≤ F →
    F ≤ Subgroup.normalizer (Y : Set X) →
    3 ≤ Nat.card (theorem4bFixedPoints M Y) →
      IsTransitiveOn F
          (fixedPointsOfSubgroup X (conjugateCosetSpace M) Y) ∧
        ∀ (omega : conjugateCosetSpace M),
          omega ∈ fixedPointsOfSubgroup X (conjugateCosetSpace M) Y →
            IsStronglyEmbedded (pointStabilizerIn F omega)

/-! ## Corollary 7.13 -/

/-- The source normalizer input for the Frattini argument in Corollary 7.13:
some Sylow `2`-subgroup of `F°` has its normalizer in `F` contained in `M`. -/
@[expose] public def HasInvolutionCoreSylowNormalizerIn
    {X : Type u} [Group X] [Finite X]
    (M F : Subgroup X) : Prop :=
  ∃ P : Sylow 2 (involutionCore F),
    Subgroup.normalizer
        ((((P : Subgroup (involutionCore F)).map
          (involutionCore F).subtype : Subgroup F)) : Set F) ≤
      M.comap F.subtype

/-- The solvable alternative of Corollary 7.13. -/
@[expose] public def Corollary713SolvableConclusion
    {X : Type u} [Group X] [Finite X]
    (M F : Subgroup X) : Prop :=
  IsSolvable (involutionCoreIn F) ∧
    ∃ u : X,
      u ∈ F ⊓ M ∧ IsInvolution u ∧
        (∀ v : X, v ∈ F ⊓ M → IsInvolution v → v = u) ∧
        F ⊓ M = F ⊓ Subgroup.centralizer ({u} : Set X)

/-- The nonsolvable alternative of Corollary 7.13.  The factorization is the
literal source equality `F = F° F_{alpha,beta}`. -/
@[expose] public def Corollary713NonsolvableConclusion
    {X : Type u} [Group X] [Finite X]
    (M F : Subgroup X) : Prop :=
  let F0 := involutionCoreIn F
  twoPrimeCore F0 = Subgroup.center F0 ∧
    IsSimpleBenderGroup (F0 ⧸ twoPrimeCore F0) ∧
    IsTwoTransitiveOn F0
      {omega : conjugateCosetSpace M |
        InOrbit F (QuotientGroup.mk 1) omega} ∧
    ∀ (beta : conjugateCosetSpace M),
      InOrbit F (QuotientGroup.mk 1) beta →
      beta ≠ QuotientGroup.mk 1 →
        (F : Set X) =
          (F0 : Set X) *
            ((F ⊓ MulAction.stabilizer X
                (QuotientGroup.mk 1 : conjugateCosetSpace M) ⊓
              MulAction.stabilizer X beta : Subgroup X) : Set X)

/-- Full conclusion of Corollary 7.13 in the strongly embedded specialization. -/
@[expose] public def Corollary713Conclusion
    {X : Type u} [Group X] [Finite X]
    (M F : Subgroup X) : Prop :=
  ¬ involutionCoreIn F ≤ M ∧
    (Corollary713SolvableConclusion M F ∨
      Corollary713NonsolvableConclusion M F)

/-! ## Proposition 8.4 -/

/-- Source notation `N_I(Y) != 1`, with `I = I_D(t)`. -/
@[expose] public def HasNontrivialPeterfalviNormalizer
    {X : Type u} [Group X] (D : Subgroup X) (t : X)
    (Y : Subgroup X) : Prop :=
  ∃ x : X,
    x ∈ peterfalviKSet D t ∧
      x ∈ Subgroup.normalizer (Y : Set X) ∧ x ≠ 1

/-- `O^{2'}(C_X(Y))`, embedded in `X`. -/
@[expose] public def centralizerTwoPrimeResidual
    {X : Type u} [Group X] (Y : Subgroup X) : Subgroup X :=
  let C := Subgroup.centralizer (Y : Set X)
  (twoPrimeResidual C).map C.subtype

/-- The normalizer of `Y` inside `H`. -/
@[expose] public def normalizerIn
    {X : Type u} [Group X] (H Y : Subgroup X) : Subgroup X :=
  H ⊓ Subgroup.normalizer (Y : Set X)

/-- Parts (a) and (b) of Proposition 8.4. -/
@[expose] public def Proposition84ABConclusion
    {X : Type u} [Group X] [Finite X]
    (M : Subgroup X) (t u : X) (Y : Subgroup X) : Prop :=
  let D := M ⊓ rightConjugate M t
  let V := D ⊓ Subgroup.centralizer ({u} : Set X)
  let F := centralizerTwoPrimeResidual Y
  IsTwoTransitiveOn F
      (fixedPointsOfSubgroup X (conjugateCosetSpace M) Y) ∧
    ((Subgroup.normalizer (Y : Set X) : Subgroup X) : Set X) =
      (F : Set X) * (normalizerIn V Y : Set X) ∧
    ∃ S : Subgroup X,
      S ≤ normalizerIn M Y ∧
      (S.subgroupOf (normalizerIn M Y)).Normal ∧
      (∃ P : Sylow 2 ↥(F ⊓ M),
        S = (P : Subgroup ↥(F ⊓ M)).map (F ⊓ M).subtype) ∧
      IsRegularOn S
        {omega : conjugateCosetSpace M |
          omega ∈ fixedPointsOfSubgroup X (conjugateCosetSpace M) Y ∧
            omega ≠ QuotientGroup.mk 1} ∧
      (normalizerIn M Y : Set X) =
        (S : Set X) * (normalizerIn D Y : Set X)

/-- Parts (c) and (d) of Proposition 8.4. -/
@[expose] public def Proposition84CDConclusion
    {X : Type u} [Group X] [Finite X]
    (M : Subgroup X) (t : X) (Y : Subgroup X) : Prop :=
  let D := M ⊓ rightConjugate M t
  let F := centralizerTwoPrimeResidual Y
  ∃ (n : ℕ) (J : Subgroup X),
    2 ≤ n ∧
      (J : Set X) =
        {x : X | x ∈ peterfalviKSet D t ∧
          x ∈ Subgroup.normalizer (Y : Set X)} ∧
      J ≤ F ∧ IsCyclic J ∧ Nat.card J = 2 ^ n - 1 ∧
      twoPrimeCore F = Subgroup.center F ∧
      IsSimpleBenderGroupAtExponent n (F ⧸ twoPrimeCore F)

/-- Full Proposition 8.4 conclusion for one `Y`. -/
@[expose] public def Proposition84Conclusion
    {X : Type u} [Group X] [Finite X]
    (M : Subgroup X) (t u : X) (Y : Subgroup X) : Prop :=
  Proposition84ABConclusion M t u Y ∧
    (HasNontrivialPeterfalviNormalizer
      (M ⊓ rightConjugate M t) t Y →
        Proposition84CDConclusion M t Y)

/-- The quantified source statement of Proposition 8.4. -/
@[expose] public def Proposition84Statement
    {X : Type u} [Group X] [Finite X]
    (M : Subgroup X) (t u : X) : Prop :=
  let D := M ⊓ rightConjugate M t
  let V := D ⊓ Subgroup.centralizer ({u} : Set X)
  ∀ (Y Y1 : Subgroup X),
    Y ≤ V → Y1 ≠ ⊥ → Y1 ≤ Y →
    (Y1.subgroupOf Y).IsSubnormal →
    HasNontrivialPeterfalviNormalizer D t Y1 →
      Proposition84Conclusion M t u Y

/-- The `Y₁ = Y` case of Proposition 8.4.  This is the independent
classification/local-structure leaf at source lines 2457--2482.  The
nontriviality hypothesis is inherited from the quantified source statement. -/
@[expose] public def Proposition84BaseStep
    {X : Type u} [Group X] [Finite X]
    (M : Subgroup X) (t u : X) : Prop :=
  let D := M ⊓ rightConjugate M t
  let V := D ⊓ Subgroup.centralizer ({u} : Set X)
  ∀ (Y : Subgroup X),
    Y ≤ V → Y ≠ ⊥ → HasNontrivialPeterfalviNormalizer D t Y →
      Proposition84Conclusion M t u Y

/-- The proper-predecessor step of Proposition 8.4 at source lines
2484--2505.  The induction hypothesis is exposed exactly as the full
conclusion for `Y₀`; parts (c)--(d) for `Y` are vacuous in this branch. -/
@[expose] public def Proposition84ProperStep
    {X : Type u} [Group X] [Finite X]
    (M : Subgroup X) (t u : X) : Prop :=
  let D := M ⊓ rightConjugate M t
  let V := D ⊓ Subgroup.centralizer ({u} : Set X)
  ∀ (Y₀ Y : Subgroup X),
    Y ≤ V → Y₀ ≠ ⊥ → Y₀ < Y →
    (Y₀.subgroupOf Y).Normal →
    Proposition84Conclusion M t u Y₀ →
    ¬ HasNontrivialPeterfalviNormalizer D t Y →
      Proposition84ABConclusion M t u Y

/-! ## Theorem 6 and final assembly -/

/-- The nilpotent normal-complement conclusion of Theorem 6. -/
@[expose] public def Theorem6Conclusion
    {X : Type u} [Group X] [Finite X]
    (M : Subgroup X) : Prop :=
  ∀ (g : X), g ∉ M →
    ∃ Q : Subgroup X,
      IsNormalComplementIn M (M ⊓ rightConjugate M g) Q ∧
        Group.IsNilpotent Q

/-- A Borel subgroup in the sense used in Theorem SE: a solvable Sylow
`2`-normalizer. -/
@[expose] public def IsBorelSubgroup
    {G : Type u} [Group G] [Finite G] (B : Subgroup G) : Prop :=
  IsSolvable B ∧
    ∃ S : Sylow 2 G,
      B = Subgroup.normalizer ((S : Subgroup G) : Set G)

/-- Proof-support data retained from the nonsolvable base case of
Proposition 8.4.  The numbered proposition only records the recognized
quotient and its action; Lemma 11.4 also needs the fact that the central odd
kernel lies in `M` and that the image of `F ∩ M` is the corresponding Borel
subgroup of the quotient. -/
public structure Proposition84ModelSupport
    {X : Type u} [Group X] [Finite X]
    (M Y : Subgroup X) : Prop where
  oddCore_map_le_M :
    (twoPrimeCore (centralizerTwoPrimeResidual Y)).map
      (centralizerTwoPrimeResidual Y).subtype ≤ M
  quotient_borel :
    IsBorelSubgroup
      ((((centralizerTwoPrimeResidual Y) ⊓ M).subgroupOf
          (centralizerTwoPrimeResidual Y)).map
        (QuotientGroup.mk'
          (twoPrimeCore (centralizerTwoPrimeResidual Y))))

/-- The Proposition 8.4 support package, quantified over the base-case
subgroups for which the Peterfalvi normalizer is nontrivial.  It is kept
separate from `Proposition84Statement` to avoid changing the source theorem's
meaning. -/
@[expose] public def Proposition84ModelSupportStatement
    {X : Type u} [Group X] [Finite X]
    (M : Subgroup X) (t u : X) : Prop :=
  let D := M ⊓ rightConjugate M t
  let V := D ⊓ Subgroup.centralizer ({u} : Set X)
  ∀ (Y : Subgroup X),
    Y ≤ V → Y ≠ ⊥ → HasNontrivialPeterfalviNormalizer D t Y →
      Proposition84ModelSupport M Y

/-- The strengthened proof-support form of the Proposition 8.4 base step. -/
@[expose] public def Proposition84BaseFullStep
    {X : Type u} [Group X] [Finite X]
    (M : Subgroup X) (t u : X) : Prop :=
  let D := M ⊓ rightConjugate M t
  let V := D ⊓ Subgroup.centralizer ({u} : Set X)
  ∀ (Y : Subgroup X),
    Y ≤ V → Y ≠ ⊥ → HasNontrivialPeterfalviNormalizer D t Y →
      Proposition84Conclusion M t u Y ∧ Proposition84ModelSupport M Y

/-- The rank-at-least-two branch of Theorem SE. -/
@[expose] public def TheoremSEBenderConclusion
    {X : Type u} [Group X] [Finite X]
    (M : Subgroup X) : Prop :=
  let L := involutionCore X
  IsSimpleBenderGroup (L ⧸ twoPrimeCore L) ∧
    (twoPrimeCore L).map L.subtype ≤ M ⊓ L ∧
    IsBorelSubgroup
      (((M ⊓ L).subgroupOf L).map
        (QuotientGroup.mk' (twoPrimeCore L)))

/-- The complete conclusion of Theorem SE. -/
@[expose] public def TheoremSEConclusion
    {X : Type u} [Group X] [Finite X]
    (M : Subgroup X) : Prop :=
  let L := involutionCore X
  ¬ TwoRankAtLeastTwo L ∨ TheoremSEBenderConclusion M

/-- The exact minimal-counterexample induction step needed to assemble
Theorem SE.  It only handles the rank-at-least-two branch and assumes the
theorem for strongly embedded subgroups of every strictly smaller finite
group.  The all-smaller-groups form is essential: the source first passes to
an odd-core quotient before invoking the simple-ambient Sections 5--11
argument.  Proper-subgroup induction is obtained by specialization in the
outer strong-induction wrapper. -/
@[expose] public def TheoremSEMinimalStep : Prop :=
  ∀ {X : Type u} [Group X] [Finite X] (M : Subgroup X),
    IsStronglyEmbedded M →
    (∀ {Y : Type u} [Group Y] [Finite Y],
      Nat.card Y < Nat.card X →
      ∀ (N : Subgroup Y), IsStronglyEmbedded N →
        TheoremSEConclusion N) →
    TwoRankAtLeastTwo (involutionCore X) →
      TheoremSEBenderConclusion M

/-- The rank-one exclusion used in the simple-group final clause. -/
@[expose] public def SimpleStronglyEmbeddedRankTwo : Prop :=
  ∀ {X : Type u} [Group X] [Finite X] (M : Subgroup X),
    IsSimpleGroup X → IsStronglyEmbedded M → TwoRankAtLeastTwo X

end CFSG.BenderSuzuki
