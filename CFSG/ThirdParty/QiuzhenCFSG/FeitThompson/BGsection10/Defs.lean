module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection6.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection9.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection9.theorem_9_6_in_particular
import Mathlib.GroupTheory.Schreier
import Mathlib.LinearAlgebra.Projectivization.Cardinality

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

/-!
# Definitions from BG Section 10

This file records the shared definitions and notation for Section 10 of
`Local Analysis for the Odd Order Theorem`.

The local PDF extraction mangles the Greek letters used in the book. This
module normalizes the notation to the names
`section10AlphaPrimes`, `section10BetaPrimes`, and `section10SigmaPrimes`.
-/

section Notation

variable {G : Type*} [Group G] [Finite G]

/-- A prime is ideal if the ambient group has `p`-rank at least `3`
and every Sylow `p`-subgroup is not narrow. -/
@[expose] public def CFSG.section10IdealPrime (p : Nat.Primes) (G : Type*) [Group G] [Finite G] :
    Prop :=
  2 < primeRank p.val G ∧ ∀ S : Sylow p.val G, ¬ IsNarrowPGroup p.val (S : Subgroup G)

/-- The set `α(M) = {p ∈ π(M) | r_p(M) ≥ 3}`. -/
@[expose] public def CFSG.section10AlphaPrimes (M : Subgroup G) : Set Nat.Primes :=
  {p | p ∈ subgroupPrimeSet M ∧ 2 < primeRank p.val M}

/-- The set `β(M) = {p ∈ α(M) | p is ideal}`. -/
@[expose] public def CFSG.section10BetaPrimes (M : Subgroup G) : Set Nat.Primes :=
  {p | p ∈ section10AlphaPrimes M ∧ section10IdealPrime p G}

/-- A Sylow subgroup of a subgroup, viewed inside the ambient group. -/
@[expose] public def CFSG.section10AmbientSylowSubgroup {p : Nat.Primes}
    (M : Subgroup G) (P : Sylow p.val M) : Subgroup G :=
  (P : Subgroup M).map M.subtype

/-- The set `σ(M) = {p ∈ π(M) | N_G(P) ≤ M` for some Sylow `p`-subgroup `P` of `M`}. -/
@[expose] public def CFSG.section10SigmaPrimes (M : Subgroup G) : Set Nat.Primes :=
  {p | p ∈ subgroupPrimeSet M ∧
      ∃ P : Sylow p.val M,
        Subgroup.normalizer (section10AmbientSylowSubgroup M P : Set G) ≤ M}

/-- The set of primes distinct from `p`. -/
@[expose] public def CFSG.section10PPrimeSet (p : Nat.Primes) : Set Nat.Primes :=
  ({p} : Set Nat.Primes)ᶜ

/-- The ambient `p'`-core of a subgroup. -/
@[expose] public def CFSG.section10PPrimeCore (p : Nat.Primes) (H : Subgroup G) : Subgroup G :=
  piCoreIn (section10PPrimeSet p) H

/-- The local Hall `β(M)`-core inside `M`. -/
@[expose] public def CFSG.section10MbetaSubgroup (M : Subgroup G) : Subgroup M :=
  piCore (section10BetaPrimes M) M

/-- The local Hall `α(M)`-core inside `M`. -/
@[expose] public def CFSG.section10MalphaSubgroup (M : Subgroup G) : Subgroup M :=
  piCore (section10AlphaPrimes M) M

/-- The local Hall `σ(M)`-core inside `M`. -/
@[expose] public def CFSG.section10MsigmaSubgroup (M : Subgroup G) : Subgroup M :=
  piCore (section10SigmaPrimes M) M

/-- The ambient subgroup `M_β = O_{β(M)}(M)`. -/
@[expose] public def CFSG.section10Mbeta (M : Subgroup G) : Subgroup G :=
  (section10MbetaSubgroup M).map M.subtype

/-- The ambient subgroup `M_α = O_{α(M)}(M)`. -/
@[expose] public def CFSG.section10Malpha (M : Subgroup G) : Subgroup G :=
  (section10MalphaSubgroup M).map M.subtype

/-- The ambient subgroup `M_σ = O_{σ(M)}(M)`. -/
@[expose] public def CFSG.section10Msigma (M : Subgroup G) : Subgroup G :=
  (section10MsigmaSubgroup M).map M.subtype

omit [Finite G] in
public theorem CFSG.section10_malpha_le {M : Subgroup G} :
    section10Malpha M ≤ M := by
  intro x hx
  rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
  exact y.property

public theorem CFSG.section10_le_normalizer_malpha_of_le
    {M X : Subgroup G} (hXle : X ≤ M) :
    X ≤ Subgroup.normalizer (section10Malpha M : Set G) := by
  change X ≤ Subgroup.normalizer (piCoreIn (section10AlphaPrimes M) M : Set G)
  exact section8_le_normalizer_piCoreIn_of_le_normalizer
    (G := G) (π := section10AlphaPrimes M) (H := M) (P := X)
    (hXle.trans Subgroup.le_normalizer)

/-- The conjugates of `M` that contain `X`. -/
@[expose] public def CFSG.section10ConjugatesContaining
    (M X : Subgroup G) : Set (Subgroup G) :=
  {N | ∃ g : G, N = M.conjBy g ∧ X ≤ N}

/-- `H` is normal in `K`, expressed with both the containment and the local normality witness. -/
@[expose] public def CFSG.section10NormalIn {H : Type*} [Group H]
    (K L : Subgroup H) : Prop :=
  ∃ _hKL : K ≤ L, (K.subgroupOf L).Normal

/-- A quotient `K / L` is nilpotent. -/
@[expose] public def CFSG.section10QuotientNilpotent {H : Type*} [Group H]
    (K L : Subgroup H) : Prop :=
  ∃ _hLK : L ≤ K, ∃ _hNorm : (L.subgroupOf K).Normal,
    Group.IsNilpotent (K ⧸ L.subgroupOf K)

/-- The subgroup `K` has a nilpotent Hall `π`-subgroup. -/
@[expose] public def CFSG.section10HasNilpotentHallSubgroup {H : Type*} [Group H] [Finite H]
    (π : Set Nat.Primes) (K : Subgroup H) : Prop :=
  ∃ L : Subgroup H, ∃ _hLK : L ≤ K,
    IsHallSubgroup π (L.subgroupOf K) ∧ Group.IsNilpotent L

/-- Prime-order subgroups of `H` in the ambient group. -/
@[expose] public def CFSG.section10PrimeOrderSubgroupsIn
    (p : Nat.Primes) (H : Subgroup G) : Set (Subgroup G) :=
  {X | X ≤ H ∧ Nat.card X = p.val}

/-- Rank-two elementary abelian subgroups that are maximal elementary abelian. -/
@[expose] public def CFSG.section10RankTwoMaximalElementaryAbelianSubgroups
    (p : Nat.Primes) (H : Type*) [Group H] : Set (Subgroup H) :=
  {A | A ∈ elementaryAbelianSubgroupsOfRank p.val 2 H ∧
      A ∈ maximalElementaryAbelianSubgroups p.val H}

/-- Maximal subgroups containing the centralizer of a single element. -/
@[expose] public def CFSG.section10MaximalSubgroupsContainingCentralizer
    (x : G) : Set (Subgroup G) :=
  section9MaximalSubgroupsContaining (Subgroup.centralizer ({x} : Set G))

/-- The ambient image of `Ω₁(Z(P))`. -/
@[expose] public def CFSG.section10OmegaOneCenter
    (p : Nat.Primes) (P : Subgroup G) : Subgroup G :=
  (Ω₁Z p.val P).map P.subtype

omit [Finite G] in
public theorem CFSG.section10OmegaOneCenter_isElementaryAbelian
    {p : Nat.Primes} (P : Subgroup G) :
    IsElementaryAbelian p.val (section10OmegaOneCenter p P) := by
  classical
  haveI : Fact p.val.Prime := ⟨p.property⟩
  let Ωc : Subgroup (Subgroup.center P) := omega₁ (G := Subgroup.center P) (p := p.val)
  have hΩcelem : IsElementaryAbelian p.val Ωc := by
    letI : IsMulCommutative (Subgroup.center P) := inferInstance
    simpa [Ωc] using
      IsElementaryAbelian.omega₁_of_isMulCommutative
        (p := p.val) (Subgroup.center P)
  have hΩZelem : IsElementaryAbelian p.val (Ω₁Z p.val P) := by
    change IsElementaryAbelian p.val
      ((omega₁ (G := Subgroup.center P) (p := p.val)).map
        (Subgroup.center P).subtype)
    letI : IsElementaryAbelian p.val Ωc := hΩcelem
    simpa [Ωc] using
      IsElementaryAbelian.map (p := p.val) (A := Ωc) (Subgroup.center P).subtype
  letI : IsElementaryAbelian p.val (Ω₁Z p.val P) := hΩZelem
  change IsElementaryAbelian p.val ((Ω₁Z p.val P).map P.subtype)
  simpa using
    IsElementaryAbelian.map (p := p.val) (A := Ω₁Z p.val P) P.subtype

omit [Finite G] in
public theorem CFSG.section10OmegaOneCenter_isPGroup
    {p : Nat.Primes} (P : Subgroup G) :
    IsPGroup p.val (section10OmegaOneCenter p P) := by
  have hZelem : IsElementaryAbelian p.val (section10OmegaOneCenter p P) :=
    section10OmegaOneCenter_isElementaryAbelian (G := G) (p := p) P
  letI : IsElementaryAbelian p.val (section10OmegaOneCenter p P) := hZelem
  exact IsElementaryAbelian.isPGroup p.val (section10OmegaOneCenter p P)

/-- `V` is a complement to the Sylow subgroup `P` in `N_G(P)`. -/
@[expose] public def CFSG.section10ComplementInNormalizer {p : Nat.Primes}
    (P : Sylow p.val G) (V : Subgroup G) : Prop :=
  ∃ _hV : V ≤ Subgroup.normalizer ((P : Subgroup G) : Set G),
    ((P : Subgroup G).subgroupOf (Subgroup.normalizer ((P : Subgroup G) : Set G))).IsComplement'
      (V.subgroupOf (Subgroup.normalizer ((P : Subgroup G) : Set G)))

/-- The nonabelian rank-two Sylow shape from Corollary 10.7(b). -/
@[expose] public def CFSG.section10SpecialRankTwoSylowShape
    {H : Type*} [Group H] [Finite H] (p : Nat.Primes) : Prop :=
  ∃ P₁ P₂ : Subgroup H,
    Nat.card P₁ = p.val ^ 3 ∧
      ¬ IsMulCommutative P₁ ∧
      Monoid.exponent P₁ = p.val ∧
      IsCyclic P₂ ∧
      IsCentralProduct P₁ P₂ ∧
      (Ω₁Z p.val P₂).map P₂.subtype = (Subgroup.center P₁).map P₁.subtype

public instance CFSG.section10MbetaSubgroup_normal (M : Subgroup G) :
    (section10MbetaSubgroup M).Normal := by
  dsimp [section10MbetaSubgroup]
  infer_instance

public instance CFSG.section10MbetaSubgroup_characteristic (M : Subgroup G) :
    (section10MbetaSubgroup M).Characteristic := by
  dsimp [section10MbetaSubgroup]
  infer_instance

public instance CFSG.section10MalphaSubgroup_normal (M : Subgroup G) :
    (section10MalphaSubgroup M).Normal := by
  dsimp [section10MalphaSubgroup]
  infer_instance

public instance CFSG.section10MalphaSubgroup_characteristic (M : Subgroup G) :
    (section10MalphaSubgroup M).Characteristic := by
  dsimp [section10MalphaSubgroup]
  infer_instance

public instance CFSG.section10MsigmaSubgroup_normal (M : Subgroup G) :
    (section10MsigmaSubgroup M).Normal := by
  dsimp [section10MsigmaSubgroup]
  infer_instance

public instance CFSG.section10MsigmaSubgroup_characteristic (M : Subgroup G) :
    (section10MsigmaSubgroup M).Characteristic := by
  dsimp [section10MsigmaSubgroup]
  infer_instance

end Notation
