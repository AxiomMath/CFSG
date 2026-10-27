module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection10.proposition_10_14_d
import Mathlib.GroupTheory.Schreier

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

/-!
# Statements from BG Section 11

Shared notation and projection helpers for Section 11.
-/

section Notation

variable {G : Type*} [Group G] [Finite G]

/-- The ambient image of `Omega_1(S)` for a subgroup `S <= G`. -/
@[expose] public def CFSG.section11OmegaOne
    (p : Nat.Primes) (S : Subgroup G) : Subgroup G :=
  (omega₁ (G := S) (p := p.val)).map S.subtype

/-- Hypothesis 11.1, before choosing the rank-two subgroup `A` and the Sylow subgroup `P`. -/
@[expose] public def CFSG.section11Hypothesis
    (M A0 : Subgroup G) (p : Nat.Primes) : Prop :=
  M ∈ section9MaximalSubgroups G ∧
    p ∉ section10SigmaPrimes M ∧
    A0 ∈ section10PrimeOrderSubgroupsIn p M ∧
    Subgroup.normalizer (A0 : Set G) ≤ M

/-- The fixed data used throughout Section 11 after Hypothesis 11.1. -/
@[expose] public def CFSG.section11Data
    (M A0 A : Subgroup G) (p : Nat.Primes) (P : Sylow p.val M) : Prop :=
  section11Hypothesis M A0 p ∧
    primeRank p.val M = 2 ∧
    ¬ section10IdealPrime p G ∧
    A0 ≤ A ∧
    A ≤ M ∧
    A ∈ elementaryAbelianSubgroupsOfRank p.val 2 G ∧
    A ≤ section10AmbientSylowSubgroup M P ∧
    ¬ Subgroup.normalizer (section10AmbientSylowSubgroup M P : Set G) ≤ M ∧
    Subgroup.centralizer (A0 : Set G) ≤ M ∧
    Subgroup.centralizer (A : Set G) ≤ Subgroup.centralizer (A0 : Set G) ∧
    Subgroup.centralizer (A : Set G) ≤ M ∧
    A ∈ section10RankTwoMaximalElementaryAbelianSubgroups p G

end Notation

section Section11

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]

omit [IsMinCE G] in
public theorem CFSG.section11Data.hypothesis
    {M A0 A : Subgroup G} {p : Nat.Primes} {P : Sylow p.val M}
    (h11 : section11Data M A0 A p P) :
    section11Hypothesis M A0 p :=
  h11.1

omit [IsMinCE G] in
public theorem CFSG.section11Data.maximal
    {M A0 A : Subgroup G} {p : Nat.Primes} {P : Sylow p.val M}
    (h11 : section11Data M A0 A p P) :
    M ∈ section9MaximalSubgroups G :=
  h11.hypothesis.1

omit [IsMinCE G] in
public theorem CFSG.section11Data.not_sigma
    {M A0 A : Subgroup G} {p : Nat.Primes} {P : Sylow p.val M}
    (h11 : section11Data M A0 A p P) :
    p ∉ section10SigmaPrimes M :=
  h11.hypothesis.2.1

omit [IsMinCE G] in
public theorem CFSG.section11Data.A0_prime_order
    {M A0 A : Subgroup G} {p : Nat.Primes} {P : Sylow p.val M}
    (h11 : section11Data M A0 A p P) :
    A0 ∈ section10PrimeOrderSubgroupsIn p M :=
  h11.hypothesis.2.2.1

omit [IsMinCE G] in
public theorem CFSG.section11Data.normalizer_A0_le
    {M A0 A : Subgroup G} {p : Nat.Primes} {P : Sylow p.val M}
    (h11 : section11Data M A0 A p P) :
    Subgroup.normalizer (A0 : Set G) ≤ M :=
  h11.hypothesis.2.2.2

omit [IsMinCE G] in
public theorem CFSG.section11Data.primeRank
    {M A0 A : Subgroup G} {p : Nat.Primes} {P : Sylow p.val M}
    (h11 : section11Data M A0 A p P) :
    primeRank p.val M = 2 :=
  h11.2.1


omit [IsMinCE G] in
public theorem CFSG.section11Data.A0_le_A
    {M A0 A : Subgroup G} {p : Nat.Primes} {P : Sylow p.val M}
    (h11 : section11Data M A0 A p P) :
    A0 ≤ A :=
  h11.2.2.2.1

omit [IsMinCE G] in
public theorem CFSG.section11Data.A_le_M
    {M A0 A : Subgroup G} {p : Nat.Primes} {P : Sylow p.val M}
    (h11 : section11Data M A0 A p P) :
    A ≤ M :=
  h11.2.2.2.2.1

omit [IsMinCE G] in
public theorem CFSG.section11Data.A_rank_two
    {M A0 A : Subgroup G} {p : Nat.Primes} {P : Sylow p.val M}
    (h11 : section11Data M A0 A p P) :
    A ∈ elementaryAbelianSubgroupsOfRank p.val 2 G :=
  h11.2.2.2.2.2.1

omit [IsMinCE G] in
public theorem CFSG.section11Data.A_le_ambient_sylow
    {M A0 A : Subgroup G} {p : Nat.Primes} {P : Sylow p.val M}
    (h11 : section11Data M A0 A p P) :
    A ≤ section10AmbientSylowSubgroup M P :=
  h11.2.2.2.2.2.2.1

omit [IsMinCE G] in
public theorem CFSG.section11Data.not_normalizer_ambient_sylow_le
    {M A0 A : Subgroup G} {p : Nat.Primes} {P : Sylow p.val M}
    (h11 : section11Data M A0 A p P) :
    ¬ Subgroup.normalizer (section10AmbientSylowSubgroup M P : Set G) ≤ M :=
  h11.2.2.2.2.2.2.2.1


omit [IsMinCE G] in
public theorem CFSG.section11Data.centralizer_A_le_M
    {M A0 A : Subgroup G} {p : Nat.Primes} {P : Sylow p.val M}
    (h11 : section11Data M A0 A p P) :
    Subgroup.centralizer (A : Set G) ≤ M :=
  h11.2.2.2.2.2.2.2.2.2.2.1

omit [IsMinCE G] in
public theorem CFSG.section11Data.rankTwoMaximal
    {M A0 A : Subgroup G} {p : Nat.Primes} {P : Sylow p.val M}
    (h11 : section11Data M A0 A p P) :
    A ∈ section10RankTwoMaximalElementaryAbelianSubgroups p G :=
  h11.2.2.2.2.2.2.2.2.2.2.2

end Section11
