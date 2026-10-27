module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Classification

/-!
# D-group quotient vocabulary (`IsDGroupQuotient`, odd `PSL₂`/`PGL₂` iso)

The quotient clause of the paper's `D`-group definition (GW Part I, p. 118)
and its `PSL₂`/`PGL₂`-isomorphism vocabulary, moved DOWN from the
`GorensteinWalter.GW1965` wrapper so that the per-theorem GW1965-cleanup
modules can state their theorems without importing the wrapper (no landing
import cycle).

namespace CFSG
end CFSG
open CFSG
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- `H ≅ PSL₂(K)` with `|K|` an odd prime power, for the explicit field `K`.
This is the paper's "isomorphic to `PSL(2,q)`, `q` odd" with `q = |K|`
(e.g. Prop 9, p. 219).  The existential form is `IsIsoToPSL2OddExists`. -/
@[expose] public def IsIsoToPSL2Odd (K : Type u) [Field K] [Finite K]
    {G : Type u} [Group G] [Finite G] (H : Subgroup G) : Prop :=
  IsOddPrimePower (Nat.card K) ∧ Nonempty (H ≃* PSL2 K)

/-- `H ≅ PSL(2,q)` with `q` an odd prime power: there is a finite field `K`
whose cardinality is an odd prime power and an isomorphism `H ≅ PSL₂(K)`.
The field is an explicit parameter of `IsIsoToPSL2Odd` (a `∃`-binder over a
`Field` instance makes the witness construction time out at `whnf`); the
statement-level quantification is packaged here. -/
@[expose] public def IsIsoToPSL2OddExists {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) : Prop :=
  ∃ (K : Type u) (instK : Field K) (_ : Finite K),
    letI : Field K := instK
    IsIsoToPSL2Odd K H

/-- `H ≅ PGL₂(K)` with `|K|` an odd prime power, for the explicit field `K`:
the `PGL(2,q)` analogue of `IsIsoToPSL2Odd`.  The existential form is
`IsIsoToPGL2OddExists`. -/
@[expose] public def IsIsoToPGL2Odd (K : Type u) [Field K] [Finite K]
    {G : Type u} [Group G] [Finite G] (H : Subgroup G) : Prop :=
  IsOddPrimePower (Nat.card K) ∧ Nonempty (H ≃* PGL2 K)

/-- `H ≅ PGL(2,q)` with `q` an odd prime power: the existential form of
`IsIsoToPGL2Odd`. -/
@[expose] public def IsIsoToPGL2OddExists {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) : Prop :=
  ∃ (K : Type u) (instK : Field K) (_ : Finite K),
    letI : Field K := instK
    IsIsoToPGL2Odd K H

/-- The quotient clause of the paper's `D`-group definition (Part I, p. 118):
`G/O(G)` is isomorphic to `A₇` or to a subgroup of `PΓL(2,q)` containing
`PSL(2,q)`, `q` odd.  The repository vocabulary has no `PΓL(2,q)`; the
`PSL(2,q)`/`PGL(2,q)` normal-subgroup clause of `IsDGroup` is used instead.
This is the paper's condition (ii) alone — unlike `IsDGroup` it does not
include the `2`-group quotient case, so e.g. a dihedral `2`-group is not a
"`D`-group" here.

**Deviations from the paper's clause (recorded per the translation review
`node_graph/review-gw1965-lean.md`):** (1) the `Odd L.index` hypothesis is
added — the paper's clause has no parity condition on the subgroup; (2) the
`PΓL(2,q)`-embeddability ("containing `PSL(2,q)`, but not `PGL(2,q)`") is
not expressible in the repository vocabulary and is dropped; (3) the
`PGL(2,q)`-isomorphic alternative is added as a substitute.  The drift is
inert in every application here (dihedral-Sylow + `O(G) = 1` + `C_G(H) = 1`
context), but the statement is strictly weaker than the paper's clause in
isolation. -/
@[expose] public def IsDGroupQuotient (G : Type u) [Group G] [Finite G] : Prop :=
  Nonempty (G ⧸ pPrimeCore 2 G ≃* alternatingGroup (Fin 7)) ∨
    ∃ L : Subgroup (G ⧸ pPrimeCore 2 G),
      L.Normal ∧ Odd L.index ∧
        (IsIsoToPSL2OddExists (G := G ⧸ pPrimeCore 2 G) L ∨
          IsIsoToPGL2OddExists (G := G ⧸ pPrimeCore 2 G) L)

end CFSG.GorensteinWalter
