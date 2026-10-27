module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection5.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection1.PFsection1_7_Core
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection2.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection3.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection4.Basic

namespace CFSG
end CFSG
open CFSG

/-!
# Peterfalvi, Section 5: Theorem (5.1)
-/

noncomputable section

open scoped BigOperators

attribute [local instance] Fintype.ofFinite

namespace CFSG.Section5
universe u
universe v

/-! ## (5.1) -/

/--
Peterfalvi Definition `(5.1)`: the triple `(S, A, T)` is coherent when
`S ⊂ Z[Irr L]`, `Z[S, A] ≠ 0`, and the given isometry on `Z[S, A]` extends to
an isometry on `Z[S]` with values in `Z[Irr(G)]`.
-/
@[expose] public def definition_5_1_statement
    {L : Type u} [Group L] [Finite L]
    {G : Type u} [Group G] [Finite G]
    (A : Set L)
    (S : Finset (Section1.ClassFunction L))
    (T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G) : Prop :=
  IsCoherentTriple A S T

end CFSG.Section5
