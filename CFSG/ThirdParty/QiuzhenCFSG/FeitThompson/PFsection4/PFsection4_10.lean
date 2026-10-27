module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection4.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection2.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection1.PFsection1_2
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection1.PFsection1_5
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection1.PFsection1_6
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.HallSubgroups.Core

namespace CFSG
end CFSG
open CFSG

/-!
# Peterfalvi, Section 4: Theorem (4.10)
-/

noncomputable section

open scoped BigOperators

attribute [local instance] Fintype.ofFinite

namespace CFSG.Section4Scratch
universe u
universe v
open Section1 Section2 Section3 Section4

/-! ## (4.10) -/

@[expose] public def theorem_4_10_statement
    {L : Type u} [Group L] [Finite L]
    {G : Type v} [Group G] [Finite G]
    {W : Subgroup L}
    {I J : Type*} [Fintype I] [Fintype J]
    (i0 : I) (j0 : J)
    (ω : I → J → ClassFunction W)
    (σ : ClassFunction W →ₗ[ℂ] ClassFunction G)
    (piChar : I → J → ClassFunction L)
    (deltaSign : J → ℂ)
    (τ : ClassFunction L →ₗ[ℂ] ClassFunction G) : Prop :=
  ∀ i j,
    τ (deltaSign j • piChar i j - deltaSign j • piChar i0 j - piChar i j0 + piChar i0 j0) =
      (σ (ω i j) - σ (ω i0 j)) - (σ (ω i j0) - σ (ω i0 j0))

end CFSG.Section4Scratch
