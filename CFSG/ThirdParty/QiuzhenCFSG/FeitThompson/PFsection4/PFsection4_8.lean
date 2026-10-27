module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection4.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection4.PFsection4_4
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection2.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection1.PFsection1_2
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection1.PFsection1_5
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection1.PFsection1_6
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.HallSubgroups.Core

namespace CFSG
end CFSG
open CFSG

/-!
# Peterfalvi, Section 4: Theorem (4.8)
-/

noncomputable section

open scoped BigOperators

attribute [local instance] Fintype.ofFinite

namespace CFSG.Section4Scratch
universe u
universe v
open Section1 Section2 Section3 Section4

/-! ## (4.8) -/

@[expose] public def theorem_4_8_statement
    {L : Type u} [Group L] [Finite L]
    {G : Type v} [Group G] [Finite G]
    (W2 W : Subgroup L)
    (A : Set L)
    {I J : Type*} [Fintype I] [Fintype J]
    (j0 : J)
    (ω : I → J → ClassFunction W)
    (σ : ClassFunction W →ₗ[ℂ] ClassFunction G)
    (piChar : I → J → ClassFunction L)
    (deltaSign : J → ℂ)
    (τ : ClassFunction L →ₗ[ℂ] ClassFunction G) : Prop :=
  ∀ i j k, j ≠ j0 → k ≠ j0 →
    Section1.degree (piChar i j) = Section1.degree (piChar i k) →
      Section1.supportedOn (piChar i j - piChar i k) (a0Set W2 W A) ∧
        deltaSign j = deltaSign k ∧
          τ (piChar i j - piChar i k) =
            deltaSign j • (σ (ω i j) - σ (ω i k))

end CFSG.Section4Scratch
