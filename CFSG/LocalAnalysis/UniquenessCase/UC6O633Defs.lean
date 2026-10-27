module

public import CFSG.LocalAnalysis.UniquenessCase.UC6S29
public import CFSG.LocalAnalysis.UniquenessCase.UC6S37
public import CFSG.LocalAnalysis.UniquenessCase.UC6S35
public import CFSG.LocalAnalysis.UniquenessCase.UCKInputs
public import CFSG.RankThree.FFModules.Offenders
public import CFSG.LocalAnalysis.UniquenessCase.UC6S9

public section

namespace CFSG.LocalAnalysis.UniquenessCase

open Subgroup CFSG.Open
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.ASVolI.ChIJK (F4)
open CFSG.RankThree.FFModules (fixSub)
open scoped MatrixGroups

namespace UC6

namespace Mz614

variable {G : Type} [Group G] [Finite G] (m : Mz614 G)

@[expose] noncomputable def OL : Subgroup G := (CFSG.pPrimeCore m.r ↥m.L).map m.L.subtype

@[expose] def C634Q : Prop :=
  ⁅m.Z, m.U⁆ ≤ CFSG.Open.pCoreOf 2 m.K →
    CFSG.Open.IsQuasisimple (CFSG.LocalAnalysis.UniquenessCase.UC22.Bar2 m.K)

end Mz614

end UC6

namespace UCK

@[expose] def K634 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X → CFSG.Open.IsQuasisimple X →
    CFSG.Open.pRank 3 (⊤ : Subgroup X) = 1 →
    ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
      (ρ : Representation (ZMod 2) X V), Function.Injective ρ →
    ∀ D : Subgroup X, Nat.card D = 3 → fixSub ρ D = ⊥ →
      ∀ p : ℕ, p.Prime → p ≠ 2 → p ≠ 3 → CFSG.Open.pRank p (⊤ : Subgroup X) ≤ 2

end UCK

end CFSG.LocalAnalysis.UniquenessCase
