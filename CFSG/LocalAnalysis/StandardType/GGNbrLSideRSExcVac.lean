module

public import CFSG.LocalAnalysis.StandardType.GGNbrLSideDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

@[expose] def GGNbrLSideNoPSL3 {R : Type} [Group R] (I : Set (MulAut R)) : Prop :=
  ∀ φ ∈ I, φ ≠ 1 → φ ^ 3 = 1 → ∀ J : Subgroup R,
    CFSG.Open.IsComponentOf J (fixSubgroup φ) →
      ∀ (F : Type) [Field F] [Finite F], 4 ≤ Nat.card F →
        IsEmpty (↥J ⧸ Subgroup.center ↥J ≃* projectiveSL 3 F)

theorem ggNbrLSideDich_of_noPSL3 {lab : LargeEvenLabel} {R : Type} [Group R]
    {I : Set (MulAut R)} (h : GGNbrLSideNoPSL3 I) : GGNbrLSideDich lab I := by
  intro φ hφ ψ _ hφ1 hφ3 _ _ J hJ Q hQ4 _ hF α _
  obtain ⟨F, _, _, hFQ, ⟨e⟩⟩ := hF
  exact ((h φ hφ hφ1 hφ3 J hJ F (by omega)).false e).elim

end CFSG.StandardType

end
