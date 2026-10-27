module

public import CFSG.LocalAnalysis.WeakClosure81.W16PFiveSix
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellThompson
public import CFSG.LocalAnalysis.WeakClosure81.W16Setup

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.QuasithinUnique.Setup.Campbell
open Subgroup
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

@[expose] def tSub16 (V₀ S : Subgroup G) : Subgroup G :=
  S ⊓ centralizer (V₀ : Set G)

@[expose] def qSub16 (V₀ V S H : Subgroup G) : Subgroup G :=
  pCoreOf 2 (conjClosure V H ⊔ tSub16 V₀ S)

@[expose] def W16SixteenDich (G : Type) [Group G] [Finite G] : Prop :=
  Std15 G → ∀ ⦃M V₀ V U S H : Subgroup G⦄, Cex16 M V₀ V U S → IsMinFam16 M U S H →
    ¬ V ≤ pCoreOf 2 H →
      (qSub16 V₀ V S H ≤ tSub16 V₀ S ∧
          ∀ A ∈ elemFamilyIn 2 (tSub16 V₀ S), A ≤ qSub16 V₀ V S H) ∨
        ((∃ φ : ↥(conjClosure V H) →* PSL(2, GaloisField 2 (E3.mQuot V (iSub16 V H))),
            Function.Surjective φ ∧ φ.ker = (iSub16 V H).subgroupOf (conjClosure V H)) ∧
          mSub V₀ = E3.mQuot V (iSub16 V H))

end CFSG.LocalAnalysis.WeakClosure81

end
