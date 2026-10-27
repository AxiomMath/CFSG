module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsC
public import CFSG.LocalAnalysis.WeakClosure81.NineDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def W3Lem914 (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (V T N L : Subgroup G), Hyp9 V T → T ≤ N → N ≤ normalizer (V : Set G) → N = T ⊔ L →
    L = CFSG.Quasithin.perfectCore (L ⊔ pCoreOf 2 N) →
    (∃ (Z : Type) (_ : Group Z) (ψ : ↥N →* Z), Function.Surjective ψ ∧
      (∀ x : ↥N, ψ x = 1 ↔ (x : G) ∈ pCoreOf 2 N) ∧
      CFSG.IsComponent ((L.subgroupOf N).map ψ)) →
    (∃ (A : Type) (_ : Group A) (φ : ↥(N ⊓ normalizer (L : Set G)) →* A),
      Function.Surjective φ ∧
      (∀ x : ↥(N ⊓ normalizer (L : Set G)),
        φ x = 1 ↔ (x : G) ∈ S17.centSection N L (oTwoThreeIn L)) ∧
      (CFSG.Quasithin.F6.IsPGL2 7 A ∨
        Inputs1719.IsAutOf A (alternatingGroup (Fin 6)) ∨ Inputs1719.IsM10 A ∨
        CFSG.Quasithin.F6.IsPGL2 9 A)) →
    (∀ P : Subgroup G, IsSylowIn 3 P N → P ∈ calP V) →
    normalizer (E3.wClos V 1 T : Set G) ≤ normalizer (V : Set G) ∨
      N ≤ normalizer (E3.wClos V 0 T : Set G)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
