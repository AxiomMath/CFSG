module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront08
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21a

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped Pointwise

section Section21d

variable {G : Type} [Group G] [Finite G]

@[expose] def CentralizesBar (x : G) (L : Subgroup G) : Prop :=
  x ∈ normalizer (L : Set G) ∧ ∀ l ∈ L, x * l * x⁻¹ * l⁻¹ ∈ CFSG.Open.pCoreOf 2 L

@[expose] def S21_3 (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx21 D Ch, ∀ L ∈ calC D.M,
    (∃ b ∈ c.B, b ≠ 1 ∧ CentralizesBar b L) → F08.Thin8 L

end Section21d

end CFSG.LocalAnalysis.UniquenessCase.UC22
