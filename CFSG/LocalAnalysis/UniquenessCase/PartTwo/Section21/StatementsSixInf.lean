module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21a
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent.Radical

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

@[expose] def S21_6Inf (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx21 D Ch, ∀ L ∈ calC D.M, (∃ s : TauCeti.SporadicName, IsSpor (BarInf L) s) →
    IsJ1 (Bar2 L) ∧
      (⁅CFSG.Quasithin.opResidual 3 c.B, L⁆ ≤ CFSG.Open.pCoreOf 2 L ∨ 7 ∈ piSet c.B)

end CFSG.LocalAnalysis.UniquenessCase.UC22
