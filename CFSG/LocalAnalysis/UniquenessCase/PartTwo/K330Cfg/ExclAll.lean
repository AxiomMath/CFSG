module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg.False
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg.Sit
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg.Cfg

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup

@[expose] def K330Cfg.ExclAll : Prop :=
  ∀ (J : Type) [Group J] [Finite J], K330Cfg.Sit J → K330Cfg.Excl J

theorem K330Cfg.OneComp.false_of_exclAll (hE : K330Cfg.ExclAll) {K : Type} [Group K] [Finite K]
    {J M X P : Subgroup K} (h : K330Cfg.OneComp J M X P) : False :=
  h.false_of_excl (hE ↥J h.sit)

theorem Cfg145.false_of_exclAll (hE : K330Cfg.ExclAll) {K : Type} [Group K] [Finite K]
    {M X₁ X₂ P : Subgroup K} (c : Cfg145 M X₁ X₂ P) {J : Subgroup K}
    (hJ : IsComponentOf J ⊤) (hJu : ∀ J' : Subgroup K, IsComponentOf J' ⊤ → J' = J)
    (hXJ : X₁ ⊔ X₂ ≤ J) : False :=
  (c.oneComp hJ hJu hXJ).false_of_exclAll hE

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
