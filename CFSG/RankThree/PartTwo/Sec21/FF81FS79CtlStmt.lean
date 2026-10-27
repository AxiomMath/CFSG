module

public import CFSG.RankThree.PartTwo.Sec21.CarterFS79Setup

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.RankThree.PartTwo.Sec21.FF79 Equiv
open CFSG.Assembly (InCatalog)

variable {H : Type} [Group H] [Finite H]

def CtlEq (b β : H) : Prop :=
  setMul (Opp 3 (Nor (Subgroup.zpowers β)))
    (Nor (Subgroup.zpowers b) ⊓ Nor (Subgroup.zpowers β)) = Nor (Subgroup.zpowers β)

def FS79D1K : Prop :=
  ∀ (H : Type) [Group H] [Finite H], KCore.KGroupNonab InCatalog H →
    ∀ (b t b₁ b₂ : H) (J : Subgroup H), FS79Hyp b t b₁ b₂ J → CtlEq b (b * b₁)

def FS79D2K : Prop :=
  ∀ (H : Type) [Group H] [Finite H], KCore.KGroupNonab InCatalog H →
    ∀ (b t b₁ b₂ : H) (J : Subgroup H), FS79Hyp b t b₁ b₂ J → CtlEq b (b * (b₁ * b₂))

end CFSG.RankThree.PartTwo.Sec21.FF81
