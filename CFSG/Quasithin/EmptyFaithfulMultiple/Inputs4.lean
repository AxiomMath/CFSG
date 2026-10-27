module

public import CFSG.Quasithin.Background.C1Basic
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.Blocks
public import CFSG.LocalAnalysis.SectionRank.NativeKGroup
public import CFSG.Quasithin.Background.B6Sections

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type*} [Group G]

@[expose] def O2FOf (H : Subgroup G) : Subgroup G := (O2F ↥H).map H.subtype

@[expose] def InputC226 : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (H R MH : Subgroup A),
    CFSG.SectionRank.IsSQTKCat ↥H →
    IsTwoRadicalIn H R → MH ≤ H → cgsIn H R ≤ MH → IsSylowTwoOf R (conjClosure R MH) →
    CharTwo (O2FOf H) → ¬ O2FOf H ≤ MH →
    ∃ (r : ℕ) (L : Fin r → Subgroup A),
      (∀ i, IsBlock2 H (L i) ∧ IsAltType (L i) 3 ∧ ¬ L i ≤ MH) ∧
        O2FOf H = (MH ⊓ O2FOf H) ⊔ ⨆ i, L i

end CFSG.Quasithin.EmptyFaithfulMultiple
