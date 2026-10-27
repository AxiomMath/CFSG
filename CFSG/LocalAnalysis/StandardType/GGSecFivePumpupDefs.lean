module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveL2SplitDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveIdentDefs

public section

namespace CFSG.StandardType

@[expose] def ggDMemberRoots {G : Type} [Group G] {L Bs : Subgroup G}
    {𝒦 : Finset (Subgroup G)} {ι : Type} {M : CoxeterMatrix ι}
    (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)) {k : ℕ} (φ : M.Group ≃* ggWeylD k)
    (X : Subgroup G) : Set (Fin k → ℤ) :=
  {γ | ∃ t : M.Group, GGDReflRoot k (φ t) γ ∧
    ((e t : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) ∈ ggAutomizer X Bs}

@[expose] def GGDNoSameSupp {G : Type} [Group G] {L Bs : Subgroup G}
    {𝒦 : Finset (Subgroup G)} {ι : Type} {M : CoxeterMatrix ι}
    (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)) {k : ℕ} (φ : M.Group ≃* ggWeylD k) : Prop :=
  ∀ X : Subgroup G, (X = L ∨ X ∈ 𝒦) → ∀ a b : Fin k, a ≠ b →
    ¬ (Pi.single a 1 + Pi.single b 1 ∈ ggDMemberRoots e φ X ∧
      Pi.single a 1 - Pi.single b 1 ∈ ggDMemberRoots e φ X)

@[expose] def GGDPumpPt {G : Type} [Group G] {L Bs : Subgroup G}
    {𝒦 : Finset (Subgroup G)} {ι : Type} {M : CoxeterMatrix ι}
    (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)) {k : ℕ} (φ : M.Group ≃* ggWeylD k) (c : Fin k)
    (b : ↥Bs) : Prop :=
  b ≠ 1 ∧ ∀ (u : M.Group) (η : Fin k → ℤ), GGDReflRoot k (φ u) η →
    ((((e u : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) b = b) ↔ η c = 0)

end CFSG.StandardType

end
