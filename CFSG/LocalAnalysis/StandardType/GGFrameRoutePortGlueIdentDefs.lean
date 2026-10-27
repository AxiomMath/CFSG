module

public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
public import CFSG.LocalAnalysis.StandardType.GGSixAutKFinerChoiceTwoMoves

public section

namespace CFSG.StandardType.FrameRoute

open CFSG.StandardType.ChoiceTwo

variable {G : Type} [Group G]

@[expose] def GGSignedB6At (Bs : Subgroup G) (z : G) : Prop :=
  ∃ u : G → Fin 6 → ZMod 3,
    (∀ b ∈ Bs, ∀ b' ∈ Bs, u (b * b') = u b + u b') ∧
    (∀ b ∈ Bs, u b = 0 ↔ b ∈ Subgroup.zpowers z) ∧
    (∀ v : Fin 6 → ZMod 3, ∃ b ∈ Bs, u b = v) ∧
    (∀ g ∈ Subgroup.normalizer (Bs : Set G) ⊓ Subgroup.centralizer ({z} : Set G),
      ∃ (π : Equiv.Perm (Fin 6)) (η : Fin 6 → Bool),
        ∀ b ∈ Bs, u (g * b * g⁻¹) = moveExp π η (u b)) ∧
    ∀ (π : Equiv.Perm (Fin 6)) (η : Fin 6 → Bool),
      ∃ g ∈ Subgroup.normalizer (Bs : Set G) ⊓ Subgroup.centralizer ({z} : Set G),
        ∀ b ∈ Bs, u (g * b * g⁻¹) = moveExp π η (u b)

end CFSG.StandardType.FrameRoute

end
