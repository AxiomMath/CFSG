module

public import CFSG.Quasithin.Background.B4Models
public import CFSG.Quasithin.Background.B6Defs
public import CFSG.Quasithin.Background.D2Basic

public section

namespace CFSG.Quasithin

open CFSG.Open

@[expose] def B69Struct : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ (X T M : Subgroup (MulAut V)),
      (∃ (H : Type) (_ : Group H) (_ : Finite H), CFSG.Open.SQTKTauCeti.StronglyQuasithin H ∧
        CFSG.SectionRank.IsKGroupCat H ∧ ∃ f : H →* ↥X, Function.Surjective f) →
      MinParabolic X T M → pCoreOf 2 X = ⊥ → IsFFModule X →
      ∃ 𝓗 : Finset (Subgroup (MulAut V)),
        (∀ H ∈ 𝓗, H ≤ X) ∧ ffJ X = ⨆ H ∈ 𝓗, H ∧
        (∀ H ∈ 𝓗, ∀ H' ∈ 𝓗, H ≠ H' → ∀ a ∈ H, ∀ b ∈ H', a * b = b * a) ∧
        (∀ H ∈ 𝓗, H ⊓ ⨆ H' ∈ 𝓗, ⨆ (_ : H' ≠ H), H' = ⊥) ∧
        commV (ffJ X) ⊔ fixV (ffJ X) = (⨆ H ∈ 𝓗, commV H) ⊔ fixV (ffJ X) ∧
        (∀ H ∈ 𝓗, (commV H ⊔ fixV (ffJ X)) ⊓
            ((⨆ H' ∈ 𝓗, ⨆ (_ : H' ≠ H), commV H') ⊔ fixV (ffJ X)) = fixV (ffJ X)) ∧
        (∀ H ∈ 𝓗, ∀ H' ∈ 𝓗, H ≠ H' → commSub (commV H) H' = ⊥) ∧
        (∀ H ∈ 𝓗, ∀ H' ∈ 𝓗, ∃ t ∈ T, B6.conjSub t H = H') ∧
        X = ffJ X ⊔ T ∧
        ∀ H ∈ 𝓗,
          (∃ e : ℕ, 1 ≤ e ∧ BinaryNaturalSL H (commV H) (commV H ⊓ fixV (ffJ X)) 2 e ∧
            M ⊓ H = H ⊓ Subgroup.normalizer ((T ⊓ H : Subgroup (MulAut V)) : Set (MulAut V))) ∨
          (∃ k : ℕ, 1 ≤ k ∧ ∃ π : Equiv.Perm (Fin (2 * k + 1)) →* ↥H,
            (FFModel.symDn (2 * k + 1)).RealizesVia H (commV H) ⊥ π ∧
            (M ⊓ H).subgroupOf H =
              (MulAction.stabilizer (Equiv.Perm (Fin (2 * k + 1))) (⟨0, by omega⟩ : Fin (2 * k + 1))).map π)

end CFSG.Quasithin
