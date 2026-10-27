module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven

open Subgroup
open scoped commutatorElement

@[expose] def KOddLieNormSylowAlpha : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (L : Subgroup A), L.Normal → IsSimpleGroup ↥L →
    centralizer (L : Set A) = ⊥ → ∀ (t : CFSG.Open.StatedLieTag) (n r f : ℕ), r ≠ 2 →
      CFSG.Open.StatedLieAdmissible t n r f → CFSG.Blueprint.LieModel ↥L t n r f →
      t ≠ .twistedG2 →
      ∀ (s p : ℕ) (T B : Subgroup A), Odd s → p.Prime → p ∣ 2 ^ s - 1 →
        CFSG.ABGLocalTools.IsSylowOf 2 T ⊤ → B ≤ normalizer (T : Set A) → Nat.card B = p →
        ⁅T, B⁆ = ⊥

@[expose] def UC2_10_7OddRee : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (L : Subgroup A), L.Normal → IsSimpleGroup ↥L →
    centralizer (L : Set A) = ⊥ → ∀ f : ℕ, CFSG.Blueprint.LieModel ↥L .twistedG2 0 3 f →
    ∀ (s p : ℕ) (T B M : Subgroup A), Odd s → p.Prime → p ∣ 2 ^ s - 1 →
      CFSG.ABGLocalTools.IsSylowOf 2 T ⊤ → B ≤ normalizer (T : Set A) → Nat.card B = p →
      L ⊔ T ⊔ B = ⊤ → T ≤ M → B ≤ M → (∀ g : A, (∀ b ∈ B, g⁻¹ * b * g ∈ M) → g ∈ M) →
      L ≤ M ∨ ⁅T, B⁆ = ⊥

theorem uc2_10_7Odd_of_kfacts (hK : KOddLieNormSylowAlpha) (hR : UC2_10_7OddRee) :
    UC2_10_7Odd := by
  intro A _ _ L hLn hLs hCL r hr hr2 hchev s p T B M hs hp hdvd hT hBT hBp hsup hTM hBM hstar
  obtain ⟨t, n, f, hadm, hmod⟩ := hchev
  by_cases ht : t = .twistedG2
  · subst ht
    obtain ⟨-, -, hn, hr3, -, -⟩ := hadm
    subst hn
    subst hr3
    exact hR A L hLn hLs hCL f hmod s p T B M hs hp hdvd hT hBT hBp hsup hTM hBM hstar
  · exact Or.inr (hK A L hLn hLs hCL t n r f hr2 hadm hmod ht s p T B hs hp hdvd hT hBT hBp)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven
