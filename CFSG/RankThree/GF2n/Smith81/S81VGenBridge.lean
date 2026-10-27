module

public import CFSG.RankThree.GF2n.Smith81.S81Gen76Line

public section

namespace CFSG.RankThree.GF2n.Smith81.S81V

open CFSG.RankThree.GF2n.Smith81.Gen76

variable {K M : Type*} [Field K] [AddCommGroup M] [Module K M]

theorem hGen_of_isLineClosed {Γ : Subgroup (Module.End K M)ˣ} {𝓛₀ Pts : Set (Submodule K M)}
    {Pi : Finset ↥Pts} (hlines : ∀ 𝓛, IsLine Γ 𝓛₀ 𝓛 → 𝓛 ⊆ Pts)
    (hgen : ∀ S : Set (Submodule K M), IsLineClosed Γ 𝓛₀ S →
      (∀ P ∈ Pi, (P : Submodule K M) ∈ S) → Pts ⊆ S) :
    ∀ Q : ↥Pts → Prop, (∀ x ∈ Pi, Q x) →
      (∀ x y z : ↥Pts, Q x → Q y → x ≠ y →
        (∃ 𝓛, IsLine Γ 𝓛₀ 𝓛 ∧ (x : Submodule K M) ∈ 𝓛 ∧ (y : Submodule K M) ∈ 𝓛 ∧
          (z : Submodule K M) ∈ 𝓛) → Q z) →
      ∀ x, Q x := by
  intro Q hPi hcl x
  let S : Set (Submodule K M) := {P | ∃ h : P ∈ Pts, Q ⟨P, h⟩}
  have hS : IsLineClosed Γ 𝓛₀ S := by
    intro 𝓛 h𝓛 P hP P' hP' hne hPS hP'S R hR
    obtain ⟨hPmem, hQP⟩ := hPS
    obtain ⟨hP'mem, hQP'⟩ := hP'S
    refine ⟨hlines 𝓛 h𝓛 hR, ?_⟩
    exact hcl ⟨P, hPmem⟩ ⟨P', hP'mem⟩ ⟨R, hlines 𝓛 h𝓛 hR⟩ hQP hQP'
      (fun h => hne (congrArg Subtype.val h)) ⟨𝓛, h𝓛, hP, hP', hR⟩
  have hPiS : ∀ P ∈ Pi, (P : Submodule K M) ∈ S := fun P hP => ⟨P.2, hPi P hP⟩
  obtain ⟨h, hQ⟩ := hgen S hS hPiS x.2
  exact hQ

end CFSG.RankThree.GF2n.Smith81.S81V
