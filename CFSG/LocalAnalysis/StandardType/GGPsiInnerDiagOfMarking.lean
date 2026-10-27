module

public import CFSG.LocalAnalysis.StandardType.GGInnerDiagMpStdAssembly
public import CFSG.LocalAnalysis.StandardType.GGInterfaceFive

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal
open CFSG.Open (StatedLieTag)

theorem ggPsiInnerDiag_of_marking
    {X : Type} [Group X] [Finite X] {t : StatedLieTag} {n f : ℕ} {ψ : (ggU t n f).K →* X}
    {G₀ A : Subgroup X} (hpres : GGPresentsG0 G₀ (ggU t n f).D t n f ψ)
    (hmark : LargeEvenMarking ↥G₀ (fun _ _ _ I _ θ => ∀ a ∈ A, ∃ φ ∈ I,
      LargeEvenInduces θ (fun l l' => (l' : X) = a⁻¹ * l * a) φ))
    (hAN : A ≤ Subgroup.normalizer (G₀ : Set X)) :
    ∀ a ∈ A, GGPsiInnerDiag (ggU t n f).D ψ a := by
  obtain ⟨⟨hadm, hrk⟩, ⟨hrange, hker⟩, -, -⟩ := hpres
  obtain ⟨-, lab, -, hraw⟩ := ggInnerDiagMpInput_holds X t n f ψ hadm hrk hker G₀ hrange _ hmark
  obtain ⟨R, _, I, F, -, -, θ, hA, himp⟩ := largeEvenRawDatum_exists hraw
  intro a ha
  obtain ⟨φ, hφ, hind⟩ := hA a ha
  exact himp a (hAN ha) ⟨φ, hφ, hind⟩

end CFSG.StandardType
