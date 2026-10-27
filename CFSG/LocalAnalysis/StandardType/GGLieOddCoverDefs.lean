module

public import CFSG.LocalAnalysis.StandardType.GGSixPositionDefs
public import CFSG.Blueprint.Catalog

public section

namespace CFSG.StandardType.LieOddCover

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.StandardType
  CFSG.StandardType.S2MathFi1035Pos
open CFSG.Open (StatedLieTag StatedLieAdmissible)

@[expose] def GGLieOddCover :
    Prop :=
  (∀ (t : StatedLieTag) (n f : ℕ), GGPosTag t → StatedLieAdmissible t n 2 f →
    ∀ (Jb : Type) [Group Jb] [Finite Jb], commutator Jb = ⊤ → Odd (Nat.card (Subgroup.center Jb)) →
      LieModel (Jb ⧸ Subgroup.center Jb) t n 2 f →
      ∃ φ : (ggU t n f).K →* Jb, Function.Surjective φ ∧ φ.ker ≤ Subgroup.center (ggU t n f).K) ∧
  (∀ (g : ℕ), 1 ≤ g → ∀ (Jb : Type) [Group Jb] [Finite Jb], commutator Jb = ⊤ →
    Odd (Nat.card (Subgroup.center Jb)) → LieModel (Jb ⧸ Subgroup.center Jb) .trialityD4 0 2 g →
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (σ : F →+* F), TriField F σ g ∧
      ∃ φ : (triD4Universal F σ).K →* Jb,
        Function.Surjective φ ∧ φ.ker ≤ Subgroup.center (triD4Universal F σ).K)

end CFSG.StandardType.LieOddCover
