module

public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.LocalAnalysis.StandardType.GGHalfCoords

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def GGHalfNbrCentInput : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (X J R : Subgroup Y) (x : Y) (n : ℕ) (lab : LargeEvenLabel),
    5 ≤ n → CFSG.Assembly.IsQuasisimple ↥X → GGHasLabel lab (↥X ⧸ Subgroup.center ↥X) →
    (lab = ⟨.A, n, 1⟩ ∨ (n = 5 ∧ lab = ⟨.twD, 4, 1⟩) ∨ (n = 7 ∧ lab = ⟨.E6, 0, 1⟩)) →
    x ∈ Subgroup.normalizer (X : Set Y) → x ^ 3 = 1 →
    Nonempty (↥J ≃* Matrix.SpecialLinearGroup (Fin (n - 1)) (GaloisField 2 1)) →
    CFSG.Assembly.IsComponentOf J (X ⊓ Subgroup.centralizer ({x} : Set Y)) →
    R ≤ Subgroup.normalizer (X : Set Y) → R ≤ Subgroup.centralizer (J : Set Y) → ⁅R, R⁆ = R →
    R ≤ Subgroup.centralizer (X : Set Y)

end CFSG.StandardType

end
