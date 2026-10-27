module

public import CFSG.LocalAnalysis.StandardType.GGTableBNoncyclic
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.Assembly.Defs

public section

namespace CFSG.StandardType

open CFSG.Assembly

namespace KGA

@[expose] def GGF4CoreAt (p f : ℕ) (R : Type) [Group R] : Prop :=
  ∀ s : R, s ^ p = 1 → s ≠ 1 → ∀ S : Subgroup R,
    IsComponentOf S (Subgroup.centralizer ({s} : Set R)) →
    GGHasLabel ⟨.C, 3, f⟩ (S ⧸ Subgroup.center S) →
    ∀ g ∈ Subgroup.centralizer ({s} : Set R), ∃ x ∈ S, ∀ y ∈ S, g * y * g⁻¹ = x * y * x⁻¹

@[expose] def GGF4CoreInput : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ f : ℕ, 1 ≤ f →
    LargeEvenLabelAll ⟨.F4, 4, f⟩ fun R _ _ _ => GGF4CoreAt p f R

end KGA

end CFSG.StandardType

end
