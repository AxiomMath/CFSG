module

public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeAEndModel

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem ggTorusTBGroup_false_of_card_lt {p r : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}
    (hcard : ∀ X : Subgroup (MulAut R), (X : Set (MulAut R)) ⊆ I → IsElemAbelian p X →
      Nat.card X < p ^ 3)
    {L' : Type} [Group L'] [Finite L'] {ψ : L' →* R} {A : Subgroup (MulAut L')}
    (hA : GGTorusTBGroup p r R I L' ψ A) : False := by
  obtain ⟨hψ, hker, hperf, hAe, hAI, _hr, h3, _hsc⟩ := hA
  have hXI : ((TypeA.inducedSub ψ A : Subgroup (MulAut R)) : Set (MulAut R)) ⊆ I := by
    rintro φ ⟨a, ha, hφa⟩
    obtain ⟨φa, hφaI, hφa'⟩ := hAI a ha
    exact TypeA.induced_unique ψ hψ hφa' hφa ▸ hφaI
  have hXab : IsElemAbelian p (TypeA.inducedSub ψ A) :=
    TypeA.isElemAbelian_inducedSub hψ hAe
  have hcardX : Nat.card (TypeA.inducedSub ψ A) = Nat.card A :=
    TypeA.card_inducedSub hψ hker hperf fun a ha => by
      obtain ⟨φa, -, hφa⟩ := hAI a ha
      exact ⟨φa, hφa⟩
  have hlt := hcard (TypeA.inducedSub ψ A) hXI hXab
  rw [hcardX] at hlt
  exact absurd hlt (not_lt.mpr h3)

end CFSG.StandardType

end
