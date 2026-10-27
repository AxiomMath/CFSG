module

public import CFSG.Quasithin.Background.ShultG53Part5
public import CFSG.Quasithin.Background.ShultG53CoverMain

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.ShultG53

open CFSG.CharacterTheory.SteinbergBY CFSG.Quasithin.RonanG51 CFSG.Quasithin.H13.A6 Equiv


theorem six_of_part6 : SixStmt := by
  intro k W w hw0 hHx hgen hline
  fin_cases k
  · exact part6_model 0 W w hw0 hHx hgen hline
  · exact part6_model 1 W w hw0 hHx hgen hline

theorem modelCover : ModelCover :=
  ⟨cover_five_dim, cover5_of_six six_of_part6, six_of_part6⟩

theorem g53_main (G₁ G₂ : Subgroup (Perm (Fin 6))) (c : Perm (Fin 6))
    (hc : c ∈ alternatingGroup (Fin 6))
    (hconj : ((∀ g, g ∈ G₁ ↔ c * g * c⁻¹ ∈ g5G1) ∧ (∀ g, g ∈ G₂ ↔ c * g * c⁻¹ ∈ cA6)) ∨
      ((∀ g, g ∈ G₂ ↔ c * g * c⁻¹ ∈ g5G1) ∧ (∀ g, g ∈ G₁ ↔ c * g * c⁻¹ ∈ cA6)))
    (V₁ V₂ : Md ↥(alternatingGroup (Fin 6)))
    (h₁ : V₁.IsIrred ∧ Nat.card V₁.carrier = 2 ^ 4 ∧ V₁.FixesPoint (inG G₁) ∧
      V₁.FixesLine (inG G₂))
    (h₂ : V₂.IsIrred ∧ Nat.card V₂.carrier = 2 ^ 4 ∧ V₂.FixesPoint (inG G₂) ∧
      V₂.FixesLine (inG G₁))
    (B : LinearMap.BilinForm (ZMod 2) V₁.carrier) (hB1 : ∀ x, B x x = 0)
    (hB2 : ∀ x, (∀ y, B x y = 0) → x = 0)
    (hB3 : ∀ (g : ↥(alternatingGroup (Fin 6))) x y, B (V₁.ρ g x) (V₁.ρ g y) = B x y) :
    Part1 V₁ ∧ Part2 V₁ ∧ Part3 V₁ B ∧ Part4 V₁ B ∧ Part5 V₁ V₂ ∧ Part6 G₁ G₂ V₁ :=
  main_parts modelCover G₁ G₂ c hc hconj V₁ V₂ h₁ h₂ B hB1 hB2 hB3

end CFSG.Quasithin.ShultG53
