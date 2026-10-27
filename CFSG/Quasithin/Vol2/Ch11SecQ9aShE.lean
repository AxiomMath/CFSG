module

public import CFSG.Quasithin.Vol2.Ch11SecQ9aShD
public import CFSG.Quasithin.Vol2.Ch11SecQ9aG2B
public import CFSG.Quasithin.Vol2.Ch11SecSFacts3

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS

open CFSG.Open CFSG.Blueprint C11P9A


theorem C11P9A.exists_parabPair_shape4 (hG1 : FactG2FourParabNonsolv) {Q : Type} [Group Q]
    [Finite Q] (hQ : Shape4 Q) {S : Subgroup Q} (hS : QuasithinUnique.IsSylowTwoOf S ⊤) :
    ∃ B : Fin 2 → Subgroup Q, ParabPair S B := by
  rcases hQ with ⟨K, _, _, hK, ⟨e⟩⟩ | hL | hP | hG
  · obtain ⟨B, hB⟩ := exists_borelPair_sl3 hK e hS
    exact ⟨B, hB.parab⟩
  · rcases hL with ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · exact exists_parabPair_l34 h hS
    · exact absurd h (by norm_num)
    · exact absurd h (by norm_num)
    · exact absurd h (by norm_num)
  · rcases hP with ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · exact exists_parabPair_sp4 le_rfl h hS
    · exact absurd h (by norm_num)
    · exact absurd h (by norm_num)
    · exact absurd h (by norm_num)
  · exact exists_parabPair_g2 hG1 hG hS

theorem factParabTwo_of_g2 (hG1 : FactG2FourParabNonsolv) : FactParabTwo := by
  intro Q _ _ hQ S hS B₁ B₂ B₃ h₁ h₂ h₃
  obtain ⟨B, hB⟩ := exists_parabPair_shape4 hG1 hQ hS
  exact hB.parabTwo h₁ h₂ h₃

theorem factParabGen_of_g2 (hG1 : FactG2FourParabNonsolv) : FactParabGen := by
  intro Q _ _ hQ S hS B₁ B₂ hne h₁ h₂ hp₁ hp₂ hS₁ hS₂ _ _
  obtain ⟨B, hB⟩ := exists_parabPair_shape4 hG1 hQ hS
  exact hB.parabGen hne h₁ h₂ hp₁ hp₂ hS₁ hS₂

theorem factBorelShape_of_g2 (hG1 : FactG2FourParabNonsolv) (hG2 : FactG2FourBorelNorm) :
    FactBorelShape := by
  intro Q _ _ hQ hnot S hS B₁ B₂ hne h₁ h₂
  have hBP : ∃ B : Fin 2 → Subgroup Q, BorelPair S B := by
    rcases hQ with ⟨K, _, _, hK, ⟨e⟩⟩ | hL | hP | hG
    · exact exists_borelPair_sl3 hK e hS
    · rcases hL with ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
      · exact absurd h hnot
      · exact absurd h (by norm_num)
      · exact absurd h (by norm_num)
      · exact absurd h (by norm_num)
    · rcases hP with ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
      · exact exists_borelPair_sp4 h hS
      · exact absurd h (by norm_num)
      · exact absurd h (by norm_num)
      · exact absurd h (by norm_num)
    · exact exists_borelPair_g2 hG1 hG2 hG hS
  obtain ⟨B, hB⟩ := hBP
  exact hB.borelShape hne h₁ h₂

end CFSG.Quasithin.Vol2.Ch11.SecS
