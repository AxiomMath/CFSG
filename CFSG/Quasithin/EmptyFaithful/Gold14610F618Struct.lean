module

public import CFSG.Quasithin.EmptyFaithful.Gold14610F618StructCase3
public import CFSG.Quasithin.EmptyFaithful.Gold14610F618StructM12
public import CFSG.Quasithin.EmptyFaithful.Gold14610F618StructSL3
public import CFSG.Quasithin.EmptyFaithful.Gold14610F618StructSym
public import CFSG.Quasithin.EmptyFaithful.Gold14610F618StructFieldExt
public import CFSG.Quasithin.EmptyFaithful.Gold14610F618StructPGL
public import CFSG.Quasithin.EmptyFaithful.Gold14610F618StructSimple

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace Gold14610

namespace Struct

section Certs


theorem case3_or_idx2Data {D : Type} [Group D] {H₁ H₂ : Subgroup D}
    (h : F6.IsF618CaseOrientedCat H₁ H₂) (h1 : ¬ F6.IsF618CaseOne H₁ H₂)
    (h2 : ¬ F6.IsF618CaseTwo D) : F6.IsF618CaseThree H₁ H₂ ∨ Idx2Data D := by
  rcases h with hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc
  · exact absurd hc h1
  · exact absurd hc h2
  · exact Or.inl hc
  · obtain ⟨⟨p, hp, hp24, hL⟩, -⟩ := hc
    exact Or.inr (idx2Data_of_isL2_one hp hp24 hL)
  · obtain ⟨⟨q, hq, hq24, hP⟩, -⟩ := hc
    exact Or.inr (idx2Data_of_isPGL2 hq hq24 hP)
  · obtain ⟨hD | ⟨p, e, hp, he1, he2, h16, hL⟩, -⟩ := hc
    · exact Or.inr (idx2Data_of_isHatAlt_six hD)
    · exact Or.inr (idx2Data_of_isL2 hp he1 he2 h16 hL)
  · obtain ⟨hD | hD, -⟩ := hc
    · exact Or.inr (idx2Data_of_alt_seven hD)
    · exact Or.inr (idx2Data_of_isHatAlt_seven hD)
  · obtain ⟨hD | ⟨p, hp, hp8, hL⟩, -⟩ := hc
    · exact Or.inr (idx2Data_of_isHatSym_six hD)
    · exact Or.inr (idx2Data_of_isL2FieldExtCat hp8 hL)
  · obtain ⟨hD | hD | ⟨p, hp, hp24, hL⟩, -⟩ := hc
    · exact Or.inr (idx2Data_of_perm_seven hD)
    · exact Or.inr (idx2Data_of_isHatSym_seven hD)
    · exact Or.inr (idx2Data_of_isL2FieldExtCat (by omega) hL)
  · obtain ⟨⟨p, hp8, hD⟩, -⟩ := hc
    exact Or.inr (idx2Data_of_isSLEps3 hp8 hD)
  · obtain ⟨⟨p, hp8, hD⟩, -⟩ := hc
    exact Or.inr (idx2Data_of_isSLEps3GraphExt hp8 hD)
  · exact Or.inr (idx2Data_of_isM12 hc.1)
  · exact Or.inr (idx2Data_of_isAutM12 hc.1)

theorem gold14610F618Struct_proved : Gold14610F618Struct := by
  intro D _ _ D₁ D₂ hA hconc h1 h2 hC2
  have hT := hA.toIsGoldschmidtTriple
  have hmain : F6.IsF618CaseThree D₁ D₂ ∨ F6.IsF618CaseThree D₂ D₁ ∨ Idx2Data D := by
    rcases hconc with hc | hc
    · rcases case3_or_idx2Data hc h1 hC2 with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
    · rcases case3_or_idx2Data hc h2 hC2 with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
  rcases hmain with h | h | h
  · obtain ⟨Kb, hc, hn, hcore, hrest⟩ := case3_conclusion hT (Or.inl h)
    exact ⟨Kb, hc, hn, hcore, Or.inr hrest⟩
  · obtain ⟨Kb, hc, hn, hcore, hrest⟩ := case3_conclusion hT (Or.inr h)
    exact ⟨Kb, hc, hn, hcore, Or.inr hrest⟩
  · obtain ⟨Kb, hc, hn, hcore, hsup, h1', h2'⟩ := idx2Comp_of_data hT h
    exact ⟨Kb, hc, hn, hcore, Or.inl ⟨hsup, h1', h2'⟩⟩

end Certs

end Struct

end Gold14610

end CFSG.Quasithin
