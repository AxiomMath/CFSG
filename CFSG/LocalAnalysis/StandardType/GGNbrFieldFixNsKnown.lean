module

public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixKnownSp
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixKnownTwOmega
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixNsDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

open FieldFixSp in
theorem ggFieldFixKnown_spNs :
    GGFieldFixKnown fun p lab => GGFieldFixNsLabel p lab ∧ (lab.tag = .B ∨ lab.tag = .C) := by
  intro p lab hp hp2 hlab hS
  obtain ⟨⟨-, ⟨-, hrow⟩, -⟩, hBC⟩ := hS
  have h3 : 3 ≤ lab.rank := by
    rcases hrow with ⟨-, h⟩ | ⟨hD, -⟩ | ⟨hT, -⟩
    · omega
    · rcases hBC with hB | hB <;> rw [hB] at hD <;> cases hD
    · rcases hBC with hB | hB <;> rw [hB] at hT <;> cases hT
  have hn : 1 ≤ lab.n := hlab.1
  intro Q hQ
  obtain ⟨t, l, n⟩ := lab
  dsimp only at hBC h3 hn
  haveI : NeZero l := ⟨by omega⟩
  rcases hBC with ht | ht <;> subst ht <;>
  · dsimp only [LargeEvenRawDatum] at hQ ⊢
    refine NbrGraphSymplectic.recipeSymplectic_all (fun K _ _ hK => ?_) hQ
    haveI : CharP K 2 := charP_two_of_card hK
    intro hS hna f hf hord
    exact exists_fixGeom h3 hn hp hp2 hK hS hna hf hord

open FieldFixTwOmega in
theorem ggFieldFixKnown_twOmegaNs :
    GGFieldFixKnown fun p lab => GGFieldFixNsLabel p lab ∧ lab.tag = .twD := by
  intro p lab hp hp2 hlab hS
  obtain ⟨⟨-, ⟨-, hrow⟩, -⟩, ht⟩ := hS
  have h4 : 4 ≤ lab.rank := by
    rcases hrow with ⟨hBC, -⟩ | ⟨hD, h4, -⟩ | ⟨-, h5, -⟩
    · rcases hBC with h | h <;> rw [ht] at h <;> cases h
    · rw [ht] at hD; cases hD
    · omega
  have hn : 1 ≤ lab.n := hlab.1
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht h4 hn
  subst ht
  refine largeEvenLabelAll_omegaMinus (lab := ⟨.twD, l, n⟩) rfl h4 fun K _ _ _ hK b c hirr => ?_
  intro hS' hna f hf hord
  have h2 : l ≠ 2 := by omega
  have h3 : l ≠ 3 := by omega
  dsimp only [LargeEvenRawDatum]
  simp only [h2, h3, ↓reduceIte]
  exact exists_fixGeom h4 hn hp hp2 hK hirr hS' hna hf hord

end CFSG.StandardType

end
