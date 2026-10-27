module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveCompatRestN
public import CFSG.LocalAnalysis.StandardType.GGSecFiveMaxJoin
public import CFSG.LocalAnalysis.StandardType.GGSecFivePresTags
public import CFSG.Sporadic.ThSchreier.AutCore
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRegionDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1IdentE
public import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1
public import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1CompatAD

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.ClassicalInvolution.WeakCT

section RegionData

theorem ggSecFiveData_of_region (hAD : GGSecFiveIdentADInput) (hE : GGSecFiveIdentEInput)
    (hJ : GGSecFiveJoinRegionInput) {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} (hReg : GGSecFiveTier1Region p B Bs x L D J) :
    GGSecFiveData p B x L D J := by
  obtain ⟨𝒦, hcfg, hsplit, ι, M, e, hpres, hM⟩ := hReg
  have hident : ∃ (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G), 3 ≤ bnRank t n ∧
      GGPresentsG0 (L ⊔ ⨆ K ∈ 𝒦, K) (ggU t n f).D t n f ψ :=
    hM.elim (hAD G p B Bs x L D J 𝒦 hcfg hsplit ι M e hpres)
      (hE G p B Bs x L D J 𝒦 hcfg hsplit ι M e hpres)
  obtain ⟨t, n, f, ψ, hrank, hpres'⟩ := hident
  obtain ⟨⟨hadm, _⟩, ⟨hrange, hker⟩, _⟩ := hpres'
  have hG0 : ggG0 p B x L D J = L ⊔ ⨆ K ∈ 𝒦, K :=
    hJ G p B Bs x L D J 𝒦 hcfg hsplit ⟨ι, M, e, hpres, hM⟩
  exact Or.inr (Or.inr
    ⟨t, n, f, ggSecFivePres_of_psi_of_admissible hadm hrank ψ hker (hrange.trans hG0.symm)⟩)

theorem ggSecFiveWeylRest5_of_res (hT : GGSecFiveTier1Input) (hJ : GGSecFiveJoinRegionInput)
    (h : GGSecFiveWeylRest5Res) : GGSecFiveWeylRest5 := by
  have hAD := ggSecFiveIdentADInput_of_tier1 hT
  have hE := ggSecFiveIdentEInput_of_tier1 hT
  obtain ⟨hA, hB, hD, hEr, hF⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro G _ _ p B Bs x L D J hR hW hAt hNb
    by_cases hReg : GGSecFiveTier1Region p B Bs x L D J
    · exact ggSecFiveData_of_region hAD hE hJ hReg
    · exact hA G p B Bs x L D J hR hW hAt hNb hReg
  · intro G _ _ p B Bs x L D J hR hW hAt hH hC
    by_cases hReg : GGSecFiveTier1Region p B Bs x L D J
    · exact ggSecFiveData_of_region hAD hE hJ hReg
    · exact hB G p B Bs x L D J hR hW hAt hH hC hReg
  · intro G _ _ p B Bs x L D J hR hW hAt
    by_cases hReg : GGSecFiveTier1Region p B Bs x L D J
    · exact ggSecFiveData_of_region hAD hE hJ hReg
    · exact hD G p B Bs x L D J hR hW hAt hReg
  · intro G _ _ p B Bs x L D J hR hW hAt
    by_cases hReg : GGSecFiveTier1Region p B Bs x L D J
    · exact ggSecFiveData_of_region hAD hE hJ hReg
    · exact hEr G p B Bs x L D J hR hW hAt hReg
  · intro G _ _ p B Bs x L D J hR hW hAt
    by_cases hReg : GGSecFiveTier1Region p B Bs x L D J
    · exact ggSecFiveData_of_region hAD hE hJ hReg
    · exact hF G p B Bs x L D J hR hW hAt hReg

theorem ggSecFiveCompatRestWInput'_of_res (hT : GGSecFiveTier1Input)
    (hC : GGSecFiveCompatLeviInput) (hJ : GGSecFiveJoinRegionInput)
    (h : GGSecFiveCompatRestWResInput) : GGSecFiveCompatRestWInput' := by
  have hAD := ggSecFiveIdentCompatADInput_of_tier1 hT hC
  have hE := ggSecFiveIdentCompatEInput_of_tier1 hT hC
  intro G _ _ p B Bs x L D J hcfg hOp hInn hNT hW hd t n f ψ hpres hL
  by_cases hReg : GGSecFiveTier1Region p B Bs x L D J
  · obtain ⟨𝒦, hrc, hsplit, ι, M, e, hp, hM⟩ := hReg
    have hident : ∃ (t' : StatedLieTag) (n' f' : ℕ) (ψ' : (ggU t' n' f').K →* G),
        3 ≤ bnRank t' n' ∧
          GGPresentsG0 (L ⊔ ⨆ K ∈ 𝒦, K) (ggU t' n' f').D t' n' f' ψ' ∧
            GGCompatPresented (ggU t' n' f').D ψ' L :=
      hM.elim (hAD G p B Bs x L D J 𝒦 hrc hsplit ι M e hp)
        (hE G p B Bs x L D J 𝒦 hrc hsplit ι M e hp)
    obtain ⟨t', n', f', ψ', -, hpres', hcompat⟩ := hident
    have hG0 : ggG0 p B x L D J = L ⊔ ⨆ K ∈ 𝒦, K :=
      hJ G p B Bs x L D J 𝒦 hrc hsplit ⟨ι, M, e, hp, hM⟩
    rw [← hG0] at hpres'
    exact ⟨t', n', f', ψ', hpres', L, Or.inl rfl, hcompat⟩
  · exact h G p B Bs x L D J hcfg hOp hInn hNT hW hd t n f ψ hpres hL hReg

end RegionData

end CFSG.StandardType

end
