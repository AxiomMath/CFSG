module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveDataResDefs
import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoRowE

public section

namespace CFSG.StandardType

theorem ggSecFiveDataResAt_F4_of_weylF4Res
    (hF : GGSecFiveWeylF4ResInput)
    (h2 : ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
      (L D J : Subgroup G) (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 →
      ¬ GGSecFiveTier1Region p B Bs x L D J → 2 ≤ 𝒦.card →
      (∀ K ∈ 𝒦, ggAutomizer L Bs ⊔ ggAutomizer K Bs ≠ ggAutomizerJoin L Bs 𝒦) →
      ∀ (ι : Type) (M : CoxeterMatrix ι) (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
        GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e → GGIsWeylMatrixF4 M →
        GGSecFiveData p B x L D J) :
    GGSecFiveDataResAt (fun M => GGIsWeylMatrixF4 M) := by
  intro G _ _ p B Bs x L D J 𝒦 hR hT1 ι M e hP hT
  obtain ⟨e', rfl⟩ := hT
  by_cases h𝒦 : 𝒦.card ≤ 1
  · exact hF G p B Bs x L D J hR.1 hR.2.1
      (hR.weylAt_of_card_le_one h𝒦 e hP).of_reindex hT1
  · by_cases hJ : ∃ K ∈ 𝒦, ggAutomizer L Bs ⊔ ggAutomizer K Bs = ggAutomizerJoin L Bs 𝒦
    · obtain ⟨K, hK, hA⟩ := hJ
      obtain ⟨y, hnbr⟩ := hR.2.2.2.1.2 K hK
      exact hF G p B Bs x L D J hR.1 hR.2.1
        (ggSecFiveWeylAt_of_join_eq hnbr hA e hP).of_reindex hT1
    · exact h2 G p B Bs x L D J 𝒦 hR hT1 (by omega)
        (fun K hK hA => hJ ⟨K, hK, hA⟩) ι _ e hP ⟨e', rfl⟩

end CFSG.StandardType

end
