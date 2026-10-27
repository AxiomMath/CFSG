module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDGen
public import CFSG.LocalAnalysis.StandardType.GGQTwoDRMBridge
import CFSG.LocalAnalysis.StandardType.GGQTwoDRMFiveJoin
import CFSG.LocalAnalysis.StandardType.GGQTwoDRMFiveType
import CFSG.LocalAnalysis.StandardType.GGQTwoDRMSel
import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitSelModule
import CFSG.LocalAnalysis.StandardType.GGRCTransfer
import CFSG.LocalAnalysis.StandardType.GGSecFiveMaxJoin
import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthWeylOrdD

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

noncomputable section


theorem GGQTwoRMInputOn.or {R R' : ℕ → Prop} (h : GGQTwoRMInputOn R) (h' : GGQTwoRMInputOn R') :
    GGQTwoRMInputOn fun m => R m ∨ R' m := by
  intro G _ _ p B Bs x L D J 𝒦 ι M e hcfg m e' hm hM y K' hN
  rcases hm with hm | hm
  · exact h G p B Bs x L D J 𝒦 ι M e hcfg m e' hm hM y K' hN
  · exact h' G p B Bs x L D J 𝒦 ι M e hcfg m e' hm hM y K' hN

theorem ggQTwoRMInputOn_five_of_inputs (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput)
    (hBase : GGQTwoDRMBaseTypeInputOn fun m => m = 5) : GGQTwoRMInputOn fun m => m = 5 := by
  classical
  intro G _ _ p B Bs x L D J 𝒦 ι M e hcfg m e' hm hM y K' hN
  have hp : p = 3 := by
    obtain ⟨r, hr, hrc, h6⟩ := hcfg.2.2.2.2
    exact ggQTwo_p_eq_three hcfg.1 M e hcfg.2.2.2.1 hr hrc h6
  subst hp
  subst m
  have hAL0 := hBase G 3 B Bs x L D J 𝒦 ι M e hcfg 5 e' rfl hM
  obtain ⟨β, hβ⟩ := ggQTwoD_selectedModule hTBF hWI hcfg e' (by norm_num) hM
  have hsel := qtwoD_image_eq (by norm_num) hM β hβ
  have hcardBs : Nat.card ↥Bs = 3 ^ 5 := card_bs_of_module β
  have hcardM : Nat.card M.Group = 1920 := by
    rw [hM, card_coxeterGroup_reindex]
    rw [OrthF3.card_coxeterD_eq 5 (by norm_num)]
    norm_num
  have hcardJoin : Nat.card ↥(ggAutomizerJoin L Bs 𝒦) = 1920 := by
    rw [← Nat.card_congr e.toEquiv]
    exact hcardM
  have hBs : 3 ^ 5 ≤ Nat.card ↥Bs := hcardBs.ge
  have hALW : GGWeylReflectionGroup 3 (ggAutomizer L Bs) := by
    rcases hAL0 with hA | hD
    · exact ⟨Fin (5 - 1), CoxeterMatrix.A (5 - 1),
        Or.inl ⟨5 - 1, Equiv.refl _, by norm_num, Or.inl rfl⟩, hA⟩
    · exact ⟨Fin (5 - 1), ggCoxeterMatrixD (5 - 1),
        Or.inl ⟨5 - 1, Equiv.refl _, by norm_num,
          Or.inr (Or.inr ⟨by norm_num, rfl⟩)⟩, hD⟩
  obtain ⟨hrest, hwc, -, hmax⟩ := hcfg.1
  obtain ⟨hsetK, -, hbest⟩ := hmax
  by_cases h𝒦 : 𝒦 = ∅
  · have hW0 : GGWeylReflectionGroup 3 (ggAutomizerJoin L Bs {K'}) := by
      rw [ggAutomizerJoin_singleton]
      exact hrest.2.2.2.2.1 y K' hN (hwc y K' hN) (Or.inr hwc)
    have hset : GGNbrSet 3 B x D J {K'} := by
      refine ⟨by simp, ?_⟩
      intro K hKmem
      rw [Finset.mem_singleton] at hKmem
      rw [hKmem]
      exact ⟨y, hN⟩
    have hcard := hbest {K'} hset hW0
    have hle : ggAutomizerJoin L Bs 𝒦 ≤ ggAutomizerJoin L Bs {K'} := by
      rw [h𝒦]
      rw [show ggAutomizerJoin L Bs (∅ : Finset (Subgroup G)) = ggAutomizer L Bs by
        simp [ggAutomizerJoin]]
      rw [ggAutomizerJoin_singleton]
      exact le_sup_left
    have heq : ggAutomizerJoin L Bs 𝒦 = ggAutomizerJoin L Bs {K'} :=
      Subgroup.eq_of_le_of_card_ge hle hcard
    have hK'le : ggAutomizer K' Bs ≤ ggAutomizerJoin L Bs {K'} := by
      rw [ggAutomizerJoin_singleton]
      exact le_sup_right
    rwa [← heq] at hK'le
  · obtain ⟨K₁, hK₁mem⟩ := Finset.nonempty_iff_ne_empty.mpr h𝒦
    obtain ⟨y₁, hK₁nbr⟩ := hsetK.2 K₁ hK₁mem
    have htype1 := qtwoD5_join_type hTBF hWI hcfg.1 hBs hcardJoin.le hK₁nbr
    have hW1le : ggAutomizer L Bs ⊔ ggAutomizer K₁ Bs ≤ ggAutomizerJoin L Bs 𝒦 := by
      rw [ggAutomizerJoin]
      exact sup_le le_sup_left
        ((le_iSup₂ (f := fun K (_ : K ∈ 𝒦) => ggAutomizer K Bs) K₁ hK₁mem).trans
          le_sup_right)
    have hcarddvd : Nat.card ↥(ggAutomizer L Bs ⊔ ggAutomizer K₁ Bs) ∣ 1920 := by
      have h := Subgroup.card_dvd_of_le hW1le
      rwa [hcardJoin] at h
    have hW1eq : ggAutomizer L Bs ⊔ ggAutomizer K₁ Bs = ggAutomizerJoin L Bs 𝒦 := by
      rcases htype1 with ⟨-, hc⟩ | ⟨-, hc⟩
      · rw [hc] at hcarddvd
        exact absurd hcarddvd (by norm_num)
      · exact Subgroup.eq_of_le_of_card_ge hW1le (by rw [hc, hcardJoin])
    have htypeK : GGWeylOfType 3 (CoxeterMatrix.A 5) (ggAutomizer L Bs ⊔ ggAutomizer K' Bs) ∨
        GGWeylOfType 3 (ggCoxeterMatrixD 5) (ggAutomizer L Bs ⊔ ggAutomizer K' Bs) := by
      rcases qtwoD5_join_type hTBF hWI hcfg.1 hBs hcardJoin.le hN with ⟨h, -⟩ | ⟨h, -⟩
      · exact Or.inl h
      · exact Or.inr h
    rcases qtwoD5_join_dichotomy hcfg.1 hALW β hsel hN htypeK with hle | himg
    · exact hle
    · have hpair : ggAutomizerJoin L Bs {K₁, K'} =
          ggAutomizerJoin L Bs {K₁} ⊔ ggAutomizer K' Bs := by
        rw [ggAutomizerJoin, Finset.iSup_insert, Finset.iSup_singleton,
          ggAutomizerJoin_singleton, sup_assoc]
      have hW1eqJoin : ggAutomizerJoin L Bs {K₁} = ggAutomizerJoin L Bs 𝒦 := by
        rw [ggAutomizerJoin_singleton]
        exact hW1eq
      have hpairK : ggAutomizerJoin L Bs {K₁, K'} =
          ggAutomizerJoin L Bs 𝒦 ⊔ ggAutomizer K' Bs := by
        rw [hpair, hW1eqJoin]
      have himg2 : (ggAutomizerJoin L Bs {K₁, K'}).map (ggLin (p := 3) β) = dNormTwo 5 := by
        rw [hpairK]
        exact himg
      have hfact : Fact (Nat.Prime 3) := Nat.fact_prime_three
      have hW2 : GGWeylReflectionGroup 3 (ggAutomizerJoin L Bs {K₁, K'}) := by
        refine ggRC_weylReflGroup_of_linWeyl (p := 3) β _ ?_
        rw [himg2]
        exact linWeyl_dNormTwo_five
      have hsetpair : GGNbrSet 3 B x D J {K₁, K'} := by
        refine ⟨?_, ?_⟩
        · simpa using Finset.card_insert_le K₁ ({K'} : Finset (Subgroup G))
        · intro K hKmem
          simp only [Finset.mem_insert, Finset.mem_singleton] at hKmem
          rcases hKmem with rfl | rfl
          · exact ⟨y₁, hK₁nbr⟩
          · exact ⟨y, hN⟩
      have hcardPair := hbest {K₁, K'} hsetpair hW2
      have hlePair : ggAutomizerJoin L Bs 𝒦 ≤ ggAutomizerJoin L Bs {K₁, K'} := by
        rw [hpairK]
        exact le_sup_left
      have heqPair : ggAutomizerJoin L Bs 𝒦 = ggAutomizerJoin L Bs {K₁, K'} :=
        Subgroup.eq_of_le_of_card_ge hlePair hcardPair
      have hK'le : ggAutomizer K' Bs ≤ ggAutomizerJoin L Bs {K₁, K'} := by
        rw [hpairK]
        exact le_sup_right
      exact heqPair.symm ▸ hK'le

end

end CFSG.StandardType.QTwo

end
