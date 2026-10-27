module

public import CFSG.LocalAnalysis.UniquenessCase.UCKOutPB
public import CFSG.LocalAnalysis.UniquenessCase.UCKInputs3
public import CFSG.HardMathSupport.Lang.Coordinator.ONanOuterSylowCyc
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.OuterArith

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open CFSG.Open
open CFSG.ComponentClassification.CatLeaf (lieOrderDivisor LieOrderFormulasInput)
open CFSG.ComponentClassification.OuterAutomorphisms (equivalence)
open CFSG.AGLEmbedding.OuterSylow (mem_inner_of_not_dvd_card_outer mem_inner_of_lie_model_cyc)
open CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis (dvd_lieOrderDivisor_cases)

section KOutP


theorem kOutP_of_fixedOrder (hLie : LieOrderFormulasInput)
    (hb : CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderBoundCyc) : KOutP := by
  intro J _ _ hs hK p hp h5 hpJ hrank T hT α hαo hαT
  have : IsSimpleGroup J := hs
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have hαp : α ^ p = 1 := by
    have := pow_orderOf_eq_one α
    rwa [hαo] at this
  obtain ⟨-, hTp, hTi⟩ := CFSG.ABGLocalTools.isSylowOf_iff.1 hT
  rw [Subgroup.relIndex_top_right] at hTi
  by_cases hnab : ∃ a b : J, a * b ≠ b * a
  swap
  ·
    exfalso
    push Not at hnab
    have hTn : T.Normal := ⟨fun x hx g => by rwa [hnab g x, mul_inv_cancel_right]⟩
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal T with hbot | htop
    · rw [hbot, Subgroup.index_bot] at hTi
      exact hTi hpJ
    · have hα1 : α = 1 := MulEquiv.ext fun x => hαT x (htop ▸ Subgroup.mem_top x)
      rw [hα1, orderOf_one] at hαo
      omega
  have hcat : IsCatalogGroup J :=
    hK.isCatalogGroup_of_surjective ⊤ hnab (Subgroup.subtype ⊤) (fun x => ⟨⟨x, trivial⟩, rfl⟩)
  rcases CFSG.RankThree.PartOne.PlaneCases.catalog_cases
      (CFSG.RankThree.PartOne.TCB.tauCetiCatalogBridge J hnab hcat) with
    ⟨q, hq, ⟨e⟩⟩ | ⟨n, hn5, ⟨e⟩⟩ | ⟨t, n, ℓ, f, hadm, hmodel⟩ | ⟨s, ⟨e⟩⟩
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    exact hab (e.injective (by rw [map_mul, map_mul, mul_comm]))
  · refine mem_inner_of_not_dvd_card_outer hp ?_ hαp
    rw [Nat.card_congr (equivalence e).toEquiv]
    exact CFSG.AGLEmbedding.not_dvd_card_outer_alternatingGroup n hn5 p hp hp2
  · by_cases ht : t = .Tits
    · subst ht
      rcases hmodel with ⟨h, -⟩ | ⟨-, h, -⟩ | ⟨-, -, hree⟩ | ⟨-, h, -⟩
      · simp [CFSG.Blueprint.classicalTags] at h
      · simp [CFSG.Blueprint.chevalleyExceptionalTags] at h
      · have h2grp := (CFSG.Sporadic.Schreier.Tits.AT_Tits_model_Schreier J ℓ f hree).1
        obtain ⟨k, hk⟩ := h2grp.exists_card_eq
        refine mem_inner_of_not_dvd_card_outer hp (fun hd => ?_) hαp
        rw [hk] at hd
        exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hd))
      · cases h
    · by_cases hdiv : p ∣ lieOrderDivisor t n (ℓ ^ f)
      · rcases dvd_lieOrderDivisor_cases hp h5 hdiv with ⟨rfl, hpn, hpq⟩ | ⟨rfl, hpn, hpq⟩
        · exact OutP.kOutP_psl (hmodel.statedClassicalModel (by decide)) hp h5 hpn hpq hrank hTp
            hTi α hαo hαT
        · exact OutP.kOutP_psu (hmodel.statedClassicalModel (by decide)) hp h5 hpn hpq hrank hTp
            hTi α hαo hαT
      · have hD4 : ¬ (t = .POmegaPlus ∧ n = 4 ∧ p = 3) := fun h => by omega
        have hT3 : ¬ (t = .trialityD4 ∧ p = 3) := fun h => by omega
        exact mem_inner_of_lie_model_cyc hLie hb hadm hmodel ht hp hp2 hpJ hdiv hD4 hT3 hTp hTi hαp
          hαT
  · have hbr := CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group
    obtain ⟨e'⟩ := hbr s
    refine mem_inner_of_not_dvd_card_outer hp ?_ hαp
    rw [Nat.card_congr (equivalence (e.trans e')).toEquiv]
    exact CFSG.AGLEmbedding.not_dvd_card_outer_sporadic hbr s p hp hp2

theorem kOutP_holds : KOutP :=
  kOutP_of_fixedOrder CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput
    CFSG.HardMathSupport.Lang.Coordinator.outerFixedOrderBoundCyc_holds

end KOutP

end CFSG.LocalAnalysis.UniquenessCase.UCK
