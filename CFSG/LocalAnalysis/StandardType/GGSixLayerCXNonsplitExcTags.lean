module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitExcCore
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitKGOmRound8
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsExcDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Minuscule LayerFacts

section Tags

@[expose] def GGExcNonsplitCoreInput (τ : Tag) : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (p : ℕ), p.Prime → p ≠ 2 →
    ¬ p ∣ Nat.card K - 1 → ¬ p ∣ Nat.card K + 1 →
      ExcNonsplit.GGNonsplitCoreAt ↥(adjointGroup τ K) p

theorem ggNonsplitTag_F4_of_core (h : GGExcNonsplitCoreInput .F4) : GGNonsplitTag .F4 := by
  refine ⟨fun G _ _ n f ψ G₀ hpres p hp hp2 hq1 hq2 x y hx hy hxy _ _ hxD hyD K hK hpK => ?_,
    fun G _ _ n f ψ G₀ hpres p hp hp2 hq1 hq2 x y hx hy hxy _ _ hxD hyD K K' hK hpK hK' hKK' _ =>
      ?_⟩
  all_goals
    obtain ⟨⟨hadm, -⟩, ⟨hrange, hker⟩, -, -⟩ := hpres
    subst hrange
    have hF : Nat.card (GaloisField 2 f) = 2 ^ f :=
      GaloisField.card 2 f (by have := hadm.2.1; omega)
    have hZ : Subgroup.center ↥(adjointGroup .F4 (GaloisField 2 f)) = ⊥ :=
      center_adjointGroup_eq_bot
    have hinj : Function.Injective ψ := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      exact hker.trans hZ.le
    obtain ⟨s, hs⟩ := LayerPDiv.exists_mem_ggConjPairs_of_inner
      (PsiDiag.Adj.exists_mem_centralizer_F4 (K := GaloisField 2 f) ψ hker hxD)
    obtain ⟨t, ht⟩ := LayerPDiv.exists_mem_ggConjPairs_of_inner
      (PsiDiag.Adj.exists_mem_centralizer_F4 (K := GaloisField 2 f) ψ hker hyD)
    obtain ⟨K'', hK'', hKK'', hm⟩ := ExcNonsplit.exists_component_of_core
      (L := ↥(adjointGroup .F4 (GaloisField 2 f))) hZ hinj
      (h (GaloisField 2 f) p hp hp2 (by rwa [hF]) (by rwa [hF])) hx hy hxy hs ht hK hpK
  · exact ⟨K'', hK'', hKK''⟩
  · obtain rfl := OmNonsplit.eq_of_isComponentOf_of_le hK' hK''
      ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native K).mp hK.2.2)
      hKK' hKK''
    exact hm

theorem ggNonsplitTag_E8_of_core (h : GGExcNonsplitCoreInput .E8) : GGNonsplitTag .E8 := by
  refine ⟨fun G _ _ n f ψ G₀ hpres p hp hp2 hq1 hq2 x y hx hy hxy _ _ hxD hyD K hK hpK => ?_,
    fun G _ _ n f ψ G₀ hpres p hp hp2 hq1 hq2 x y hx hy hxy _ _ hxD hyD K K' hK hpK hK' hKK' _ =>
      ?_⟩
  all_goals
    obtain ⟨⟨hadm, -⟩, ⟨hrange, hker⟩, -, -⟩ := hpres
    subst hrange
    have hF : Nat.card (GaloisField 2 f) = 2 ^ f :=
      GaloisField.card 2 f (by have := hadm.2.1; omega)
    have hZ : Subgroup.center ↥(adjointGroup .E8 (GaloisField 2 f)) = ⊥ :=
      center_adjointGroup_eq_bot
    have hinj : Function.Injective ψ := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      exact hker.trans hZ.le
    obtain ⟨s, hs⟩ := LayerPDiv.exists_mem_ggConjPairs_of_inner
      (PsiDiag.Adj.exists_mem_centralizer_E8 (K := GaloisField 2 f) ψ hker hxD)
    obtain ⟨t, ht⟩ := LayerPDiv.exists_mem_ggConjPairs_of_inner
      (PsiDiag.Adj.exists_mem_centralizer_E8 (K := GaloisField 2 f) ψ hker hyD)
    obtain ⟨K'', hK'', hKK'', hm⟩ := ExcNonsplit.exists_component_of_core
      (L := ↥(adjointGroup .E8 (GaloisField 2 f))) hZ hinj
      (h (GaloisField 2 f) p hp hp2 (by rwa [hF]) (by rwa [hF])) hx hy hxy hs ht hK hpK
  · exact ⟨K'', hK'', hKK''⟩
  · obtain rfl := OmNonsplit.eq_of_isComponentOf_of_le hK' hK''
      ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native K).mp hK.2.2)
      hKK' hKK''
    exact hm

theorem ggNonsplitTag_E7_of_core (h : GGExcNonsplitCoreInput .E7) : GGNonsplitTag .E7 := by
  refine ⟨fun G _ _ n f ψ G₀ hpres p hp hp2 hq1 hq2 x y hx hy hxy _ _ hxD hyD K hK hpK => ?_,
    fun G _ _ n f ψ G₀ hpres p hp hp2 hq1 hq2 x y hx hy hxy _ _ hxD hyD K K' hK hpK hK' hKK' _ =>
      ?_⟩
  all_goals
    obtain ⟨⟨hadm, -⟩, ⟨hrange, hker⟩, -, -⟩ := hpres
    subst hrange
    have hF : Nat.card (GaloisField 2 f) = 2 ^ f :=
      GaloisField.card 2 f (by have := hadm.2.1; omega)
    have hZ : Subgroup.center ↥(e7Data_valid.minGroup (GaloisField 2 f)) = ⊥ :=
      CFSG.SeitzReduction.E8Pilot.center_minGroup_e7_eq_bot
    have hinj : Function.Injective ψ := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      exact hker.trans hZ.le
    have hcore : ExcNonsplit.GGNonsplitCoreAt ↥(e7Data_valid.minGroup (GaloisField 2 f)) p :=
      ExcNonsplit.ggNonsplitCoreAt_of_mulEquiv
        (CFSG.SeitzReduction.E8Pilot.e7MinEquivAdjoint (GaloisField 2 f))
        center_adjointGroup_eq_bot (h (GaloisField 2 f) p hp hp2 (by rwa [hF]) (by rwa [hF]))
    obtain ⟨s, hs⟩ := LayerPDiv.exists_mem_ggConjPairs_of_inner
      (PsiDiag.Minu.exists_mem_centralizer_E7 ψ hker hxD)
    obtain ⟨t, ht⟩ := LayerPDiv.exists_mem_ggConjPairs_of_inner
      (PsiDiag.Minu.exists_mem_centralizer_E7 ψ hker hyD)
    obtain ⟨K'', hK'', hKK'', hm⟩ := ExcNonsplit.exists_component_of_core
      (L := ↥(e7Data_valid.minGroup (GaloisField 2 f))) hZ hinj hcore hx hy hxy hs ht hK hpK
  · exact ⟨K'', hK'', hKK''⟩
  · obtain rfl := OmNonsplit.eq_of_isComponentOf_of_le hK' hK''
      ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native K).mp hK.2.2)
      hKK' hKK''
    exact hm

end Tags

section Assembly


theorem ggNonsplitRound8_of_excCore (hF4 : GGExcNonsplitCoreInput .F4)
    (hE7 : GGExcNonsplitCoreInput .E7) (hE8 : GGExcNonsplitCoreInput .E8)
    (hE6 : GGNonsplitTag .E6) (hTwE6 : GGNonsplitTag .twistedE6) :
    GGNonsplitCompLiftRound8 ∧ GGNonsplitNbrMarkingRound8 :=
  have h4 := ggNonsplitTag_F4_of_core hF4
  have h7 := ggNonsplitTag_E7_of_core hE7
  have h8 := ggNonsplitTag_E8_of_core hE8
  ⟨ggNonsplitCompLiftRound8_of_exc h4.1 hE6.1 h7.1 h8.1 hTwE6.1,
    ggNonsplitNbrMarkingRound8_of_exc h4.2 hE6.2 h7.2 h8.2 hTwE6.2⟩

theorem ggSixLayerCXNonsplitInput_of_excCore (hF4 : GGExcNonsplitCoreInput .F4)
    (hE7 : GGExcNonsplitCoreInput .E7) (hE8 : GGExcNonsplitCoreInput .E8)
    (hE6 : GGNonsplitTag .E6) (hTwE6 : GGNonsplitTag .twistedE6) : GGSixLayerCXNonsplitInput :=
  ggSixLayerCXNonsplitInput_of_tags_exc (ggNonsplitTag_F4_of_core hF4) hE6
    (ggNonsplitTag_E7_of_core hE7) (ggNonsplitTag_E8_of_core hE8) hTwE6

end Assembly

end CFSG.StandardType
