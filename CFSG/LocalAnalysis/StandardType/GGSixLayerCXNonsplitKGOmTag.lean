module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitKGOmSpin
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitKGClHerm
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitKGClAltSix
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitKGSLTag

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin QuadraticMap LayerCores LayerFacts

namespace OmNonsplit

section SpinGroups

variable {G : Type} [Group G] [Finite G] {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]

theorem exists_component_spinPlus (hn : 3 ≤ n) {ψ : spinGroup (quadPlus n F) →* G}
    (hker : ψ.ker ≤ Subgroup.center (spinGroup (quadPlus n F))) {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hF : Nat.card F = 2 ^ f) (hq1 : ¬ p ∣ 2 ^ f - 1) (hq2 : ¬ p ∣ 2 ^ f + 1)
    {x y : G} (hx : x ^ p = 1) (hy : y ^ p = 1) (hxy : x * y = y * x)
    (hxD : GGPsiInnerDiag (plusDatum n F hn) ψ x) (hyD : GGPsiInnerDiag (plusDatum n F hn) ψ y)
    {K : Subgroup G} (hK : IsComponentOf K (ψ.range ⊓ Subgroup.centralizer {x}))
    (hpK : ¬ p ∣ Nat.card K) :
    ∃ K'' : Subgroup G, IsComponentOf K'' (ψ.range ⊓ Subgroup.centralizer {y}) ∧ K ≤ K'' ∧
      (∃ k ∈ K'', ∀ l ∈ K'', x⁻¹ * l * x = k⁻¹ * l * k) ∧ OmModel F K'' := by
  have hZ := RootCentOmega.center_spinGroup_quadPlus_eq_bot_charTwo (K := F) hn
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff, ← hZ]
    exact hker
  obtain ⟨s, hs⟩ := LayerPDiv.exists_mem_ggConjPairs_of_inner
    (PsiDiag.SpinP.exists_mem_centralizer hn ψ hker hxD)
  obtain ⟨t, ht⟩ := LayerPDiv.exists_mem_ggConjPairs_of_inner
    (PsiDiag.SpinP.exists_mem_centralizer hn ψ hker hyD)
  exact exists_component_spin (nondegenerate_polarBilin_quadPlus n F)
    RootCentOmega.spinAction_quadPlus_injective (range_spinAction_quadPlus_eq_commutator hn) hZ
    hinj hp hp2 hF hq1 hq2 hx hy hxy hs ht hK hpK

theorem exists_component_spinMinus {b c : F} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (hn : 4 ≤ n) {ψ : spinGroup (quadMinus n F b c) →* G}
    (hker : ψ.ker ≤ Subgroup.center (spinGroup (quadMinus n F b c))) {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hF : Nat.card F = 2 ^ f) (hq1 : ¬ p ∣ 2 ^ f - 1) (hq2 : ¬ p ∣ 2 ^ f + 1)
    {x y : G} (hx : x ^ p = 1) (hy : y ^ p = 1) (hxy : x * y = y * x)
    (hxD : GGPsiInnerDiag (Spin.Twisted.minusDatum n hirr) ψ x)
    (hyD : GGPsiInnerDiag (Spin.Twisted.minusDatum n hirr) ψ y)
    {K : Subgroup G} (hK : IsComponentOf K (ψ.range ⊓ Subgroup.centralizer {x}))
    (hpK : ¬ p ∣ Nat.card K) :
    ∃ K'' : Subgroup G, IsComponentOf K'' (ψ.range ⊓ Subgroup.centralizer {y}) ∧ K ≤ K'' ∧
      (∃ k ∈ K'', ∀ l ∈ K'', x⁻¹ * l * x = k⁻¹ * l * k) ∧ OmModel F K'' := by
  have hZ := PsiDiag.SpinM.center_eq_bot hirr hn
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff, ← hZ]
    exact hker
  obtain ⟨s, hs⟩ := LayerPDiv.exists_mem_ggConjPairs_of_inner
    (PsiDiag.SpinM.exists_mem_centralizer hirr hn ψ hker hxD)
  obtain ⟨t, ht⟩ := LayerPDiv.exists_mem_ggConjPairs_of_inner
    (PsiDiag.SpinM.exists_mem_centralizer hirr hn ψ hker hyD)
  exact exists_component_spin (nondegenerate_polarBilin_quadMinus_of_finite n F hirr)
    (RootCentOmega.spinAction_quadMinus_injective hirr)
    (range_spinAction_quadMinus_eq_commutator hn hirr) hZ hinj hp hp2 hF hq1 hq2 hx hy hxy hs ht
    hK hpK

end SpinGroups

end OmNonsplit

section CompLift

theorem ggNonsplitCompLiftTag_POmegaPlus : GGNonsplitCompLiftTag .POmegaPlus := by
  intro G _ _ n f
  by_cases hn : 3 ≤ n
  · rw [show ggU .POmegaPlus n f = ⟨spinGroup (quadPlus n (GaloisField 2 f)),
        plusDatum n (GaloisField 2 f) hn⟩ from dite_eq_left hn]
    intro ψ G₀ hpres p hp hp2 hq1 hq2 x y hx hy hxy _ _ hxD hyD K hK hpK
    obtain ⟨⟨hadm, -⟩, ⟨hrange, hker⟩, -, -⟩ := hpres
    subst hrange
    have hF : Nat.card (GaloisField 2 f) = 2 ^ f :=
      GaloisField.card 2 f (by have := hadm.2.1; omega)
    obtain ⟨K'', hK'', hKK'', -, -⟩ := OmNonsplit.exists_component_spinPlus hn hker hp hp2 hF
      hq1 hq2 hx hy hxy hxD hyD hK hpK
    exact ⟨K'', hK'', hKK''⟩
  · rw [show ggU .POmegaPlus n f = trivialUniversal from dite_eq_right hn]
    intro ψ G₀ hpres
    exact absurd hpres.1.2 (by decide)

theorem ggNonsplitCompLiftTag_POmegaMinus : GGNonsplitCompLiftTag .POmegaMinus := by
  intro G _ _ n f ψ G₀ hpres p hp hp2 hq1 hq2 x y hx hy hxy _ _ hxD hyD K hK hpK
  obtain ⟨⟨hadm, -⟩, ⟨hrange, hker⟩, -, -⟩ := hpres
  obtain ⟨-, hf, hn⟩ := hadm
  subst hrange
  have hF : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  obtain ⟨K'', hK'', hKK'', -, -⟩ := OmNonsplit.exists_component_spinMinus
    (F := GaloisField 2 f) (minusCoeffs_irr 2 f) hn hker hp hp2 hF hq1 hq2 hx hy hxy hxD hyD hK
    hpK
  exact ⟨K'', hK'', hKK''⟩

end CompLift

section Marking

theorem ggNonsplitNbrMarkingTag_POmegaPlus : GGNonsplitNbrMarkingTag .POmegaPlus := by
  intro G _ _ n f
  by_cases hn : 3 ≤ n
  · rw [show ggU .POmegaPlus n f = ⟨spinGroup (quadPlus n (GaloisField 2 f)),
        plusDatum n (GaloisField 2 f) hn⟩ from dite_eq_left hn]
    intro ψ G₀ hpres p hp hp2 hq1 hq2 x y hx hy hxy _ _ hxD hyD K K' hK hpK hK' hKK' _
    obtain ⟨⟨hadm, -⟩, ⟨hrange, hker⟩, -, -⟩ := hpres
    subst hrange
    have hF : Nat.card (GaloisField 2 f) = 2 ^ f :=
      GaloisField.card 2 f (by have := hadm.2.1; omega)
    obtain ⟨K'', hK'', hKK'', hinn, hM⟩ := OmNonsplit.exists_component_spinPlus hn hker hp hp2
      hF hq1 hq2 hx hy hxy hxD hyD hK hpK
    obtain rfl := OmNonsplit.eq_of_isComponentOf_of_le hK' hK''
      ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native K).mp hK.2.2)
      hKK' hKK''
    exact OmNonsplit.not_ggNbrClauseFiveMarking_of_omModel hF hM hp hp2 hq1 hq2 hinn
  · rw [show ggU .POmegaPlus n f = trivialUniversal from dite_eq_right hn]
    intro ψ G₀ hpres
    exact absurd hpres.1.2 (by decide)

theorem ggNonsplitNbrMarkingTag_POmegaMinus : GGNonsplitNbrMarkingTag .POmegaMinus := by
  intro G _ _ n f ψ G₀ hpres p hp hp2 hq1 hq2 x y hx hy hxy _ _ hxD hyD K K' hK hpK hK' hKK' _
  obtain ⟨⟨hadm, -⟩, ⟨hrange, hker⟩, -, -⟩ := hpres
  obtain ⟨-, hf, hn⟩ := hadm
  subst hrange
  have hF : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  obtain ⟨K'', hK'', hKK'', hinn, hM⟩ := OmNonsplit.exists_component_spinMinus
    (F := GaloisField 2 f) (minusCoeffs_irr 2 f) hn hker hp hp2 hF hq1 hq2 hx hy hxy hxD hyD hK
    hpK
  obtain rfl := OmNonsplit.eq_of_isComponentOf_of_le hK' hK''
    ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native K).mp hK.2.2)
    hKK' hKK''
  exact OmNonsplit.not_ggNbrClauseFiveMarking_of_omModel hF hM hp hp2 hq1 hq2 hinn

theorem ggNonsplitTag_POmegaPlus : GGNonsplitTag .POmegaPlus :=
  ⟨ggNonsplitCompLiftTag_POmegaPlus, ggNonsplitNbrMarkingTag_POmegaPlus⟩

theorem ggNonsplitTag_POmegaMinus : GGNonsplitTag .POmegaMinus :=
  ⟨ggNonsplitCompLiftTag_POmegaMinus, ggNonsplitNbrMarkingTag_POmegaMinus⟩

theorem ggSixLayerCXNonsplitInput_of_tags_exc (hF4 : GGNonsplitTag .F4)
    (hE6 : GGNonsplitTag .E6) (hE7 : GGNonsplitTag .E7) (hE8 : GGNonsplitTag .E8)
    (hTwE6 : GGNonsplitTag .twistedE6) : GGSixLayerCXNonsplitInput :=
  ggSixLayerCXNonsplitInput_of_tags_PSL ggNonsplitTag_PSU_holds ggNonsplitTag_PSp_holds
      ggNonsplitTag_POmegaPlus ggNonsplitTag_POmegaMinus hF4 hE6 hE7 hE8 hTwE6

end Marking

end CFSG.StandardType
