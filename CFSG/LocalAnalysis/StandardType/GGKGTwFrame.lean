module

public import CFSG.LocalAnalysis.StandardType.GGTwKGLayerDefs
public import CFSG.LocalAnalysis.StandardType.GGKGTwFrameCore

public section

namespace CFSG.StandardType.KGL

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType.TableBExc.E6Three
  CFSG.Open

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent


theorem ggTwKGFrame_holds : GGTwKGFrame := by
  intro n hn h3 K _ _ hK σ hσ ε hε Fr hFr ζ hζ hζo L' _ _ ψ A hTB h5
  obtain ⟨hψ, hker, hperf, hA, hAI, -, -, hsc⟩ := hTB
  let ψ₀ : L' →* ↥(twistedE6RootGroup K σ) := ε.symm.toMonoidHom.comp ψ
  have hψ₀ : Function.Surjective ψ₀ := ε.symm.surjective.comp hψ
  have hker₀ : ψ₀.ker ≤ Subgroup.center L' := by
    rw [show ψ₀.ker = ψ.ker from
      MonoidHom.ker_comp_of_injective ψ ε.symm.toMonoidHom ε.symm.injective]
    exact hker
  have hAH : ∀ a ∈ A, ∃ φ ∈ (RecipeExcLang.twConj K σ).range, ∀ l, φ (ψ₀ l) = ψ₀ (a l) := by
    intro a ha
    obtain ⟨φ', hφ'I, hφ'⟩ := hAI a ha
    have hcongr : MulAut.congr ε (MulAut.congr ε.symm φ') = φ' := by
      ext x
      simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_symm,
        MulEquiv.apply_symm_apply]
    have hmem : MulAut.congr ε (MulAut.congr ε.symm φ') ∈ TwE6Delta.RecipeI K n := by
      rwa [hcongr]
    refine ⟨MulAut.congr ε.symm φ', (hε (MulAut.congr ε.symm φ')).mp hmem, fun l => ?_⟩
    change MulAut.congr ε.symm φ' (ε.symm (ψ l)) = ε.symm (ψ (a l))
    simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_symm,
      MulEquiv.apply_symm_apply, hφ']
  obtain ⟨v, g, κ, t, hF⟩ :=
    kgTwFrame_core hn hK σ hσ h3 hFr hζ hζo hψ₀ hker₀ hperf hA hAH h5 hsc
  exact ⟨v, g, κ, t, ⟨hF.hFr, hF.hv, hF.hg, hF.hgF, hF.aut, hF.ht, hF.conj⟩⟩

end CFSG.StandardType.KGL

end
