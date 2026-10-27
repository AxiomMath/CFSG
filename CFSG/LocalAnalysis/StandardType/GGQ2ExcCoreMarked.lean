module

public import CFSG.LocalAnalysis.StandardType.GGQ2ExcCoreOccurs
public import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel

import CFSG.LocalAnalysis.StandardType.GGLangCoroot
import CFSG.LocalAnalysis.StandardType.GGQ2ExcCoreNormLe

public section

namespace CFSG.StandardType.GGQ2Frame.ExcPlacement

open CFSG CFSG.Assembly CFSG.StandardType CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.StandardType.QTwoCav

noncomputable section

theorem excCoreMarked
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {m : Fin 6} (hm : 2 ≤ m.val) :
    ExcCoreMarked m τ := by
  intro L _ _ p S hS T₀ d c hadm
  have hchar : CharP L 2 :=
    LangRat.charP_two_of_langSetup_q_eq_two_pow S (f := 1) (hS.1.trans (pow_one 2).symm)
  obtain ⟨U, hU⟩ := hadm.1
  obtain ⟨A, hA, hAU⟩ := d.exists_le_ggLinImage_eq U
  have hc : ExcRaw.occurs m (ggLinImage (p := 3) d.coord A) c := hAU.symm ▸ hU
  have hK := isComponentOf_codeComponent_of_occurs hτ hm hS d hA hadm hc
  obtain ⟨a, ha, hT, hap⟩ := exists_excFamily d hA
  obtain ⟨j, hj⟩ := exists_kernelComponent_of_occurs d hA ha hc
  have hK' : CFSG.Open.IsComponentOf (codeComponent S d.γ c)
      (S.Γ ⊓ Subgroup.centralizer (Set.range fun u => rootDiagUnit τ (a u))) := by
    rw [← isComponentOf_iff_open, centralizer_range_excFamily ha]
    exact hK
  have hKspan : codeComponent S d.γ c ≤ rootSpan τ L {γ | ∃ (k : ℕ) (δ : Fin τ.rank → ℤ),
      δ ∈ componentRoots (TableCRes.famCharHom a) j ∧
        γ = (S.ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ))^[k] δ} := by
    rw [← rationalComponentM_eq_codeComponent hS.2.2 d.γ j hj]
    exact (Subgroup.commutator_le_self _).trans inf_le_left
  obtain ⟨n, hn, hlab⟩ := TableCRes.langFamilyCompLabel_exc hτ S (p := 3) (by norm_num)
    (by norm_num) a hT hap hK' j hKspan
  have hΨ : IsRootComponent (codeRoots d.γ c) := by
    rw [← hj]
    exact isRootComponent_componentRoots j
  have hn1 : n = 1 := by
    have h2 : 2 ^ n = 2 ^ 1 := by
      rw [hn, componentOrbitLength_componentRoots_eq_one_of_neg hS.2.2 j, hS.1]
    exact Nat.pow_right_injective (le_refl 2) h2
  have hhas : GGHasLabel (ExcRaw.label m c)
      (↥(codeComponent S d.γ c) ⧸ Subgroup.center ↥(codeComponent S d.γ c)) := by
    have h := hlab.2.2.1
    rw [hn1, hj, componentLabel_codeRoots_eq_labelSL hτ d hS.2.2 hΨ hc.1] at h
    rwa [excRaw_label_eq_labelSL hm c]
  exact largeEvenMarking_of_hasLabel hK.2.2 hadm.2 hhas

end

end CFSG.StandardType.GGQ2Frame.ExcPlacement

end
