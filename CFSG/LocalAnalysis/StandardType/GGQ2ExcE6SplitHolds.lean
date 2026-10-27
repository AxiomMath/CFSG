module

public import CFSG.LocalAnalysis.StandardType.GGQ2ExcE6SplitDefs
import CFSG.LocalAnalysis.StandardType.GGQ2ExcE6SplitChecks
import CFSG.LocalAnalysis.StandardType.GGQ2ExcRawFixWeylOne
import CFSG.LocalAnalysis.StandardType.GGQ2ExcE6SplitAmbient
import CFSG.LocalAnalysis.StandardType.GGQ2ExcE6SplitCent
import CFSG.LocalAnalysis.StandardType.GGQ2ExcE6SplitShortWeyl
import CFSG.LocalAnalysis.StandardType.GGQ2ExcE6SplitLongWeyl
import CFSG.LocalAnalysis.StandardType.GGQ2ExcE6SplitInsideGe
import CFSG.LocalAnalysis.StandardType.GGQ2ExcE6SplitInsideLe
import CFSG.LocalAnalysis.StandardType.GGQ2ExcE6SplitOccurs
import CFSG.LocalAnalysis.StandardType.GGQ2ExcE6SplitMarked
import CFSG.LocalAnalysis.StandardType.GGQ2ExcE6SplitDatum

public section

namespace CFSG.StandardType.GGQ2Frame.ExcPlacement

open CFSG CFSG.Assembly CFSG.StandardType CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.StandardType.QTwoCav

noncomputable section


theorem e6SplitCoreNormalizer_holds : E6SplitCoreNormalizer := by
  intro L _ _ p S hS T₀ d c hc
  have hN : ExcRaw.normalizerGroup 1 c = ExcRaw.weyl 1 c := if_neg (by simp)
  rw [hN]
  refine le_antisymm ?_ ?_
  · rintro _ ⟨φ, hφ, rfl⟩
    refine ExcRaw.mem_weyl_one_of_fix_cent hc
      (E6SplitDatum.map_ggAutomizer_le_ambientNormalizer d hS
        ⟨φ, ggAutomizer_mono T₀ (e6SplitComponent_le_Γ S c) hφ, rfl⟩) fun v hv => ?_
    rw [← e6SplitCoreCent_holds S hS d c hc, mem_ggLinImage] at hv
    obtain ⟨g, hgR, -, hφg⟩ := mem_ggAutomizer_iff.1 hφ
    have hfix : φ (Additive.toMul (d.coord.symm v)) = Additive.toMul (d.coord.symm v) := by
      apply Subtype.ext
      rw [hφg, Subgroup.mem_centralizer_iff.1 hv g hgR, mul_inv_cancel_right]
    rw [ggLin_apply, hfix, ofMul_toMul, AddEquiv.apply_symm_apply]
  · rw [ExcRaw.weyl, Subgroup.closure_le]
    rintro _ ⟨i, hi, rfl⟩
    have hmem : e6SplitWeyl L i ∈ e6SplitComponent S c := by
      cases h : ExcRaw.tabFix1.getD i.val false
      · exact e6SplitWeyl_mem_e6SplitComponent hS hi h
      · obtain ⟨j, hj, hjs, hij⟩ := e6Split_exists_short_adj_of_admissible hc hi h
        exact e6SplitWeyl_long_mem_e6SplitComponent hS
          (fun γ hγ δ hδ hγδ => E6SplitDatum.add_mem_e6SplitCodeRoots hS d hc.1 hγ hδ hγδ)
          hi hj h hjs hij
    have hnN := E6SplitDatum.e6SplitWeyl_mem_normalizer d hS i
    exact ⟨ggConjAut T₀ hnN, ggConjAut_mem_ggAutomizer hmem hnN,
      E6SplitDatum.ggLin_ggConjAut_e6SplitWeyl d hS i⟩

theorem e6SplitCoreInside_holds : E6SplitCoreInside := by
  intro L _ _ p S hS T₀ d c hc
  have hle : ∀ v, v ∈ ggLinImage (p := 3) d.coord (e6SplitComponent S c) →
      v ∈ ggLinImage (p := 3) d.coord (rootSpan .E6 L (e6SplitCodeRoots c)) := fun v hv =>
    (mem_ggLinImage _ _ v).2 ((Subgroup.commutator_le_self _).trans inf_le_left
      ((mem_ggLinImage _ _ v).1 hv))
  refine le_antisymm (fun v hv => ?_) (E6SplitDatum.inside_le_ggLinImage hS d c)
  rcases e6Split_inside_check hc with ⟨htype, hsup⟩ | hall
  · obtain ⟨U, hU⟩ := hc.1
    have hv' : v ∈ ExcRaw.inside 1 c ⊔ ExcRaw.cent 1 c := hsup ▸ Submodule.mem_top
    obtain ⟨a, ha, w, hw, rfl⟩ := Submodule.mem_sup.1 hv'
    have hwR : w ∈ ggLinImage (p := 3) d.coord (e6SplitComponent S c) := by
      simpa using Submodule.sub_mem _ hv (E6SplitDatum.inside_le_ggLinImage hS d c ha)
    rw [E6SplitDatum.eq_zero_of_mem_ggLinImage_of_mem_cent hS d hU htype (hle w hwR) hw, add_zero]
    exact ha
  · exact hall v fun k hk => E6SplitDatum.root_eq_zero_of_mem_ggLinImage_rootSpan d hk (hle v hv)


theorem e6SplitLangModelFrame_holds : E6SplitLangModelFrame :=
  e6SplitLangModelFrame_of_core e6SplitCoreDatum_holds e6SplitCoreOccurs_holds
    e6SplitCoreMarked_holds e6SplitCoreCent_holds e6SplitCoreInside_holds
    e6SplitCoreNormalizer_holds e6SplitCoreAmbient_holds

end

end CFSG.StandardType.GGQ2Frame.ExcPlacement
