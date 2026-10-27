module

public import CFSG.LocalAnalysis.StandardType.GGResFFDefs
public import CFSG.LocalAnalysis.StandardType.GGCentreTrivialTwKnownHolds

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank
open CFSG.Blueprint.Multiplier (generic exceptional genericOrders exceptionalOrders)
open CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier (torsBound tors tors_of_not_dvd)

private theorem o2ac_torsBound_psl7 {r : ℕ} (hr : r.Prime) : torsBound r .PSL 7 2 1 = 1 := by
  have hg : genericOrders .PSL 7 2 1 = (1, 1) := by
    simp only [genericOrders]
    rfl
  have hex : exceptionalOrders .PSL 7 2 1 = (1, 1) := rfl
  have h1 : tors r 1 = 1 := tors_of_not_dvd hr.not_dvd_one
  unfold torsBound
  rw [hg, hex]
  simp [h1]

theorem ggO2aCentreKnown_holds :
    GGO2aCentreKnown := by
  intro lab hlab
  rcases hlab with rfl | rfl
  · exact (ggCentreTrivialTwKnown_holds 1 le_rfl).2.1 (by norm_num)
  · intro Q hQ
    have hlabΛ : LargeEvenInLambda2 ⟨.A, 6, 1⟩ := by simp [LargeEvenInLambda2]
    have hmarked : LargeEvenLabelAll ⟨.A, 6, 1⟩ fun R _ _ _ =>
        MarkedModel ⟨.A, 6, 1⟩ R :=
      SCFourCover.largeEvenLabelAll_markedModel_classical hlabΛ (Or.inl rfl)
    have hb : ∀ r : ℕ, r.Prime →
        torsBound r (markTag ⟨.A, 6, 1⟩) (markRank ⟨.A, 6, 1⟩)
          (markChar ⟨.A, 6, 1⟩) (markDeg ⟨.A, 6, 1⟩) = 1 := by
      intro r hr
      simp only [markTag, markRank, markChar, markDeg]
      exact o2ac_torsBound_psl7 hr
    refine largeEvenRawDatum_mono ?_ (hmarked Q hQ)
    rintro R _ I F ⟨hq, hM⟩
    obtain ⟨hperfR, hT⟩ :=
      CFSG.Milestones.cl_lit_griess_schur_multipliers_all_native_models _ _ _ _ _ hM
    have hsimple : IsSimpleGroup R := CFSG.Evidence.isSimpleGroup_of_lieModel hM
    exact ⟨hq, fun L' _ _ ψ hs hker hperf =>
      gctt_of_markedModel hb hM hsimple hperfR hT L' ψ hs hker hperf⟩

end CFSG.StandardType
