module

public import CFSG.Blueprint.LieModelAPI
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotSetup
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotTorus
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotCatTypeDet
public import CFSG.LocalAnalysis.StandardType.Marking
public import CFSG.LocalAnalysis.StandardType.MarkingDict
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitF4Label
public import CFSG.LocalAnalysis.StandardType.GGExclNoIso
public import CFSG.LocalAnalysis.StandardType.GGLayerCycModelLabels

public section

namespace CFSG.StandardType.A6Red

open CFSG.Assembly CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.SeitzReduction.SymplecticPilot
open CFSG.StandardType.F4Nonsplit
open LinearMap (BilinForm)

theorem ggA6_p_eq_three
    {L : Type} [Group L] (m : ℕ) (hLie : LieModel L .PSp m 2 1) (p : ℕ) (hp : p.Prime)
    (hmk : LargeEvenMarking L (fun lab _ _ _ _ _ => LargeEvenSplit p lab)) : p = 3 := by
  obtain ⟨K, hKfield, hKfinite, hKchar, _hKcard, ⟨e⟩⟩ := exists_mulEquiv_statedSp_of_lieModel hLie
  have hZ : Subgroup.center L = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    have hx' : e x ∈ Subgroup.center (StatedSp m K) := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨z, rfl⟩ := e.surjective y
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hx z]
    rw [center_statedSp_eq_bot, Subgroup.mem_bot] at hx'
    exact e.injective (by simpa using hx')
  have hQ : LieModel (L ⧸ Subgroup.center L) .PSp m 2 1 :=
    LieModel.quotient_center hZ hLie
  obtain ⟨lab, hlab, R, _, I, F, θ, -, -, hsplit, hM⟩ :=
    largeEvenMarking_exists_markedModel hmk
  have hMq : MarkedModel lab (L ⧸ Subgroup.center L) :=
    MarkedModel.of_mulEquiv θ.symm hM
  have hn1 : lab.n = 1 := by
    by_cases hc : markChar lab = 2
    ·
      have hM' : LieModel (L ⧸ Subgroup.center L) (markTag lab) (markRank lab) 2
          (markDeg lab) := by
        have h := hMq
        unfold MarkedModel at h
        rwa [hc] at h
      have hdeg : markDeg lab = 1 := (lieModel_PSp_two_unique hQ hM').2.2
      rcases markDeg_eq_or hc with h | h
      · rwa [h] at hdeg
      · rw [h] at hdeg; omega
    ·
      have htag : lab.tag = .B2der ∨ lab.tag = .G2der := by
        by_contra h
        simp only [not_or] at h
        exact hc (markChar_eq_two_of_ne h.1 h.2)
      rcases htag with ht | ht
      · have hh := hlab
        simp only [LargeEvenInLambda2, ht] at hh
        exact hh.2.2
      · have hh := hlab
        simp only [LargeEvenInLambda2, ht] at hh
        exact hh.2.2
  exact eq_three_of_largeEvenSplit hp hn1 hsplit

end CFSG.StandardType.A6Red
