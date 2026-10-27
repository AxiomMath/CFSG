module

public import CFSG.LocalAnalysis.StandardType.GGSporKShape
public import CFSG.LocalAnalysis.StandardType.GGSporKRestPairs
public import CFSG.LocalAnalysis.StandardType.GGSporKRestFalseCover
public import CFSG.LocalAnalysis.StandardType.GGSporKRestFalseUnmarked
public import CFSG.LocalAnalysis.StandardType.GGSporKRestTransport

public section

namespace CFSG.StandardType.SporadicShape

open CFSG CFSG.StandardType CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Solomon.Coordinator

theorem ggSporKRest_pair_of_cover (hOut : SporadicOuterLeTwo) (s : TauCeti.SporadicName) (p : ℕ)
    (hCov : SporKRestCover p (TauCeti.CFSGIndex.sporadic s).Group) :
    GGKGroupFusionAtFlatKPair s p := by
  intro W _ _ hW q H E i hi hyp hL hK he
  obtain ⟨rfl, rfl⟩ := hi
  obtain ⟨e⟩ := he
  exact (ggSporKRest_false_of_cover hyp hK (hOut _ hyp.2.1.1 hyp.2.1.2.1 s ⟨e⟩)
    (hCov.of_mulEquiv e.symm)).elim

theorem ggSporKRest_pair_of_coverOrUnmarked (hOut : SporadicOuterLeTwo) (s : TauCeti.SporadicName)
    (p : ℕ) (hCov : SporKRestCoverOrUnmarked p (TauCeti.CFSGIndex.sporadic s).Group) :
    GGKGroupFusionAtFlatKPair s p := by
  intro W _ _ hW q H E i hi hyp hL hK he
  obtain ⟨rfl, rfl⟩ := hi
  obtain ⟨e⟩ := he
  exact (ggSporKRest_false_of_coverOrUnmarked hyp hL hK (hOut _ hyp.2.1.1 hyp.2.1.2.1 s ⟨e⟩)
    (hCov.of_mulEquiv e.symm)).elim

theorem ggSporKRest_pair_Fi22_five (hOut : SporadicOuterLeTwo)
    (hCov : SporKRestFi22Exc (TauCeti.CFSGIndex.sporadic .Fi22).Group) :
    GGKGroupFusionAtFlatKPair .Fi22 5 := by
  intro W _ _ hW q H E i hi hyp hL hK he
  obtain ⟨rfl, rfl⟩ := hi
  obtain ⟨e⟩ := he
  exact ggSporKRest_exception_of_fi22 hyp hK (hOut _ hyp.2.1.1 hyp.2.1.2.1 .Fi22 ⟨e⟩) ⟨e⟩
    (hCov.of_mulEquiv e.symm)

theorem ggKGroupFusionAtFlatK_rest_of_leaves (hOut : SporadicOuterLeTwo) (hP2 : SporadicP2Table)
    (hCov : ∀ s p, SporKRestCoverPair s p → SporKRestCover p (TauCeti.CFSGIndex.sporadic s).Group)
    (hBad : ∀ s p, SporKRestBadPair s p →
      SporKRestCoverOrUnmarked p (TauCeti.CFSGIndex.sporadic s).Group)
    (hFi : SporKRestFi22Exc (TauCeti.CFSGIndex.sporadic .Fi22).Group) :
    GGKGroupFusionAtFlatK GGKFSporadicRest := by
  refine GGKGroupFusionAtFlatK.of_pairs (S := GGKFSporadicRest)
    (fun i p h => ?_) (fun s p hs => ?_)
  · obtain ⟨s, rfl, -, -⟩ := h
    exact ⟨s, rfl⟩
  · obtain ⟨s', hs', hB, hM⟩ := hs
    have hss : s' = s := by simpa using hs'.symm
    subst hss
    intro W _ _ hW q H E i hi hyp hL hK he
    obtain ⟨hi1, rfl⟩ := hi
    by_cases hsq : q ^ 2 ∣ Nat.card (MulAut (TauCeti.CFSGIndex.sporadic s').Group)
    · obtain ⟨e⟩ := he
      haveI : IsSimpleGroup ↥(CFSG.generalizedFitting W) := hyp.2.1.1
      have hS : IsSimpleGroup (TauCeti.CFSGIndex.sporadic s').Group := by
        subst hi1
        exact MulEquiv.isSimpleGroup e.symm
      have hN : ∃ a b : (TauCeti.CFSGIndex.sporadic s').Group, a * b ≠ b * a := by
        subst hi1
        obtain ⟨a, b, hab⟩ := hyp.2.1.2.1
        exact ⟨e a, e b, fun hc => hab (e.injective (by simpa using hc))⟩
      rcases ggSporKRest_pairs_list hOut hP2 s' hB hM hS hN q hyp.1.1 hyp.1.2.1 hsq with h | h | h
      · exact ggSporKRest_pair_of_cover hOut s' q (hCov s' q h) W hW q H E i ⟨hi1, rfl⟩ hyp hL hK
          ⟨e⟩
      · exact ggSporKRest_pair_of_coverOrUnmarked hOut s' q (hBad s' q h) W hW q H E i ⟨hi1, rfl⟩
          hyp hL hK ⟨e⟩
      · obtain ⟨rfl, rfl⟩ := h
        exact ggSporKRest_pair_Fi22_five hOut hFi W hW 5 H E i ⟨hi1, rfl⟩ hyp hL hK ⟨e⟩
    · exact ggSporK_pair_of_not_sq_dvd s' q hsq W hW q H E i ⟨hi1, rfl⟩ hyp hL hK he

end CFSG.StandardType.SporadicShape
