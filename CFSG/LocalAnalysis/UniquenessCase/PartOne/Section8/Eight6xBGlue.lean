module

public import CFSG.LocalAnalysis.UniquenessCase.UC6Inst
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC6 (R6_14 dataOfSetup4)
open CFSG.LocalAnalysis.UniquenessCase.UC6S846 (SigmaStd)
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 Theorem614At SigmaOne4)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

@[expose] def SigmaIsRankFour {G : Type} [Group G] [Finite G] (D : Data G) : Prop :=
  D.sig = uniqueFourSigma D.M ∧ D.sig1 = uniqueFourSigma D.M ∩ SigmaOne4 G

theorem sigmaIsRankFour_dataOfSetup4 {G : Type} [Group G] [Finite G] (hS : Standing4 G)
    (hU : uniqueFourUnique G) (S : Setup4 G) : SigmaIsRankFour (dataOfSetup4 hS hU S) :=
  ⟨rfl, rfl⟩

theorem r6_14_iff_theorem614At {G : Type} [Group G] [Finite G] {D : Data G}
    (h : SigmaIsRankFour D) : R6_14 D ↔ Theorem614At D.M := by
  obtain ⟨h0, h1⟩ := h
  constructor
  · intro hR hsub r hr hr2 hrσ R hRS E hE hEel hEcard hΓ
    refine hR ?_ r hr hr2 ?_ R hRS E hE hEel hEcard hΓ
    · rw [h0, h1]
      exact fun p hp => ⟨hp, hsub hp⟩
    · rwa [h0]
  · intro hT hsub r hr hr2 hrσ R hRS E hE hEel hEcard hΓ
    rw [h0, h1] at hsub
    rw [h0] at hrσ
    exact hT (fun p hp => (hsub hp).2) r hr hr2 hrσ R hRS E hE hEel hEcard hΓ

theorem sub_and_not_mem_of_sigmaStd {G : Type} [Group G] [Finite G] {D : Data G}
    (hSg : SigmaStd D) (h : SigmaIsRankFour D) (hns : ¬ Group.IsSolvable ↥D.M) {r : ℕ}
    (hnot : ¬ IsStronglyPEmbedded r D.M) :
    uniqueFourSigma D.M ⊆ SigmaOne4 G ∧ r ∉ uniqueFourSigma D.M := by
  obtain ⟨h0, h1⟩ := h
  refine ⟨fun p hp => ?_, fun hr => ?_⟩
  · rw [← h0] at hp
    have hp1 := CFSG.LocalAnalysis.UniquenessCase.UC6S846.sig_subset_sig1 hSg hns hp
    rw [h1] at hp1
    exact hp1.2
  · rw [← h0] at hr
    exact hnot (CFSG.LocalAnalysis.UniquenessCase.UC6S846.sp_of_mem_sig hSg hns hr)

theorem family_hyps_of_r6_14 {G : Type} [Group G] [Finite G] {D : Data G}
    (hSg : SigmaStd D) (h : SigmaIsRankFour D) (hns : ¬ Group.IsSolvable ↥D.M)
    (h614 : R6_14 D) {r : ℕ} (hnot : ¬ IsStronglyPEmbedded r D.M) :
    Theorem614At D.M ∧ uniqueFourSigma D.M ⊆ SigmaOne4 G ∧ r ∉ uniqueFourSigma D.M :=
  ⟨(r6_14_iff_theorem614At h).1 h614, sub_and_not_mem_of_sigmaStd hSg h hns hnot⟩

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
