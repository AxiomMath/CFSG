module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront78Nar
public import CFSG.LocalAnalysis.UniquenessCase.UC6Inst

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F08

open CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

@[expose] def R869MRest (D : Data G) : Prop :=
  ∀ L : Subgroup G,
    (L ∈ calC D.M ∨ (L ≤ D.M ∧ D.M ≤ normalizer (L : Set G) ∧ IsProdOfCalC D.M L)) →
    ¬ Thin8 L → (∀ p ∈ D.sig, CFSG.Open.pRank p L ≤ 1) → UniqueMax D.M L

theorem R869MRest_of_R869M (D : Data G) (h : R869M D) : R869MRest D :=
  fun L hL hthin _ => h L hL hthin

end CFSG.LocalAnalysis.UniquenessCase.UC22.F08

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4)

variable {G : Type} [Group G] [Finite G]

theorem uniqueMax_of_two_le_pRank_sigma (hU : uniqueFourUnique G) {M : Subgroup G}
    (hM : uniqueFourIsMaxTwoLocal M) {p : ℕ} (hp : p ∈ uniqueFourSigma M) {L : Subgroup G}
    (hLM : L ≤ M) (h2 : 2 ≤ CFSG.Open.pRank p L) : UniqueMax M L := by
  show calMOf L = {M}
  ext N
  constructor
  · rintro ⟨hN, hLN⟩
    have hle := sec61 hU hM hp hLM h2 hN.1 hLN
    exact (hN.2 _ hM.1 hle).symm
  · intro hN
    have hNM : N = M := hN
    subst hNM
    exact ⟨hM, hLM⟩

theorem r869M_dataOfSetup4_of_rest (hS : Standing4 G) (hU : uniqueFourUnique G) (S : Setup4 G)
    (h : F08.R869MRest (dataOfSetup4 hS hU S)) : F08.R869M (dataOfSetup4 hS hU S) := by
  intro L hL hthin
  have hLM : L ≤ S.M := by
    rcases hL with hL | ⟨hL, -, -⟩
    · exact CFSG.Quasithin.A3.subnormal_le hL.1
    · exact hL
  by_cases hp : ∃ p ∈ uniqueFourSigma S.M, 2 ≤ CFSG.Open.pRank p L
  · obtain ⟨p, hp, h2⟩ := hp
    exact uniqueMax_of_two_le_pRank_sigma hU S.maxLocal hp hLM h2
  · push_neg at hp
    refine h L hL hthin fun p hp' => ?_
    have := hp p hp'
    omega

end CFSG.LocalAnalysis.UniquenessCase.UC6
