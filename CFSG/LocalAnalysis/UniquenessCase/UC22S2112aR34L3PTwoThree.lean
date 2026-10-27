module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34L3PTwoSplit
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34L3P149Three
import CFSG.LocalAnalysis.UniquenessCase.UC22L3FrameLin
import CFSG.LocalAnalysis.UniquenessCase.UC22L3FrameUni
import CFSG.LocalAnalysis.UniquenessCase.UC22L3ThreeNoFive
import CFSG.LocalAnalysis.UniquenessCase.UC7R71Three
import CFSG.LocalAnalysis.UniquenessCase.UC22S213L3Cover
import CFSG.LocalAnalysis.UniquenessCase.UC22S213PrimeRank
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.ConjSetCard
import CFSG.Quasithin.Background.A3FactsA134

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.RankThreeUC (Setup Standing AGL81TheoremC)

variable {G : Type} [Group G] [Finite G]

theorem uc22s2112l3p_le_normalizer_three (hGA : GriessAllModelsStatement) (hS : Standing G)
    (S : Setup G) : ∀ L ∈ calC (PartTwo.Three.dataOfSetup hS S).M, ∀ p : ℕ, p.Prime → p ≠ 2 →
      (LieModel (BarInf L) .PSL 3 p 1 ∨ LieModel (BarInf L) .PSU 3 p 1) →
        (PartTwo.Three.dataOfSetup hS S).M ≤ normalizer (L : Set G) := by
  intro L hL p hp hp2 hX g hg
  by_contra hgN
  have hZ : ¬ p ∣ Nat.card (center (Bar2 L)) := by
    rcases hX with h | h
    · exact uc22s213_not_dvd_card_center_of_rank_three_odd hGA hL (.inl rfl) hp2 h
    · exact uc22s213_not_dvd_card_center_of_rank_three_odd hGA hL (.inr rfl) hp2 h
  have hpL : 2 ≤ Open.pRank p L := by
    rw [← uc22s213_pRank_barInf_of_prime hL.2.2 hp hp2 hZ]
    exact CFSG.Quasithin.A3Facts.two_le_pRank_psl_psu_three hp2
      (hX.imp (·.statedClassicalModel_of_ne_zero (by norm_num))
        (·.statedClassicalModel_of_ne_zero (by norm_num)))
  have hne : L ≠ L.map (MulAut.conj g).toMonoidHom := fun he =>
    hgN (Subgroup.mem_normalizer_iff_map_conj_eq.mpr he.symm)
  have h4 := uc22s213_four_le_pRank_of_two_conj hL
    (PartOne.Section8.mem_conjSetOf_self (PartTwo.Three.dataOfSetup hS S).M L) ⟨g, hg, rfl⟩ hne
    hp hp2 hpL hZ
  have h3 : Open.pRank p (PartTwo.Three.dataOfSetup hS S).M ≤ 3 :=
    PartTwo.Three.pRank_le_three_dataOfSetup hS S hp hp2 le_rfl
  omega

theorem s21_12aFR34L3PTwo_dataOfSetup
    (hS : Standing G) (hUC : CFSG.Open.rankThreeUC G) (hC : AGL81TheoremC G) (S : Setup G)
    (_hMS : S.InMSigma) :
    S21_12aFR34L3PTwo (PartTwo.Three.dataOfSetup hS S)
      (Choice214U (PartTwo.Three.dataOfSetup hS S)) :=
  s21_12aFR34L3PTwo_of_invertSplit (l3InvertSplit_of_frames l3FrameExists_psl l3FrameExists_psu
      l3ThreeNoFive_holds) (r149L3P_dataOfSetup hS hUC hC S)
    (uc22s2112l3p_le_normalizer_three
      CFSG.HardMathSupport.Foote.FamilyReduction.griessAllModelsStatement hS S)

end CFSG.LocalAnalysis.UniquenessCase.UC22
