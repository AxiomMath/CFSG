module

public import CFSG.LocalAnalysis.UniquenessCase.UC6G.AutEbar
public import CFSG.LocalAnalysis.UniquenessCase.UC6L34Aut

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6G

open Subgroup CFSG.RankThree.PartTwo.KFacts.L34
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ABGLocalTools
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase.UC6
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)

namespace Mz614

variable {G : Type} [Group G] [Finite G] {Dat : Data G} (m : Mz614 Dat)

theorem kc633_of_l34 (h620 : m.C620) (hr3 : m.r = 3) (hL : LieModel m.Lbar .PSL 3 2 2) :
    m.KC633 := by
  obtain ⟨K, _, _, hK, ⟨φ⟩⟩ := CFSG.RankThree.PartOne.AUTSL.exists_projectiveSL_equiv_of_lieModel hL
  have hK4 : Nat.card K = 4 := by rw [hK]; norm_num
  have := LinearFieldFour.finite_of_card_eq_four hK4
  haveI : Finite (projectiveSL 3 K) := by
    refine Nat.finite_of_card_ne_zero ?_
    rw [card_projectiveSL hK4]; norm_num
  refine m.kc633_of_model h620 φ (by rw [hr3]; exact factorization_card hK4)
    (E₀ := eZero K) (by rw [hr3]; exact L34K.isSylowOf_eZero hK4) ?_
  rw [hr3]
  exact L34K.absKC_eZero hK4

theorem kn633_of_l34 (h620 : m.C620) (hr3 : m.r = 3) (hL : LieModel m.Lbar .PSL 3 2 2) :
    m.KN633 := by
  obtain ⟨K, _, _, hK, ⟨φ⟩⟩ := CFSG.RankThree.PartOne.AUTSL.exists_projectiveSL_equiv_of_lieModel hL
  have hK4 : Nat.card K = 4 := by rw [hK]; norm_num
  have := LinearFieldFour.finite_of_card_eq_four hK4
  haveI : Finite (projectiveSL 3 K) := by
    refine Nat.finite_of_card_ne_zero ?_
    rw [card_projectiveSL hK4]; norm_num
  refine m.kn633_of_model h620 φ (by rw [hr3]; exact factorization_card hK4)
    (E₀ := eZero K) (by rw [hr3]; exact L34K.isSylowOf_eZero hK4) ?_
  have key : AbsKN (projectiveSL 3 K) 3 (eZero K) (m.r = 3 ∧ LieModel m.Lbar .PSL 3 2 2) :=
    L34K.absKN_of_card hK4 (card_eZero hK4) ⟨hr3, hL⟩
  have hsw : ∀ n : ℕ, n = 3 →
      AbsKN (projectiveSL 3 K) 3 (eZero K) (m.r = 3 ∧ LieModel m.Lbar .PSL 3 2 2) →
      AbsKN (projectiveSL 3 K) n (eZero K) (m.r = 3 ∧ LieModel m.Lbar .PSL 3 2 2) :=
    fun n hn h => by subst hn; exact h
  exact hsw _ hr3 key

theorem kinv633_of_l34 (h620 : m.C620) (hr3 : m.r = 3) (hL : LieModel m.Lbar .PSL 3 2 2) :
    m.KInv633 := by
  obtain ⟨K, _, _, hK, ⟨φ⟩⟩ := CFSG.RankThree.PartOne.AUTSL.exists_projectiveSL_equiv_of_lieModel hL
  have hK4 : Nat.card K = 4 := by rw [hK]; norm_num
  have := LinearFieldFour.finite_of_card_eq_four hK4
  haveI : Finite (projectiveSL 3 K) := by
    refine Nat.finite_of_card_ne_zero ?_
    rw [card_projectiveSL hK4]; norm_num
  exact m.kinv633_of_model h620 φ (by rw [hr3]; exact factorization_card hK4)
    (E₀ := eZero K) (by rw [hr3]; exact L34K.isSylowOf_eZero hK4) (L34K.absKInv_eZero hK4)

end Mz614

end CFSG.LocalAnalysis.UniquenessCase.UC6G
