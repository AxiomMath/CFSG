module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsOmegaK
import CFSG.HardMathSupport.Solomon.Coordinator.Th1J1.Zero
import CFSG.Quasithin.EmptyFaithful.SBd17Quot
import CFSG.RankThree.PartTwo.Sec20.SimsYKO3Bridge
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Interface2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise

private theorem odd_normal_eq_bot_of_centralizer_pCore_le {X : Type} [Group X] [Finite X]
    (hchar : Subgroup.centralizer (CFSG.pCore 2 X : Set X) ≤ CFSG.pCore 2 X)
    {N : Subgroup X} (hNn : (⊤ : Subgroup X) ≤ Subgroup.normalizer (N : Set X))
    (hodd : ¬ 2 ∣ Nat.card N) : N = ⊥ := by
  have hNn' : N.Normal :=
    (Subgroup.normalizer_eq_top_iff).mp (le_antisymm le_top hNn)
  have hodd' : Odd (Nat.card N) := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hodd)
  have hle := CFSG.ComponentClassification.OddCore.maximal X N hNn' hodd'
  rw [CFSG.Quasithin.SBd17.oddCore_eq_bot_of_centralizer_pCore_le hchar] at hle
  exact le_antisymm hle bot_le

theorem kThomp_holds : KThomp := by
  unfold KThomp
  intro X _ _ hsolv h3 hchar P
  by_cases hZ : zOneOf (P : Subgroup X) = ⊥
  · rw [hZ, Subgroup.normalizer_eq_top (H := (⊥ : Subgroup X)), Subgroup.coe_top,
      Set.mul_univ_of_one_mem (Subgroup.one_mem _)]
  · have hfour : CFSG.RankThree.PartTwo.Sec18.fourChar (P : Subgroup X) 2 =
        zOneOf (P : Subgroup X) := rfl
    have hne : CFSG.RankThree.PartTwo.Sec18.fourChar (P : Subgroup X) 2 ≠ ⊥ :=
      fun h => hZ (hfour.symm.trans h)
    have hJ : F12.jOf (P : Subgroup X) =
        CFSG.HardMathSupport.Solomon.UniquenessMaximal.jOf (P : Subgroup X) := by
      rw [← CFSG.RankThree.PartTwo.Sec20.SimsYKO3.fourChar_one_eq]
      change (CFSG.elemThompson (P : Subgroup X) 2).map (P : Subgroup X).subtype =
        (CFSG.higherElemThompson (P : Subgroup X) 0).map (P : Subgroup X).subtype
      rw [CFSG.higherElemThompson_zero]
    have hZ1 : zOneOf (P : Subgroup X) =
        CFSG.HardMathSupport.Solomon.UniquenessMaximal.omegaOneZ
          (CFSG.HardMathSupport.Solomon.UniquenessMaximal.jOneOf (P : Subgroup X)) := by
      rw [← hfour]
      exact CFSG.RankThree.PartTwo.Sec20.SimsYKO3.fourChar_two_eq _ P.isPGroup' hne
    have hsolvTop : Group.IsSolvable (⊤ : Subgroup X) :=
      Group.isSolvable_of_surjective (f := (Subgroup.topEquiv (G := X)).symm.toMonoidHom)
        (Subgroup.topEquiv (G := X)).symm.surjective
    have hfac := CFSG.HardMathSupport.Solomon.Coordinator.I28_8.Th1J1.fac_zero_one0
      (G := X) (R := (⊤ : Subgroup X)) (S := (P : Subgroup X))
      ⟨hsolvTop, by rwa [Subgroup.card_top],
        fun N _ hNn hodd => odd_normal_eq_bot_of_centralizer_pCore_le hchar hNn hodd,
        le_top, P.isPGroup', by
          rw [Subgroup.relIndex_top_right]
          exact P.not_dvd_index⟩
    unfold CFSG.HardMathSupport.Solomon.Coordinator.I28_8.Th1J1.Fac at hfac
    simp only [inf_top_eq, Subgroup.coe_top] at hfac
    rw [hJ, hZ1, hfac]

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
