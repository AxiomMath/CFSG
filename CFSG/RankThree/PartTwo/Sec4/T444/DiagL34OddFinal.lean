module

public import CFSG.RankThree.PartTwo.Sec4.T444.DiagFinalDefs
public import CFSG.RankThree.PartTwo.Sec4.T444.DiagL34OddSection
import CFSG.RankThree.PartTwo.Sec4.Item4Res5ProofL34

public section

namespace CFSG.RankThree.PartTwo.Sec4.L34Odd

open CFSG.Assembly.RankThreeEven (projSL projSU)
open CFSG.GorensteinWalter

theorem not_hasSection_L34_of_le_range_toPGL {K : Type*} [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (X : Subgroup (Matrix.ProjGenLinGroup (Fin 3) K))
    (hX : X ≤ (Matrix.SpecialLinearGroup.toPGL :
      Matrix.SpecialLinearGroup (Fin 3) K →* Matrix.ProjGenLinGroup (Fin 3) K).range) :
    ¬ HasSection X (projSL 3 (GaloisField 2 2)) := by
  intro hsec
  have h := KFacts.L34.hasSection_congr_right hsec
    (KFacts.L34.projSLEquivProjectiveSL 3 (GaloisField 2 2))
  refine not_hasSection_of_le_range_toPGL hK X hX
    (Census.Res5L34.eOne (GaloisField 2 2)) ?_ ?_ h
  · intro x hx
    exact Census.Res5L34.sq_eq_one_of_mem_eOne hx
  · rw [Census.Res5L34.card_eOne, KFacts.L34.card_galoisField_two_two]
    norm_num

theorem projSU_le_range_toPGL (p e : ℕ) [Fact p.Prime] :
    projSU 3 p e ≤ (Matrix.SpecialLinearGroup.toPGL :
      Matrix.SpecialLinearGroup (Fin 3) (GaloisField p (2 * e)) →*
        Matrix.ProjGenLinGroup (Fin 3) (GaloisField p (2 * e))).range := by
  rintro _ ⟨g, hg, rfl⟩
  have hdet : g ∈ (Matrix.GeneralLinearGroup.det :
      GL (Fin 3) (GaloisField p (2 * e)) →* (GaloisField p (2 * e))ˣ).ker := by
    refine (Subgroup.closure_le _).2 ?_ hg
    intro A hA
    exact hA.1
  rw [← Matrix.SpecialLinearGroup.range_toGL_eq_ker_det] at hdet
  obtain ⟨s, rfl⟩ := hdet
  exact ⟨s, rfl⟩

end CFSG.RankThree.PartTwo.Sec4.L34Odd

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG.Assembly.RankThreeEven (projSL projSU)
open CFSG.GorensteinWalter
open CFSG.RankThree.PartTwo.Sec4.L34Odd

theorem l34SectionPSL3Odd_holds : L34SectionPSL3Odd := by
  intro p e _ hp he
  have hodd : IsOddPrimePower (Nat.card (GaloisField p e)) :=
    ⟨p, e, Fact.out, (Fact.out : p.Prime).odd_of_ne_two hp, he,
      GaloisField.card p e (by omega)⟩
  exact not_hasSection_L34_of_le_range_toPGL hodd _
    (KFacts.L34.projSL_eq_range_toPGL 3 (GaloisField p e)).le

theorem l34SectionPSU3Odd_holds : L34SectionPSU3Odd := by
  intro p e _ hp he
  have hodd : IsOddPrimePower (Nat.card (GaloisField p (2 * e))) :=
    ⟨p, 2 * e, Fact.out, (Fact.out : p.Prime).odd_of_ne_two hp, by omega,
      GaloisField.card p (2 * e) (by omega)⟩
  exact not_hasSection_L34_of_le_range_toPGL hodd _ (projSU_le_range_toPGL p e)

end CFSG.RankThree.PartTwo.Sec4

end
