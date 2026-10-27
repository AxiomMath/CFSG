module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.RankThree.PartTwo.Sec13.KF135Proof.FamOdd

open CFSG Subgroup
open scoped MatrixGroups

theorem projSU_le_range_toPGL (n r e : ℕ) [Fact r.Prime] :
    CFSG.Assembly.RankThreeEven.projSU n r e ≤ (Matrix.SpecialLinearGroup.toPGL :
      Matrix.SpecialLinearGroup (Fin n) (GaloisField r (2 * e)) →*
        Matrix.ProjGenLinGroup (Fin n) (GaloisField r (2 * e))).range := by
  rintro _ ⟨g, hg, rfl⟩
  have hdet : g ∈ (Matrix.GeneralLinearGroup.det :
      GL (Fin n) (GaloisField r (2 * e)) →* (GaloisField r (2 * e))ˣ).ker := by
    refine (Subgroup.closure_le _).2 ?_ hg
    intro A hA
    exact hA.1
  rw [← Matrix.SpecialLinearGroup.range_toGL_eq_ker_det] at hdet
  obtain ⟨s, rfl⟩ := hdet
  exact ⟨s, rfl⟩

end CFSG.RankThree.PartTwo.Sec13.KF135Proof.FamOdd
