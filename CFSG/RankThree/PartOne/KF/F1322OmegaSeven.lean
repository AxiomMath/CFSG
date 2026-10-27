module

public import CFSG.RankThree.PartOne.KF.BloomOmega
public import CFSG.LocalAnalysis.ComponentInitial.SmallLinearIsomorphisms

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.RankThree.PartOne.KF1322

open Matrix CFSG.RankThree.SubgroupLists CFSG.RankThree.PartOne.LIT CFSG.RankThree.PartOne.KFBloom
open scoped MatrixGroups

theorem ker_adGL_eq_center {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    (adGL (K := ZMod p)).ker = Subgroup.center SL(2, ZMod p) := by
  ext g
  have hmem : g ∈ (adGL (K := ZMod p)).ker ↔ g = 1 ∨ g = negOne := by
    have := Set.ext_iff.mp (ker_adGL_eq hp2) g
    simpa using this
  have hneg : (Matrix.diagonal fun _ : Fin 2 => (-1 : ZMod p)) = -1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [hmem, Matrix.SpecialLinearGroup.mem_center_iff]
  constructor
  · rintro (rfl | rfl)
    · exact ⟨1, by simp, by simp⟩
    · refine ⟨-1, by simp, ?_⟩
      simpa [negOne] using hneg
  · rintro ⟨r, hr, hg⟩
    have hr2 : r * r = 1 := by simpa [sq] using hr
    rcases mul_self_eq_one_iff.mp hr2 with rfl | rfl
    · left
      apply Subtype.ext
      simpa using hg.symm
    · right
      apply Subtype.ext
      have := hg.symm
      simp only [map_neg, map_one, negOne] at this ⊢
      exact this

theorem nonempty_omegaGL_equiv_psl2 {p : ℕ} [Fact p.Prime] (hp : 5 ≤ p)
    {M : Matrix (Fin 3) (Fin 3) (ZMod p)} (hMt : Mᵀ = M) (hdet : M.det ≠ 0) :
    Nonempty (omegaGL M ≃* ProjectiveSpecialLinearGroup (Fin 2) (ZMod p)) := by
  have hp2 : p ≠ 2 := by omega
  obtain ⟨g, c, hc, hg⟩ := exists_congr_splitForm hp2 M hMt hdet
  have hΩ : (omegaGL M).comap (MulAut.conj g : GL (Fin 3) (ZMod p) →* GL (Fin 3) (ZMod p)) =
      omegaGL (splitForm p) := by
    rw [← omegaGL_congr, hg, omegaGL_smul _ hc]
  have hmap : (omegaGL (splitForm p)).map
      (MulAut.conj g : GL (Fin 3) (ZMod p) →* GL (Fin 3) (ZMod p)) = omegaGL M := by
    rw [← hΩ, Subgroup.map_comap_eq_self_of_surjective (MulAut.conj g).surjective]
  have e1 : omegaGL (splitForm p) ≃* omegaGL M :=
    ((omegaGL (splitForm p)).equivMapOfInjective _ (MulAut.conj g).injective).trans
      (MulEquiv.subgroupCongr hmap)
  have e2 : omegaGL (splitForm p) ≃* (adGL (K := ZMod p)).range :=
    MulEquiv.subgroupCongr (omegaGL_splitForm_eq_range hp)
  have e3 : SL(2, ZMod p) ⧸ (adGL (K := ZMod p)).ker ≃* (adGL (K := ZMod p)).range :=
    QuotientGroup.quotientKerEquivRange _
  have e4 : SL(2, ZMod p) ⧸ (adGL (K := ZMod p)).ker ≃*
      ProjectiveSpecialLinearGroup (Fin 2) (ZMod p) :=
    QuotientGroup.quotientMulEquivOfEq (ker_adGL_eq_center hp2)
  exact ⟨e1.symm.trans (e2.trans (e3.symm.trans e4))⟩

theorem nonempty_omegaGL_equiv_GL_three_two [Fact (Nat.Prime 7)]
    {M : Matrix (Fin 3) (Fin 3) (ZMod 7)} (hMt : Mᵀ = M)
    (hdet : M.det ≠ 0) : Nonempty (omegaGL M ≃* GL (Fin 3) (ZMod 2)) := by
  obtain ⟨e⟩ := nonempty_omegaGL_equiv_psl2 (by norm_num : 5 ≤ 7) hMt hdet
  obtain ⟨e7⟩ := CFSG.LocalAnalysis.ComponentInitial.nonempty_GL_three_two_equiv_PSL_two_seven
  exact ⟨e.trans e7.symm⟩

end CFSG.RankThree.PartOne.KF1322
