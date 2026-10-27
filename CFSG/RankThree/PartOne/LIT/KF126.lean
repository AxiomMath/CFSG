module

public import CFSG.RankThree.PartOne.S12.InputsLinear
public import CFSG.RankThree.PartOne.LIT.CongruenceFive
public import CFSG.RankThree.PartOne.LIT.OmegaFive
public import CFSG.RankThree.SubgroupLists2.OmegaThree

public section

namespace CFSG.RankThree.PartOne

open CFSG.RankThree.SubgroupLists

theorem natCard_soGL_one_five : Nat.card (soGL (1 : LIT.M3)) = 120 := by
  have h := card_soGL_three (p := 5) (by norm_num) (M := (1 : LIT.M3)) (by simp) (by simp)
  rw [h]
  norm_num

theorem kf126 : KF126 := by
  intro M hM hdet
  obtain ⟨g, c, hc, hgc⟩ := LIT.exists_congr_scalar_five M hM hdet
  have hΩ : (omegaGL M).comap (MulAut.conj g : GL (Fin 3) (ZMod 5) →* GL (Fin 3) (ZMod 5)) =
      omegaGL (1 : LIT.M3) := by
    rw [← LIT.omegaGL_congr, hgc, LIT.omegaGL_smul 1 hc]
  refine ⟨?_, ?_⟩
  · rw [LIT.natCard_eq_of_comap (MulAut.conj g) _ _ hΩ]
    exact LIT.natCard_omegaGL_one natCard_soGL_one_five
  · exact LIT.perfect_normalizer_le_of_comap (MulAut.conj g) _ _ hΩ LIT.perfect_normalizer_le

end CFSG.RankThree.PartOne
