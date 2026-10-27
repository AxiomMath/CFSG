module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsThreeThreeJ2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.HJ12ThreeThreeSound
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.HJTransport

@[expose] public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

theorem w4Lem3_3J2_holds :
    W4Lem3_3J2 := by
  intro W _ _ hW Y L hLY hN hF hspor hirr hrk
  classical
  obtain ⟨ψ, hψ⟩ := exists_mulEquiv_map_eq_hjL0 hW hrk hspor hirr
  let φ : MulAut W →* MulAut W12 := (MulAut.congr ψ).toMonoidHom
  have hcomp : (MulAut.congr ψ.symm).toMonoidHom.comp φ = MonoidHom.id (MulAut W) := by
    ext f w
    change ψ.symm ((MulAut.congr ψ f) (ψ w)) = f w
    rw [MulAut.congr_apply]
    simp
  have hLmap : L = hjL0.map (MulAut.congr ψ.symm).toMonoidHom := by
    rw [← hψ, Subgroup.map_map, hcomp, Subgroup.map_id]
  refine ⟨?_, ?_⟩
  · refine ⟨MulAut.congr ψ.symm (hjWord HJ12.hj_zWord), ?_, ?_, ?_⟩
    · rw [hLmap]
      exact Subgroup.mem_map_of_mem _ hjZ_mem
    · have hord := orderOf_injective (MulAut.congr ψ.symm).toMonoidHom
        (MulEquiv.injective (MulAut.congr ψ.symm)) (hjWord HJ12.hj_zWord)
      exact hord.trans hjZ_orderOf
    · exact (rk_commSub_congr (e := ψ.symm) (x := hjWord HJ12.hj_zWord)).trans hjZ_rank
  · have hYnorm : Y ≤ Subgroup.normalizer (L : Set (MulAut W)) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hLY).1 hN
    have hYN : Y.map φ ≤ Subgroup.normalizer (hjL0 : Set (MulAut W12)) := by
      calc Y.map φ ≤ (Subgroup.normalizer (L : Set (MulAut W))).map φ :=
            Subgroup.map_mono hYnorm
        _ = Subgroup.normalizer ((L.map φ) : Set (MulAut W12)) :=
            Subgroup.map_equiv_normalizer_eq L (MulAut.congr ψ)
        _ = Subgroup.normalizer (hjL0 : Set (MulAut W12)) := by rw [hψ]
    calc E3.aParam Y = E3.aParam (Y.map φ) :=
          (CFSG.Quasithin.H.aParam_map_congrHom ψ Y).symm
      _ ≤ E3.aParam (Subgroup.normalizer (hjL0 : Set (MulAut W12))) := E3.aParam_mono hYN
      _ ≤ 2 := aParam_normalizer_hjL0_le_two

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

end
