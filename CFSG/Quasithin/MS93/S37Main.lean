module

public import CFSG.Quasithin.MS93.S37SQ
public import CFSG.Quasithin.MS93.S37QLine

public section

namespace CFSG.Quasithin.MS93.S37

open CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.Quasithin.MS93 CFSG.Quasithin.MS93.MSP
open CFSG.QuasithinUnique
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible

theorem s37_of_qLine (hQL : QLineCase) (h36 : S36) : S37 := by
  intro G _ _ M T L h hb k F _ _ α hk hF hα hn hodd
  have hn' : IsSumOfNaturalModulesVia L (Uq M T L) (Uq M T L ⊓ Subgroup.centralizer (L : Set G))
      α false 1 := by
    rw [← h.Uq_inf_Zq]
    exact hn
  let C : Cfg M T L F := ⟨h, vq_eq_uq h h36 hb hk hF hα hn, k, hk, hF, α, hα, hn'⟩
  obtain ⟨C', hC'⟩ := C.exists_std hodd
  have hk' : C'.k = k := Nat.pow_right_injective le_rfl (C'.hF.symm.trans hF)
  have hb' : critDist (puAmalgam C'.h.le) = 2 := hb
  rcases hC' with hS | hQ₁ | hQ₂ | hbot
  · by_contra hk2
    exact C'.false_of_SQ₂ (Or.inl hS) hb' (by omega)
  · rw [← hk']
    exact hQL G M T L F C' hb' hodd hQ₁
  · by_contra hk2
    exact C'.false_of_SQ₂ (Or.inr hQ₂) hb' (by omega)
  · exact (C'.false_of_T0bar_bot hbot hb').elim

end CFSG.Quasithin.MS93.S37
