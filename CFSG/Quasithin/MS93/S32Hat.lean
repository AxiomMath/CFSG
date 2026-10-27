module

public import CFSG.Quasithin.MS93.S32Main
public import CFSG.Quasithin.MS93.S32Types

public section

namespace CFSG.Quasithin.MS93.S32

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible

theorem card_of_isHat {P : Type} [Group P] (h : IsHat P ↥(alternatingGroup (Fin 6))) :
    Nat.card P = 1080 := by
  obtain ⟨-, h3, ⟨e⟩⟩ := h
  have hA : Nat.card (P ⧸ Subgroup.center P) = 360 := by
    rw [Nat.card_congr e.toEquiv, H13.card_alternatingGroup_fin 6 (by norm_num)]
    decide
  rw [← Subgroup.card_mul_index (Subgroup.center P), h3, Subgroup.index, hA]

theorem s32PartHat_of (h51 : AsB51) (hSQ : SQTKQuot) (hT : TypeFacts) : S32PartHat := by
  intro G _ _ M T L h hhat hC hXL
  obtain ⟨-, ⟨-, hP2⟩, -, -, -, -⟩ := b51_Xq h h51 hSQ
  by_cases hdir : IsIntDirect (commV (autI h.isElemAbelian_Xq L))
      (fixV (autI h.isElemAbelian_Xq L)) ⊤
  · obtain ⟨hsup, -⟩ := (isIntDirect_Xq_iff h).mp hdir
    rw [hXL] at hsup
    rw [← hsup, sup_comm]
  · exfalso
    obtain ⟨-, hlist⟩ := hP2 hdir
    have hU := card_lstar_of_hat (isSecW_Uq h) h hhat
    have hX := isSecW_Xq h
    rcases hlist with ⟨m, F, iF, fF, hF, π, hπ⟩ | ⟨m, F, iF, fF, hF, π, hπ⟩ |
      ⟨m, F, iF, fF, hF, π, hπ⟩ | ⟨π, hπ⟩ | ⟨π, hπ⟩ | ⟨F, iF, fF, hF, π, hπ⟩ |
      ⟨F, iF, fF, hF, π, hπ⟩
    · exact false_of_sl2 hX h hT hF hπ
    · obtain ⟨hm, hc⟩ := card_lstar_of_sp4 hX h hF hπ
      exact (ordBC_two_ne (by omega)).2.1 (hc.symm.trans hU)
    · obtain ⟨hm, hc⟩ := card_lstar_of_g2 hX h hT hF hπ
      exact (ordG2_ne (by omega)).2.1 (hc.symm.trans hU)
    ·
      have hXc : Nat.card (autI h.isElemAbelian_Xq L) = 360 := by
        rw [← Nat.card_congr (FFC.equivOfRealizes (FFC.altDn_faithful (by norm_num)) hπ).toEquiv]
        exact (H13.card_alternatingGroup_fin 6 (by norm_num)).trans (by decide)
      obtain ⟨Kf, iK, fK, Γ₀, -, -, hH, -, π₀, hπ₀⟩ := hhat
      have hUc : Nat.card (autI h.isElemAbelian_Uq L) = 1080 := by
        rw [← Nat.card_congr (FFC.equivOfRealizes (FFModel.nat_faithful _) hπ₀).toEquiv]
        exact card_of_isHat hH
      have hle := card_autI_le h.isElemAbelian_Uq h.isElemAbelian_Xq h.Uq_le_Xq
        ((isSecW_Uq h).L_le_normalizer h) (hX.L_le_normalizer h)
      omega
    · exact false_of_alt8 hX h hT hπ
    · have hc := card_lstar_of_g2d hX h hT hF hπ
      omega
    · obtain ⟨-, hc⟩ := card_lstar_of_sl3 hX h hF hπ
      exact ordA_two_ne_360 le_rfl (hc.symm.trans hU)

end CFSG.Quasithin.MS93.S32
