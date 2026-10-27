module

public import CFSG.Sporadic.Co1Patterson.NativeSetting
public import CFSG.Sporadic.Co1Patterson.TwistNativeBasis

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Sporadic.Co1Patterson.TwistNative

open Subgroup CFSG.Sporadic.Co1Block CFSG.Sporadic.Co1Schreier CFSG.LargeExtraspecial
open CFSG.Blueprint (NativeSporadic.Co1)


theorem nwcOK_parts : Native.mul (twRow gIdx) (Native.inv (twRow gIdx)) = Native.one ∧
    Native.mul (Native.mul (twRow gIdx) iotaARows) (Native.inv (twRow gIdx)) = yRow 0 ∧
    yRow 0 ≠ iotaARows := by
  have h := tw_nwc_check
  simp only [nwcOK, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem nwc_conj : twG gIdx * aG * (twG gIdx)⁻¹ = yG 0 := by
  have hg := rep_twG gIdx
  have hx := (hg.mul rep_iotaA).mul (hg.inv nwcOK_parts.1)
  rw [nwcOK_parts.2.1] at hx
  exact hx.eq (rep_yG 0)

theorem yG_ne_aG : yG 0 ≠ aG := fun h => nwcOK_parts.2.2
  ((rows_eq_iff (rep_yG 0) rep_iotaA (dagOK_parts.2.2.1 0 (by norm_num)) dagOK_parts.2.1).2 h)


theorem notWeaklyClosed_native : NotWeaklyClosed pattersonCo1Hyp_native := by
  obtain ⟨g, hg⟩ := exists_nativeEmb_eq (twG_mem_GA gIdx)
  have he : nativeEmb (g * aNC * g⁻¹) = yG 0 := by
    rw [map_mul, map_mul, map_inv, hg, nativeEmb_aNC, nwc_conj]
  refine ⟨g, ?_, fun h => yG_ne_aG ?_⟩
  · rw [setting_native_QG, mem_twoAQNC_iff, he]
    exact yG_mem_twoAQ 0
  · rw [← he, h, nativeEmb_aNC]

end CFSG.Sporadic.Co1Patterson.TwistNative
