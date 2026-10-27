module

public import CFSG.LocalAnalysis.StandardType.GGFFLocalFus
public import CFSG.RankThree.PartTwo.Sec21.HeringFFStatement

@[expose] public section

namespace CFSG.StandardType.GGFF

open CFSG.RankThree.PartTwo.Sec21.FF79 (Cen CenS Nor)

variable {G : Type} [Group G] [Finite G]

namespace SettingCore

variable {b : G} {K : Subgroup G} {z : Fin 3 → K}

theorem not_nor_le (h : SettingCore b K z)
    (hWC : CFSG.RankThree.PartTwo.Sec21.FFNotWeaklyClosed b) :
    ¬ Nor (Bt b z) ≤ Nor (Subgroup.zpowers b) := by
  rintro hle
  obtain ⟨g, hgC, hgne⟩ := hWC
  have hβmem : g⁻¹ * b * g ∈ CFSG.conjugate (Subgroup.zpowers b) g := by
    rw [CFSG.conjugate, Subgroup.mem_map]
    refine ⟨b, Subgroup.mem_zpowers b, ?_⟩
    simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply, inv_inv]
  have hβC : g⁻¹ * b * g ∈ Cen b := hgC hβmem
  have hβ3 : (g⁻¹ * b * g) ^ 3 = 1 := by
    rw [show g⁻¹ * b * g = g⁻¹ * b * (g⁻¹)⁻¹ by rw [inv_inv], conj_pow, h.b_cube]
    group
  obtain ⟨l, hlK, β', hβ'B, hβeq⟩ := h.exists_conj_mem_Bt hβC hβ3
  have hm : (l⁻¹ * g⁻¹) * b * (l⁻¹ * g⁻¹)⁻¹ = β' := by
    have e : (l⁻¹ * g⁻¹) * b * (l⁻¹ * g⁻¹)⁻¹ = l⁻¹ * (g⁻¹ * b * g) * l := by group
    rw [e, hβeq]
    group
  obtain ⟨n, hnB, hnb⟩ := h.fusion hβ'B hm
  have hnN : n ∈ Nor (Subgroup.zpowers b) := hle hnB
  have hβ'mem : β' ∈ Subgroup.zpowers b := by
    have hm' := (Subgroup.mem_normalizer_iff.mp hnN b).mp (Subgroup.mem_zpowers b)
    rwa [hnb] at hm'
  have hlβ' : l * β' * l⁻¹ = β' := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hβ'mem
    rw [← hk, (Commute.zpow_right (h.comm_of_mem hlK) k).eq, mul_assoc, mul_inv_cancel,
      mul_one]
  have hβzp : g⁻¹ * b * g ∈ Subgroup.zpowers b := by
    rw [hβeq, hlβ']
    exact hβ'mem
  have hle_conj : CFSG.conjugate (Subgroup.zpowers b) g ≤ Subgroup.zpowers b := by
    intro x hx
    rw [CFSG.conjugate, Subgroup.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [map_zpow]
    have e : ((MulAut.conj g⁻¹).toMonoidHom) b = g⁻¹ * b * g := by
      simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply, inv_inv]
    rw [e]
    exact (Subgroup.zpowers b).zpow_mem hβzp k
  exact hgne (Subgroup.eq_of_le_of_card_ge hle_conj (by
    rw [CFSG.conjugate, Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective]))

end SettingCore

end CFSG.StandardType.GGFF

end
