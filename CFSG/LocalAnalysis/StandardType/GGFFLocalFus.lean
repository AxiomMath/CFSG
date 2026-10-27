module

public import CFSG.LocalAnalysis.StandardType.GGFFLocal

@[expose] public section

namespace CFSG.StandardType.GGFF

open CFSG.RankThree.PartTwo.Sec21.FF79 (Cen CenS Nor)
open CFSG.RankThree.PartTwo.Sec4.Item434Kit (vecElt)

variable {G : Type} [Group G] [Finite G]

namespace SettingCore

variable {b : G} {K : Subgroup G} {z : Fin 3 → K}

theorem exists_conj_mem_Bt (h : SettingCore b K z) {x : G} (hx : x ∈ Cen b) (hx3 : x ^ 3 = 1) :
    ∃ l ∈ K, ∃ β ∈ Bt b z, x = l * β * l⁻¹ := by
  obtain ⟨k, hkK, hk3, j, rfl⟩ := h.cube_decomp hx hx3
  have hk3' : (⟨k, hkK⟩ : K) ^ 3 = 1 := Subtype.ext (by simpa using hk3)
  obtain ⟨l, v, hl⟩ := h.model.fus ⟨k, hkK⟩ hk3'
  have hl' : k = (l : G) * vecElt (zs z) v * (l : G)⁻¹ := by
    have := congrArg (fun y : K => (y : G)) hl
    simpa [Subgroup.coe_mul, ← vecElt_zs] using this
  refine ⟨l, l.2, vecElt (zs z) v * b ^ j,
    (Bt b z).mul_mem (tor_le_Bt b z (vecElt_mem_tor _ v))
      ((Bt b z).zpow_mem (b_mem_Bt b z) j), ?_⟩
  rw [hl']
  have hcl : Commute (l : G) b := h.comm_of_mem l.2
  have hcomm : (l : G)⁻¹ * b ^ j = b ^ j * (l : G)⁻¹ :=
    (hcl.inv_left.zpow_right j).eq
  calc (l : G) * vecElt (zs z) v * (l : G)⁻¹ * b ^ j
      = (l : G) * vecElt (zs z) v * ((l : G)⁻¹ * b ^ j) := by group
    _ = (l : G) * vecElt (zs z) v * (b ^ j * (l : G)⁻¹) := by rw [hcomm]
    _ = (l : G) * (vecElt (zs z) v * b ^ j) * (l : G)⁻¹ := by group

theorem fusC (h : SettingCore b K z) {g : G} (hg : g * b * g⁻¹ ∈ Cen b) :
    ∃ n ∈ Nor (Bt b z), ∃ c ∈ Cen b, g * b * g⁻¹ = c * (n * b * n⁻¹) * c⁻¹ := by
  have hx3 : (g * b * g⁻¹) ^ 3 = 1 := by rw [conj_pow, h.b_cube]; group
  obtain ⟨l, hlK, β, hβB, hxβ⟩ := h.exists_conj_mem_Bt hg hx3
  have hβeq : β = (l⁻¹ * g) * b * (l⁻¹ * g)⁻¹ := by
    have h1 : β = l⁻¹ * (g * b * g⁻¹) * l := by rw [hxβ]; group
    rw [h1]; group
  obtain ⟨n, hn, hnb⟩ := h.fusion hβB hβeq.symm
  exact ⟨n, hn, l, h.le hlK, by rw [hxβ, hnb]⟩

end SettingCore

end CFSG.StandardType.GGFF

end
