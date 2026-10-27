module

public import CFSG.Quasithin.MS93.S34FFlat
import CFSG.Quasithin.MS93.S34EAB
import CFSG.Quasithin.MS93.S33LamW

public section

namespace CFSG.Quasithin.MS93.S34F

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

theorem qv_inf_centralizer_critR_le_flat_base (h : PUHyp M T L) (hU : IsSL3U M T L)
    {μ : Vtx (puAmalgam h.le)} (hcμ : IsCritical (puAmalgam h.le) μ (baseA _))
    (hμβ : geo _ (baseA (puAmalgam h.le)) μ 1 = baseB _) :
    Qv (puAmalgam h.le) (baseB _) ⊓
        Subgroup.centralizer (critR (puAmalgam h.le) μ (baseA _) : Set _) ≤
      flat h (baseA _) := by
  obtain ⟨-, -, n, F, _, _, a, hcard, ha, -, -, β, hβ, hβker, hβα⟩ := hU
  have hET := (S34E.pre_zm_le_not_le h hcμ hμβ).1
  obtain ⟨e, heE, g₀, hg₀, hmv⟩ := S34E.exists_crit_mat_sl h hcard ha hβ hβker hβα hcμ hμβ
  have hRM : ⁅Uq M T L, S33.pre h.le (ZM _ μ)⁆ ≤ M :=
    S33.commutator_le_of_le (Uq_le h.L_le) (S33.pre_le h.le _)
  rintro x ⟨hxT, hxC⟩
  rw [puAmalgam.qv_baseB, imM_of_le h.le le_rfl] at hxT
  obtain ⟨t, -, rfl⟩ := hxT
  rw [← S33.imM_commutator_pre h hcμ hET] at hxC
  have htC := S34E.mem_centralizer_of_ofT h hRM t hxC
  have hlin := S34E.mem_linPart_of_centralizer_sl h ha hβ hβker hβα (hET heE) hg₀ hmv
    (fun u hu => by
      rw [← commutatorElement_inv]
      exact inv_mem (Subgroup.commutator_mem_commutator hu heE)) t.2 htC
  obtain ⟨-, γ, hγ⟩ := hlin
  have hsup := S34D.mem_sup_of_isCoordAct_sl h hcard ha hβ hβker hβα t.2 hγ
  rw [flat, puTrans_baseA h.le (flat_subgroupOf_normal h), S34E.ofT_mem_imM_iff h]
  exact hsup

theorem qv_inf_centralizer_critR_le_flat (h : PUHyp M T L) (hU : IsSL3U M T L)
    {δ α' : Vtx (puAmalgam h.le)} (hc : IsCritical (puAmalgam h.le) δ α') :
    Qv (puAmalgam h.le) (geo _ α' δ 1) ⊓
        Subgroup.centralizer (critR (puAmalgam h.le) δ α' : Set _) ≤ flat h α' := by
  obtain ⟨k, hkα, hkβ, hcμ, hμβ⟩ := S33.exists_conj_of_isCritical _ h.hyp20 h.critDist_pos hc
  have hbase := qv_inf_centralizer_critR_le_flat_base h hU hcμ hμβ
  have hR : critR (puAmalgam h.le) δ α' =
      (critR (puAmalgam h.le) (k⁻¹ • δ) (baseA _)).map (MulAut.conj k).toMonoidHom := by
    rw [critR, critR, Subgroup.map_commutator, ← PU.zm_smul, ← PU.zm_smul, smul_inv_smul, hkα]
  rintro x ⟨hxQ, hxC⟩
  rw [← hkβ, PU.qv_smul] at hxQ
  obtain ⟨y, hyQ, rfl⟩ := hxQ
  rw [← hkα, flat, puTrans_smul h.le (flat_subgroupOf_normal h)]
  have hxC' : k * y * k⁻¹ ∈
      Subgroup.centralizer (critR (puAmalgam h.le) δ α' : Set (puAmalgam h.le).Universal) := hxC
  refine ⟨y, hbase (Subgroup.mem_inf.mpr ⟨hyQ, ?_⟩), rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  intro r hr
  have hkr : k * r * k⁻¹ ∈ critR (puAmalgam h.le) δ α' := by
    rw [hR]
    exact ⟨r, hr, rfl⟩
  have h1 := Subgroup.mem_centralizer_iff.mp hxC' _ hkr
  have h2 : k * (r * y) * k⁻¹ = k * (y * r) * k⁻¹ := by
    calc k * (r * y) * k⁻¹ = k * r * k⁻¹ * (k * y * k⁻¹) := by group
      _ = k * y * k⁻¹ * (k * r * k⁻¹) := h1
      _ = k * (y * r) * k⁻¹ := by group
  simpa using h2

end CFSG.Quasithin.MS93.S34F
