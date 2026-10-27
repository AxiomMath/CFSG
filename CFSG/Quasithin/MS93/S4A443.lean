module

public import CFSG.Quasithin.MS93.S4A44Base
public import CFSG.Quasithin.MS93.S4A44Stmt

public section

namespace CFSG.Quasithin.MS93.S4A

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible


section Helpers

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
include h

theorem commutator_conjCl_inf_le_dloc_of_ltil (hb : 2 < critDist (puAmalgam h.le))
    {α γ ν : Vtx (puAmalgam h.le)} (hν : IsMVtx _ ν)
    (hdν : (puAmalgam h.le).treeGraph.dist ν γ = 2) (hc : Concl441 h.le L α γ)
    {l : (puAmalgam h.le).Universal} (hl : l ∈ Ltil h.le L γ) (hlν : l • ν = α) :
    ⁅conjCl (stab _ γ) (ZM (puAmalgam h.le) ν), Qv _ ν ⊓ Qv _ γ⁆ ≤ Dloc h.le L γ ∧
      ZM (puAmalgam h.le) α ≤ conjCl (stab _ γ) (ZM (puAmalgam h.le) ν) := by
  have hls : l ∈ stab (puAmalgam h.le) γ := ltil_le_stab h γ hl
  have hlγ : l⁻¹ • γ = γ := by
    rw [inv_smul_eq_iff]
    exact ((mem_stab _).mp hls).symm
  have hlα : l⁻¹ • α = ν := by rw [inv_smul_eq_iff, hlν]
  have hc' := concl441_smul_of h l⁻¹ hc
  rw [hlα, hlγ] at hc'
  refine ⟨commutator_conjCl_inf_le_dloc h hc'
    ((zm_le_qv_of_dist_lt _ hν (by omega)).trans (qv_le_stab _ γ)), ?_⟩
  rw [← hlν, zm_smul]
  exact map_conj_le_conjCl hls

end Helpers

theorem s443_of (h32 : S32) (h441 : S441) (h442 : S442) : S443 := by
  intro G _ _ M T L h F _ _ φ hH hb
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hH.2.2⟩
  have hC := centHyp_of_S32 h32 h
  have hb0 := h.critDist_pos
  by_contra hb6
  have h6 : critDist (puAmalgam h.le) = 6 := by
    obtain ⟨k, hk⟩ := ms21_v _ h.hyp20
    omega
  obtain ⟨α, α', hc, hs⟩ := h442 G M T L h F inferInstance inferInstance φ hH hb
  have hd : (puAmalgam h.le).treeGraph.dist α α' = 6 := hc.2.1.trans h6
  have hα := hc.1
  have hα' := hc.isMVtx_right (puAmalgam h.le) h.hyp20
  have hc' := ms22_iii (puAmalgam h.le) h.hyp20 hb0 hC hc
  have hadj : ∀ i, i < 6 →
      (puAmalgam h.le).treeGraph.Adj (geo (puAmalgam h.le) α α' i)
        (geo (puAmalgam h.le) α α' (i + 1)) :=
    fun i hi => adj_geo (puAmalgam h.le) (by omega)
  have hdist : ∀ i, i ≤ 6 → (puAmalgam h.le).treeGraph.dist α (geo (puAmalgam h.le) α α' i) = i :=
    fun i hi => dist_geo (puAmalgam h.le) (by omega)
  have hdist' : ∀ i, i ≤ 6 →
      (puAmalgam h.le).treeGraph.dist (geo (puAmalgam h.le) α α' i) α' = 6 - i :=
    fun i hi => by rw [dist_geo_right (puAmalgam h.le) (by omega), hd]
  have hM : ∀ i, i ≤ 6 → Even i → IsMVtx (puAmalgam h.le) (geo (puAmalgam h.le) α α' i) :=
    fun i hi he => (isMVtx_geo (puAmalgam h.le) (by omega)).mpr ⟨fun _ => he, fun _ => hα⟩
  have h0 : geo (puAmalgam h.le) α α' 0 = α := geo_zero (puAmalgam h.le) α α'
  have h6' : geo (puAmalgam h.le) α α' 6 = α' := geo_of_le (puAmalgam h.le) (by omega)
  have hsym : geo (puAmalgam h.le) α' α 2 = geo (puAmalgam h.le) α α' 4 := by
    have := geo_symm (puAmalgam h.le) (u := α) (w := α') (i := 4) (by omega)
    rwa [hd] at this
  obtain ⟨g₁, hg₁, hg₁e⟩ := hs 1 (by omega) (by omega)
  obtain ⟨g₂, hg₂, hg₂e⟩ := hs 2 (by omega) (by omega)
  simp only [show 2 * 1 = 2 from rfl, show 2 * 1 + 2 = 4 from rfl, show 2 * 1 - 2 = 0 from rfl,
    ] at hg₁ hg₁e
  rw [h0] at hg₁e
  simp only [show 2 * 2 = 4 from rfl, show 2 * 2 + 2 = 6 from rfl, show 2 * 2 - 2 = 2 from rfl,
    ] at hg₂ hg₂e
  rw [h6'] at hg₂e
  obtain ⟨l₁, hl₁, hl₁e⟩ := exists_ltil_smul_eq h hfull (hM 2 (by omega) (by decide))
    (hadj 2 (by omega)) (hadj 3 (by omega)) hg₁
  obtain ⟨l₂, hl₂, hl₂e⟩ := exists_ltil_smul_eq h hfull (hM 4 (by omega) (by decide))
    (hadj 4 (by omega)) (by have h5 := hadj 5 (by omega); rwa [h6'] at h5) hg₂
  simp only [show (3 : ℕ) + 1 = 4 from rfl] at hl₁e
  rw [hg₁e] at hl₁e
  rw [hg₂e] at hl₂e
  have hb2 : 2 < critDist (puAmalgam h.le) := by omega
  have hR2 : ⁅ZM (puAmalgam h.le) α, ZM (puAmalgam h.le) α'⁆ ≤
      Dloc h.le L (geo (puAmalgam h.le) α α' 2) := by
    obtain ⟨hcomm, hle⟩ := commutator_conjCl_inf_le_dloc_of_ltil h hb2
      (hM 4 (by omega) (by decide))
      (by rw [SimpleGraph.dist_comm, dist_geo_geo (puAmalgam h.le) (show 2 ≤ 4 by omega)
        (by omega)])
      (h441 G M T L h F inferInstance inferInstance φ hH hb α α' hc) hl₁ hl₁e
    refine (Subgroup.commutator_mono hle (le_inf ?_ ?_)).trans hcomm
    · exact zm_le_qv_of_dist_lt (puAmalgam h.le) hα'
        (by rw [SimpleGraph.dist_comm, hdist' 4 (by omega)]; omega)
    · exact zm_le_qv_of_dist_lt (puAmalgam h.le) hα'
        (by rw [SimpleGraph.dist_comm, hdist' 2 (by omega)]; omega)
  have hR4 : ⁅ZM (puAmalgam h.le) α, ZM (puAmalgam h.le) α'⁆ ≤
      Dloc h.le L (geo (puAmalgam h.le) α α' 4) := by
    have hc441 := h441 G M T L h F inferInstance inferInstance φ hH hb α' α hc'
    rw [hsym] at hc441
    have hl₂' : l₂⁻¹ ∈ Ltil h.le L (geo (puAmalgam h.le) α α' 4) := (Ltil h.le L _).inv_mem hl₂
    have hl₂e' : l₂⁻¹ • geo (puAmalgam h.le) α α' 2 = α' := by rw [inv_smul_eq_iff, hl₂e]
    obtain ⟨hcomm, hle⟩ := commutator_conjCl_inf_le_dloc_of_ltil h hb2
      (hM 2 (by omega) (by decide))
      (by rw [dist_geo_geo (puAmalgam h.le) (show 2 ≤ 4 by omega) (by omega)]) hc441 hl₂' hl₂e'
    rw [Subgroup.commutator_comm]
    refine (Subgroup.commutator_mono hle (le_inf ?_ ?_)).trans hcomm
    · exact zm_le_qv_of_dist_lt (puAmalgam h.le) hα (by rw [hdist 2 (by omega)]; omega)
    · exact zm_le_qv_of_dist_lt (puAmalgam h.le) hα (by rw [hdist 4 (by omega)]; omega)
  have hDD : Dloc h.le L (geo (puAmalgam h.le) α α' 2) ⊓
      Dloc h.le L (geo (puAmalgam h.le) α α' 4) ≤ Dloc h.le L α := by
    intro x ⟨hx2, hx4⟩
    have hcx : l₁ * x * l₁⁻¹ = x := by
      have := Subgroup.mem_centralizer_iff.mp
        (dloc_le_centralizer_ltil h (hM 2 (by omega) (by decide)) hx2) l₁ hl₁
      rw [this, mul_inv_cancel_right]
    rw [← hcx, ← hl₁e, dloc_smul h]
    exact ⟨x, hx4, rfl⟩
  have hR : ⁅ZM (puAmalgam h.le) α, ZM (puAmalgam h.le) α'⁆ ≤ Uloc h.le L α ⊓ Dloc h.le L α :=
    le_inf (critR_le_uloc h hfull hC hc) ((le_inf hR2 hR4).trans hDD)
  rw [uloc_inf_dloc h hH.2.2, le_bot_iff] at hR
  exact ms22_ii (puAmalgam h.le) h.hyp20 hb0 hC hc hR

end CFSG.Quasithin.MS93.S4A
