module

public import CFSG.Quasithin.MS93.S4AVtx

public section

namespace CFSG.Quasithin.MS93.S4A

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible

section Conj

variable {G : Type*} [Group G]

theorem map_conj_le_conjCl {H K : Subgroup G} {g : G} (hg : g ∈ H) :
    K.map (MulAut.conj g).toMonoidHom ≤ conjCl H K :=
  le_iSup₂_of_le (f := fun g (_ : g ∈ H) => K.map (MulAut.conj g).toMonoidHom) g hg le_rfl

end Conj

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
include h

theorem concl441_smul_of (g : (puAmalgam h.le).Universal) {α γ : Vtx (puAmalgam h.le)}
    (hc : Concl441 h.le L α γ) : Concl441 h.le L (g • α) (g • γ) := by
  have hinj : Function.Injective (MulAut.conj g).toMonoidHom := (MulAut.conj g).injective
  intro hH
  rw [zm_smul, qv_smul, dloc_smul h, ← Subgroup.map_commutator,
    Subgroup.map_le_map_iff_of_injective hinj] at hH
  obtain ⟨h1, h2⟩ := hc hH
  rw [zm_smul, qv_smul, qv_smul, dloc_smul h, stab_smul, ← conjCl_map_conj,
    ← Subgroup.map_inf_eq _ _ _ hinj, ← Subgroup.map_commutator,
    Subgroup.map_le_map_iff_of_injective hinj, zm_smul]
  refine ⟨h1, ?_⟩
  rintro _ ⟨y, hy, rfl⟩ hy'
  rw [← MonoidHom.map_zpowers, ← Subgroup.map_commutator,
    Subgroup.map_le_map_iff_of_injective hinj] at hy'
  rw [← MonoidHom.map_zpowers, ← Subgroup.map_commutator, ← Subgroup.map_sup,
    Subgroup.map_le_map_iff_of_injective hinj]
  exact h2 y hy hy'

theorem concl441_smul (g : (puAmalgam h.le).Universal) (α γ : Vtx (puAmalgam h.le)) :
    Concl441 h.le L (g • α) (g • γ) ↔ Concl441 h.le L α γ := by
  refine ⟨fun hc => ?_, concl441_smul_of h g⟩
  simpa [smul_smul] using concl441_smul_of h g⁻¹ hc

theorem stab_le_normalizer_dloc (μ : Vtx (puAmalgam h.le)) :
    stab _ μ ≤ Subgroup.normalizer (Dloc h.le L μ : Set (puAmalgam h.le).Universal) :=
  stab_le_normalizer_puTrans h.le (S4A.Dq_normal h) μ

theorem stab_le_normalizer_uloc (μ : Vtx (puAmalgam h.le)) :
    stab _ μ ≤ Subgroup.normalizer (Uloc h.le L μ : Set (puAmalgam h.le).Universal) :=
  stab_le_normalizer_puTrans h.le (S4A.Uq_normal h) μ

theorem commutator_conjCl_inf_le_dloc {α γ : Vtx (puAmalgam h.le)}
    (hc : Concl441 h.le L α γ) (hZ : ZM _ α ≤ stab _ γ) :
    ⁅conjCl (stab _ γ) (ZM (puAmalgam h.le) α), Qv _ α ⊓ Qv _ γ⁆ ≤ Dloc h.le L γ := by
  by_cases hH : ⁅ZM (puAmalgam h.le) α, Qv _ γ⁆ ≤ Dloc h.le L γ
  · refine (Subgroup.commutator_mono le_rfl inf_le_right).trans ?_
    exact commutator_conjCl_le (stab_le_normalizer_dloc h γ) (stab_le_normalizer_qv _ γ)
      (hZ.trans (stab_le_normalizer_dloc h γ)) hH
  · exact (hc hH).1

theorem dloc_le_centralizer_ltil {μ : Vtx (puAmalgam h.le)} (hμ : IsMVtx _ μ) :
    Dloc h.le L μ ≤ Subgroup.centralizer (Ltil h.le L μ : Set (puAmalgam h.le).Universal) := by
  rw [Dloc, h.puTrans_Dq hμ]
  exact inf_le_right

theorem dloc_le_qv {μ : Vtx (puAmalgam h.le)} (hμ : IsMVtx _ μ) :
    Dloc h.le L μ ≤ Qv _ μ := by
  rw [Dloc, h.puTrans_Dq hμ]
  exact inf_le_left

theorem uloc_inf_dloc {F : Type} [Field F] [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)}
    (hφ : IsSL3FullVia M T L φ) (μ : Vtx (puAmalgam h.le)) :
    Uloc h.le L μ ⊓ Dloc h.le L μ = ⊥ := by
  have hUD : Uq M T L ⊓ Dq M L = ⊥ := by
    rw [h.Uq_inf_Dq, ← h.Uq_inf_Zq, inf_comm]
    exact hφ.2.2.2.1
  rw [Uloc, Dloc, ← puTrans_inf, hUD, puTrans, Subgroup.bot_subgroupOf, transN_bot]

theorem exists_ltil_smul_eq (hfull : IsSL3Full M T L) {μ ρ ν : Vtx (puAmalgam h.le)}
    (hμ : IsMVtx _ μ) (hμρ : (puAmalgam h.le).treeGraph.Adj μ ρ)
    (hρν : (puAmalgam h.le).treeGraph.Adj ρ ν) {g : (puAmalgam h.le).Universal}
    (hg : g ∈ stab _ μ) : ∃ l ∈ Ltil h.le L μ, l • ν = g • ν := by
  have hnorm : Qv (puAmalgam h.le) μ ≤
      Subgroup.normalizer (Ltil h.le L μ : Set (puAmalgam h.le).Universal) :=
    (qv_le_stab _ μ).trans (stab_le_normalizer_ltil h μ)
  have hg' : g ∈ ((Ltil h.le L μ ⊔ Qv _ μ : Subgroup _) : Set (puAmalgam h.le).Universal) := by
    rw [← stab_eq_ltil_sup_qv h hfull hμ]
    exact hg
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hnorm] at hg'
  obtain ⟨l, hl, y, hy, rfl⟩ := hg'
  refine ⟨l, hl, ?_⟩
  have hyρ : y ∈ Qv (puAmalgam h.le) ρ := qv_le_qv _ h.hyp20 hμ hμρ hy
  have hyν : y • ν = ν := (mem_stab _).mp (qv_le_stab_of_adj _ hρν hyρ)
  rw [mul_smul, hyν]

theorem critR_le_uloc (hfull : IsSL3Full M T L) (hC : CentHyp (puAmalgam h.le))
    {α α' : Vtx (puAmalgam h.le)} (hc : IsCritical (puAmalgam h.le) α α') :
    ⁅ZM (puAmalgam h.le) α, ZM _ α'⁆ ≤ Uloc h.le L α := by
  have hZs : ZM (puAmalgam h.le) α' ≤ stab _ α :=
    zm_le_stab_right _ h.hyp20 h.critDist_pos hC (ms22_iii _ h.hyp20 h.critDist_pos hC hc)
  rw [commutator_zm_eq_uloc h hfull hc.1 hZs]
  exact Subgroup.le_normalizer_iff_commutator_le_left.mp
    (hZs.trans (stab_le_normalizer_uloc h α))

end CFSG.Quasithin.MS93.S4A
