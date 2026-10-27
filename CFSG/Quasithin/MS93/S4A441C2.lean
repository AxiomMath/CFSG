module

public import CFSG.Quasithin.MS93.S4A42
public import CFSG.Quasithin.MS93.S4A43Stmt
public import CFSG.Quasithin.MS93.S4A44Base

public section

namespace CFSG.Quasithin.MS93.S4A.C441

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Quasithin.MS93 CFSG.Quasithin.MS93.S4A
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

@[expose] def S441C2Wlog : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L)
    (F : Type) (_ : Field F) (_ : Fintype F) (φ : ↥M →* ↥(StatedSL 3 F)), Hyp40 h φ →
    4 < critDist (puAmalgam h.le) →
    ∀ α α' μ : Vtx (puAmalgam h.le), IsCritical (puAmalgam h.le) α α' →
      (∀ g : (puAmalgam h.le).Universal,
        ¬ Concl441 h.le L (g • α) (g • geo (puAmalgam h.le) α α' 2)) →
      (∃ g : (puAmalgam h.le).Universal, g • μ = α ∧ g • α = geo (puAmalgam h.le) α α' 2) →
      ∀ x ∈ ⁅ZM (puAmalgam h.le) μ, Qv (puAmalgam h.le) α⁆, x ∉ Dloc h.le L α →
        x ∉ Bloc h.le L α →
        ∃ k ∈ stab (puAmalgam h.le) α, ¬ ZM (puAmalgam h.le) α' ≤ Subgroup.normalizer
          ((⁅ZM (puAmalgam h.le) (k • μ), Qv (puAmalgam h.le) α⁆ ⊔ ZM (puAmalgam h.le) α :
            Subgroup (puAmalgam h.le).Universal) : Set (puAmalgam h.le).Universal)

@[expose] def S441C2NonCrit : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L)
    (F : Type) (_ : Field F) (_ : Fintype F) (φ : ↥M →* ↥(StatedSL 3 F)), Hyp40 h φ →
    4 < critDist (puAmalgam h.le) →
    ∀ α α' μ : Vtx (puAmalgam h.le), IsCritical (puAmalgam h.le) α α' →
      (∀ g : (puAmalgam h.le).Universal,
        ¬ Concl441 h.le L (g • α) (g • geo (puAmalgam h.le) α α' 2)) →
      (∃ g : (puAmalgam h.le).Universal, g • μ = α ∧ g • α = geo (puAmalgam h.le) α α' 2) →
      ∀ x ∈ ⁅ZM (puAmalgam h.le) μ, Qv (puAmalgam h.le) α⁆, x ∉ Dloc h.le L α →
        x ∉ Bloc h.le L α →
        ¬ ZM (puAmalgam h.le) α' ≤ Subgroup.normalizer
          ((⁅ZM (puAmalgam h.le) μ, Qv (puAmalgam h.le) α⁆ ⊔ ZM (puAmalgam h.le) α :
            Subgroup (puAmalgam h.le).Universal) : Set (puAmalgam h.le).Universal) →
        ZM (puAmalgam h.le) μ ≤ Qv (puAmalgam h.le) (geo (puAmalgam h.le) α' α 2) →
        ⁅ZM (puAmalgam h.le) μ, ZM (puAmalgam h.le) α'⁆ ≤
          ⁅⁅ZM (puAmalgam h.le) μ, Qv (puAmalgam h.le) α⁆, ZM (puAmalgam h.le) α'⁆ ⊔
            ZM (puAmalgam h.le) α

@[expose] def S441C2Cent : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L)
    (F : Type) (_ : Field F) (_ : Fintype F) (φ : ↥M →* ↥(StatedSL 3 F)), Hyp40 h φ →
    4 < critDist (puAmalgam h.le) →
    ∀ α α' μ : Vtx (puAmalgam h.le), IsCritical (puAmalgam h.le) α α' →
      (∀ g : (puAmalgam h.le).Universal,
        ¬ Concl441 h.le L (g • α) (g • geo (puAmalgam h.le) α α' 2)) →
      (∀ g : (puAmalgam h.le).Universal,
        ¬ IsC1 h.le L (Fintype.card F) (g • geo (puAmalgam h.le) α α' 2)
          (conjCl (stab (puAmalgam h.le) (g • geo (puAmalgam h.le) α α' 2))
            (ZM (puAmalgam h.le) (g • α)))
          (ZM (puAmalgam h.le) (g • geo (puAmalgam h.le) α α' 2))) →
      (∃ g : (puAmalgam h.le).Universal, g • μ = α ∧ g • α = geo (puAmalgam h.le) α α' 2) →
      ∀ x ∈ ⁅ZM (puAmalgam h.le) μ, Qv (puAmalgam h.le) α⁆, x ∉ Dloc h.le L α →
        ⁅ZM (puAmalgam h.le) μ, Qv (puAmalgam h.le) α⁆ ≤ Bloc h.le L α →
        ∃ k ∈ stab (puAmalgam h.le) α,
          (∃ w ∈ ZM (puAmalgam h.le) α', ⁅k * x * k⁻¹, w⁆ ∉ Dloc h.le L α) ∧
            ¬ ZM (puAmalgam h.le) (k • μ) ≤ Qv (puAmalgam h.le) (geo (puAmalgam h.le) α' α 2)

section Claim2

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
  {F : Type} [Field F] [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)} (hH : Hyp40 h φ)
include h hH

theorem claim2_of (h2w : S441C2Wlog) (h2n : S441C2NonCrit) (h2c : S441C2Cent)
    (hb : 4 < critDist (puAmalgam h.le)) {α α' : Vtx (puAmalgam h.le)}
    (hc : IsCritical (puAmalgam h.le) α α')
    (hfail : ∀ g : (puAmalgam h.le).Universal,
      ¬ Concl441 h.le L (g • α) (g • geo (puAmalgam h.le) α α' 2))
    (hc1 : ∀ g : (puAmalgam h.le).Universal,
      ¬ IsC1 h.le L (Fintype.card F) (g • geo (puAmalgam h.le) α α' 2)
        (conjCl (stab (puAmalgam h.le) (g • geo (puAmalgam h.le) α α' 2))
          (ZM (puAmalgam h.le) (g • α)))
        (ZM (puAmalgam h.le) (g • geo (puAmalgam h.le) α α' 2))) :
    ∃ μ : Vtx (puAmalgam h.le),
      (∃ g : (puAmalgam h.le).Universal, g • μ = α ∧ g • α = geo (puAmalgam h.le) α α' 2) ∧
      IsCritical (puAmalgam h.le) μ (geo (puAmalgam h.le) α' α 2) ∧
      geo (puAmalgam h.le) μ (geo (puAmalgam h.le) α' α 2) 2 = α ∧
      ⁅⁅ZM (puAmalgam h.le) μ, Qv (puAmalgam h.le) α⁆, ZM (puAmalgam h.le) α'⁆ ≠ ⊥ := by
  have h20 := h.hyp20
  have hb0 := h.critDist_pos
  have hα : IsMVtx _ α := hc.1
  have hd : (puAmalgam h.le).treeGraph.dist α α' = critDist (puAmalgam h.le) := hc.2.1
  have hγ : IsMVtx _ (geo (puAmalgam h.le) α α' 2) := isMVtx_geo_two _ h20 hb0 hc
  have hdαν : (puAmalgam h.le).treeGraph.dist α (geo (puAmalgam h.le) α' α 2) =
      critDist (puAmalgam h.le) - 2 := by
    rw [tdist_comm, dist_geo_right _ (by rw [tdist_comm]; omega), tdist_comm, hd]
  obtain ⟨g₀, hg₀⟩ := exists_smul_eq_of_isMVtx _ hγ hα
  obtain ⟨μ₀, g, hgμ, hgα⟩ : ∃ μ₀ : Vtx (puAmalgam h.le), ∃ g : (puAmalgam h.le).Universal,
      g • μ₀ = α ∧ g • α = geo (puAmalgam h.le) α α' 2 :=
    ⟨g₀ • α, g₀⁻¹, inv_smul_smul _ _, inv_smul_eq_iff.mpr hg₀.symm⟩
  have hconj₀ : ∃ g : (puAmalgam h.le).Universal,
      g • μ₀ = α ∧ g • α = geo (puAmalgam h.le) α α' 2 := ⟨g, hgμ, hgα⟩
  have hμ₀e : μ₀ = g⁻¹ • α := by rw [← hgμ, inv_smul_smul]
  have hαe : α = g⁻¹ • geo (puAmalgam h.le) α α' 2 := by rw [← hgα, inv_smul_smul]
  have hdμ₀ : (puAmalgam h.le).treeGraph.dist α μ₀ = 2 := by
    have h1 := dist_smul (puAmalgam h.le) g μ₀ α
    rw [hgμ, hgα] at h1
    rw [tdist_comm, ← h1, dist_geo _ (by omega)]
  have hμ₀M : IsMVtx (puAmalgam h.le) μ₀ := by
    rw [hμ₀e, isMVtx_smul]
    exact hα
  have hH0 : ¬ ⁅ZM (puAmalgam h.le) μ₀, Qv (puAmalgam h.le) α⁆ ≤ Dloc h.le L α := by
    intro hle
    apply hfail g⁻¹
    rw [← hμ₀e, ← hαe]
    intro hnot
    exact absurd hle hnot
  obtain ⟨x, hx, hxD⟩ := Set.not_subset.mp hH0
  have hgood : ∀ k ∈ stab (puAmalgam h.le) α,
      ¬ ZM (puAmalgam h.le) (k • μ₀) ≤ Qv (puAmalgam h.le) (geo (puAmalgam h.le) α' α 2) →
      ⁅⁅ZM (puAmalgam h.le) (k • μ₀), Qv (puAmalgam h.le) α⁆, ZM (puAmalgam h.le) α'⁆ ≠ ⊥ →
      ∃ μ : Vtx (puAmalgam h.le),
        (∃ g : (puAmalgam h.le).Universal, g • μ = α ∧ g • α = geo (puAmalgam h.le) α α' 2) ∧
        IsCritical (puAmalgam h.le) μ (geo (puAmalgam h.le) α' α 2) ∧
        geo (puAmalgam h.le) μ (geo (puAmalgam h.le) α' α 2) 2 = α ∧
        ⁅⁅ZM (puAmalgam h.le) μ, Qv (puAmalgam h.le) α⁆, ZM (puAmalgam h.le) α'⁆ ≠ ⊥ := by
    intro k hk hkQ hkne
    have hkα : k • α = α := (mem_stab _).mp hk
    have hdk : (puAmalgam h.le).treeGraph.dist α (k • μ₀) = 2 := by
      have := dist_smul (puAmalgam h.le) k α μ₀
      rw [hkα, hdμ₀] at this
      exact this
    have hkM : IsMVtx (puAmalgam h.le) (k • μ₀) := by
      rw [isMVtx_smul]
      exact hμ₀M
    have hdist : (puAmalgam h.le).treeGraph.dist (k • μ₀) (geo (puAmalgam h.le) α' α 2) =
        critDist (puAmalgam h.le) := by
      have t := dist_triangle (puAmalgam h.le) (k • μ₀) α (geo (puAmalgam h.le) α' α 2)
      rw [tdist_comm _ (k • μ₀) α, hdk, hdαν] at t
      by_contra hne
      exact hkQ (zm_le_qv_of_dist_lt _ hkM (by omega))
    refine ⟨k • μ₀, ?_, ⟨hkM, hdist, hkQ⟩, ?_, hkne⟩
    · obtain ⟨g, hg1, hg2⟩ := hconj₀
      refine ⟨g * k⁻¹, ?_, ?_⟩
      · rw [mul_smul, inv_smul_smul, hg1]
      · rw [mul_smul, ← hg2]
        congr 1
        rw [inv_smul_eq_iff, hkα]
    · have hadd : (puAmalgam h.le).treeGraph.dist (k • μ₀) (geo (puAmalgam h.le) α' α 2) =
          (puAmalgam h.le).treeGraph.dist (k • μ₀) α +
            (puAmalgam h.le).treeGraph.dist α (geo (puAmalgam h.le) α' α 2) := by
        rw [tdist_comm _ (k • μ₀) α, hdk, hdαν, hdist]
        omega
      have := eq_geo (puAmalgam h.le) hadd.symm
      rw [tdist_comm _ (k • μ₀) α, hdk] at this
      exact this.symm
  by_cases hall : ⁅ZM (puAmalgam h.le) μ₀, Qv (puAmalgam h.le) α⁆ ≤ Bloc h.le L α
  ·
    obtain ⟨k, hk, ⟨w, hw, hwx⟩, hkQ⟩ :=
      h2c G M T L h F inferInstance inferInstance φ hH hb α α' μ₀ hc hfail hc1 hconj₀ x hx hxD
        hall
    refine hgood k hk hkQ fun hbot => hwx ?_
    have hkx : k * x * k⁻¹ ∈ ⁅ZM (puAmalgam h.le) (k • μ₀), Qv (puAmalgam h.le) α⁆ := by
      have h1 : k * x * k⁻¹ ∈
          (⁅ZM (puAmalgam h.le) μ₀, Qv (puAmalgam h.le) α⁆).map (MulAut.conj k).toMonoidHom :=
        ⟨x, hx, rfl⟩
      rwa [Subgroup.map_commutator, ← zm_smul,
        map_conj_eq_of_mem_normalizer (stab_le_normalizer_qv _ α hk)] at h1
    have h1 : ⁅k * x * k⁻¹, w⁆ ∈
        ⁅⁅ZM (puAmalgam h.le) (k • μ₀), Qv (puAmalgam h.le) α⁆, ZM (puAmalgam h.le) α'⁆ :=
      Subgroup.commutator_mem_commutator hkx hw
    rw [hbot, Subgroup.mem_bot] at h1
    rw [h1]
    exact (Dloc h.le L α).one_mem
  ·
    clear x hx hxD
    obtain ⟨x, hx, hxB⟩ := Set.not_subset.mp hall
    have hxD : x ∉ Dloc h.le L α := by
      intro hxD
      apply hxB
      have hVn : Qv (puAmalgam h.le) α ≤
          Subgroup.normalizer (Vv (puAmalgam h.le) α : Set (puAmalgam h.le).Universal) :=
        (qv_le_stab _ α).trans (stab_le_normalizer_vv h α)
      have hZV : ZM (puAmalgam h.le) μ₀ ≤ Vv (puAmalgam h.le) α := by
        have := zv_le_vv h (α := α) (ρ := μ₀) hdμ₀.le
        rwa [zv_of_isMVtx _ hμ₀M] at this
      have hxV : x ∈ Vv (puAmalgam h.le) α :=
        Subgroup.le_normalizer_iff_commutator_le_left.mp hVn
          (Subgroup.commutator_mono hZV le_rfl hx)
      refine (mem_bloc_iff h (by omega) hα).mpr ⟨hxV, fun l hl => ?_⟩
      rw [(commutatorElement_eq_one_iff_mul_comm).mpr
        (Subgroup.mem_centralizer_iff.mp (dloc_le_centralizer_ltil h hα hxD) l hl).symm]
      exact (ZM (puAmalgam h.le) α).one_mem
    obtain ⟨k, hk, hkN⟩ :=
      h2w G M T L h F inferInstance inferInstance φ hH hb α α' μ₀ hc hfail hconj₀ x hx hxD hxB
    have hkα : k • α = α := (mem_stab _).mp hk
    have hdk : (puAmalgam h.le).treeGraph.dist α (k • μ₀) = 2 := by
      have := dist_smul (puAmalgam h.le) k α μ₀
      rw [hkα, hdμ₀] at this
      exact this
    have hkM : IsMVtx (puAmalgam h.le) (k • μ₀) := by
      rw [isMVtx_smul]
      exact hμ₀M
    have hconjk : ∃ g : (puAmalgam h.le).Universal,
        g • (k • μ₀) = α ∧ g • α = geo (puAmalgam h.le) α α' 2 := by
      obtain ⟨g, hg1, hg2⟩ := hconj₀
      refine ⟨g * k⁻¹, ?_, ?_⟩
      · rw [mul_smul, inv_smul_smul, hg1]
      · rw [mul_smul, ← hg2]
        congr 1
        rw [inv_smul_eq_iff, hkα]
    have hkx : k * x * k⁻¹ ∈ ⁅ZM (puAmalgam h.le) (k • μ₀), Qv (puAmalgam h.le) α⁆ := by
      have h1 : k * x * k⁻¹ ∈
          (⁅ZM (puAmalgam h.le) μ₀, Qv (puAmalgam h.le) α⁆).map (MulAut.conj k).toMonoidHom :=
        ⟨x, hx, rfl⟩
      rwa [Subgroup.map_commutator, ← zm_smul,
        map_conj_eq_of_mem_normalizer (stab_le_normalizer_qv _ α hk)] at h1
    have hkxD : k * x * k⁻¹ ∉ Dloc h.le L α := by
      intro hm
      apply hxD
      have h1 : k * x * k⁻¹ ∈ (Dloc h.le L α).map (MulAut.conj k).toMonoidHom := by
        rwa [map_conj_eq_of_mem_normalizer (stab_le_normalizer_dloc h α hk)]
      obtain ⟨y, hy, hyx⟩ := h1
      have : y = x := by
        simpa using hyx
      rwa [← this]
    have hkxB : k * x * k⁻¹ ∉ Bloc h.le L α := by
      intro hm
      apply hxB
      have hBn : stab (puAmalgam h.le) α ≤
          Subgroup.normalizer (Bloc h.le L α : Set (puAmalgam h.le).Universal) :=
        stab_le_normalizer_of_smul (F := fun δ => Bloc h.le L δ) _
          (fun g δ => bloc_smul h g δ) α
      have h1 : k * x * k⁻¹ ∈ (Bloc h.le L α).map (MulAut.conj k).toMonoidHom := by
        rwa [map_conj_eq_of_mem_normalizer (hBn hk)]
      obtain ⟨y, hy, hyx⟩ := h1
      have : y = x := by
        simpa using hyx
      rwa [← this]
    by_cases hkQ :
        ZM (puAmalgam h.le) (k • μ₀) ≤ Qv (puAmalgam h.le) (geo (puAmalgam h.le) α' α 2)
    · exfalso
      have hcomm := h2n G M T L h F inferInstance inferInstance φ hH hb α α' (k • μ₀) hc hfail
        hconjk (k * x * k⁻¹) hkx hkxD hkxB hkN hkQ
      have hZQ : ZM (puAmalgam h.le) (k • μ₀) ≤ Qv (puAmalgam h.le) α :=
        zm_le_qv_of_dist_lt _ hkM (by rw [tdist_comm, hdk]; omega)
      exact hkN (ms21_vi _ h20 hb0 hc hdk hZQ hcomm).2
    · refine hgood k hk hkQ fun hbot => hkN ?_
      have hcen : ZM (puAmalgam h.le) α' ≤ Subgroup.centralizer
          ((⁅ZM (puAmalgam h.le) (k • μ₀), Qv (puAmalgam h.le) α⁆ :
            Subgroup (puAmalgam h.le).Universal) : Set (puAmalgam h.le).Universal) := by
        rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer] at hbot
        exact hbot
      have hZs : ZM (puAmalgam h.le) α' ≤ stab _ α := zm_le_stab_of_isCritical _ h20 hb0 hc
      exact le_normalizer_sup (hcen.trans (Subgroup.centralizer_le_normalizer _))
        (hZs.trans (stab_le_normalizer_zm _ α))

end Claim2

end CFSG.Quasithin.MS93.S4A.C441
