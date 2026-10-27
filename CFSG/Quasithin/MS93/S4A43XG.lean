module

public import CFSG.Quasithin.MS93.S4A43XF

public section

namespace CFSG.Quasithin.MS93.S4A

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

section WnabGen

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)

theorem exists_vv_not_le_of_wnab {α ρ : Vtx (puAmalgam h.le)} {Q : Subgroup _}
    (hW : ¬ Wnab h.le L α ρ ≤ Q) :
    ∃ μ, (puAmalgam h.le).treeGraph.Adj ρ μ ∧ α ∈ nablaSet h.le L μ ∧
      ¬ Vv (puAmalgam h.le) μ ≤ Q := by
  by_contra hall
  push Not at hall
  exact hW (iSup₂_le fun μ hμ => hall μ hμ.1 hμ.2)

theorem vv_le_wnab {α ρ μ : Vtx (puAmalgam h.le)} (hρμ : (puAmalgam h.le).treeGraph.Adj ρ μ)
    (hαμ : α ∈ nablaSet h.le L μ) : Vv (puAmalgam h.le) μ ≤ Wnab h.le L α ρ :=
  le_iSup₂_of_le (f := fun μ (_ : μ ∈ {μ : Vtx (puAmalgam h.le) |
    (puAmalgam h.le).treeGraph.Adj ρ μ ∧ α ∈ nablaSet h.le L μ}) =>
    Vv (puAmalgam h.le) μ) μ ⟨hρμ, hαμ⟩ le_rfl

end WnabGen

namespace Ctx43

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} {h : PUHyp M T L}
  {F : Type} [Field F] [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)} (c : Ctx43 h φ)
include c

local notation "𝔛" => puAmalgam h.le
local notation "𝔘" => GoldAmalgam.Universal (puAmalgam h.le)
local notation "𝔄" => SimpleGraph.Adj (GoldAmalgam.treeGraph (puAmalgam h.le))

theorem commutator_vcirc_zm_eq {α α' ρ μ γ γ' : Vtx 𝔛} (hs : Star 𝔛 α α') (hαρ : 𝔄 α ρ)
    (hgen : Gab 𝔛 α ρ ⊔ ZM 𝔛 α' = stab 𝔛 α) (hρμ : 𝔄 ρ μ) (hαμ : α ∈ nablaSet h.le L μ)
    (hγ : IsMVtx 𝔛 γ) (hγγ' : 𝔄 γ γ') (hZγ : ZM 𝔛 γ ≤ Qv 𝔛 μ)
    (hVγ' : Vcirc h.le L μ ≤ Qv 𝔛 γ') (hVγ : ¬ Vcirc h.le L μ ≤ Qv 𝔛 γ)
    (hZc : ZM 𝔛 γ ≤ Subgroup.centralizer (ZM 𝔛 α' : Set 𝔘)) :
    ⁅Vcirc h.le L μ, ZM 𝔛 γ⁆ = Usup 𝔛 α ρ ⊓ Usup 𝔛 α (geo 𝔛 α α' 1) ∧
      ⁅Vcirc h.le L μ, ZM 𝔛 γ⁆ ≤ Uloc h.le L γ := by
  have hα := hs.1.1
  have hμM : IsMVtx 𝔛 μ := by
    have := isMVtx_iff_of_adj _ hρμ; have := isMVtx_iff_of_adj _ hαρ; tauto
  have hρgeo : geo 𝔛 μ α 1 = ρ :=
    (eq_geo_one _ hρμ.symm (by rw [dist_eq_one_of_adj _ hαρ.symm, hαμ.1])).symm
  have hαβ : 𝔄 α (geo 𝔛 α α' 1) := adj_geo_one_of_isCritical _ h.critDist_pos hs.1
  have hHα := (c.concl432 hμM).2 α hαμ
  rw [hρgeo] at hHα
  have h1 : ⁅Vcirc h.le L μ, ZM 𝔛 γ⁆ ≤ Usup 𝔛 α ρ := by
    refine (Subgroup.commutator_mono le_rfl hZγ).trans ?_
    rw [← hHα.2, ← hHα.1]
    exact le_rfl
  have hVs : Vcirc h.le L μ ≤ stab 𝔛 γ := hVγ'.trans (qv_le_stab_of_adj _ hγγ'.symm)
  have h2 : ⁅Vcirc h.le L μ, ZM 𝔛 γ⁆ ≤ Uloc h.le L γ := by
    rw [Subgroup.commutator_comm, commutator_zm_eq_uloc h c.full hγ hVs]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp
      (hVs.trans (stab_le_normalizer_puTrans h.le (S4A.Uq_normal h) γ))
  obtain ⟨z, hzZ, hzQ⟩ := IsConcreteLE.not_le_iff_exists.mp (c.not_zm_le_qv hs)
  have h3 : ⁅Vcirc h.le L μ, ZM 𝔛 γ⁆ ≤ Usup 𝔛 α (geo 𝔛 α α' 1) := fun u hu =>
    c.mem_usup_of_commute hα hαβ (zm_le_qv_geo_one_of_star h hs hzZ) hzQ
      (c.usup_le_uloc hα hαρ (h1 hu))
      (Subgroup.mem_centralizer_iff.mp (hZc (uloc_le_zm h c.full hγ (h2 hu))) z hzZ)
  obtain ⟨x, hxV, hxQ⟩ := IsConcreteLE.not_le_iff_exists.mp hVγ
  have h4 : Fintype.card F ≤ Nat.card ↥⁅Vcirc h.le L μ, ZM 𝔛 γ⁆ := by
    refine (c.le_card_commutator_uloc hγ hγγ' (hVγ' hxV) hxQ).trans ?_
    have hfin : Finite ↥⁅Vcirc h.le L μ, ZM 𝔛 γ⁆ := by
      have := finite_qv _ h.hyp20 (by rw [← isMVtx_iff_of_adj _ hγγ']; exact hγ)
      exact Finite.of_injective _ (Subgroup.inclusion_injective (h2.trans
        ((uloc_le_zm h c.full hγ).trans ((zm_le_qv_self _ hγ h.critDist_pos).trans
          (qv_le_qv _ h.hyp20 hγ hγγ')))))
    refine Subgroup.card_le_of_le ?_
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_mono ((Subgroup.zpowers_le).mpr hxV) (uloc_le_zm h c.full hγ)
  have hfinℓ : Finite ↥(Usup 𝔛 α ρ ⊓ Usup 𝔛 α (geo 𝔛 α α' 1)) := by
    have := finite_qv _ h.hyp20 (by rw [← isMVtx_iff_of_adj _ hαρ]; exact hα)
    exact Finite.of_injective _ (Subgroup.inclusion_injective (inf_le_left.trans
      ((c.usup_le_zh hα hαρ).trans (zh_le_qv _ _))))
  refine ⟨Subgroup.eq_of_le_of_card_ge (le_inf h1 h3) ?_, h2⟩
  rw [c.card_ell hs hαρ hgen]
  exact h4

theorem dist_geo_rev {α α' : Vtx 𝔛} (hs : Star 𝔛 α α') {i : ℕ} (hi : i ≤ critDist 𝔛) :
    (puAmalgam h.le).treeGraph.dist α (geo 𝔛 α' α i) = critDist 𝔛 - i := by
  have hd' : (puAmalgam h.le).treeGraph.dist α' α = critDist 𝔛 := (c.crit_symm hs).2.1
  rw [tdist_comm, dist_geo_right _ (by omega), hd']

theorem adj_geo_rev {α α' : Vtx 𝔛} (hs : Star 𝔛 α α') {i : ℕ} (hi : i < critDist 𝔛) :
    𝔄 (geo 𝔛 α' α i) (geo 𝔛 α' α (i + 1)) := by
  have hd' : (puAmalgam h.le).treeGraph.dist α' α = critDist 𝔛 := (c.crit_symm hs).2.1
  exact adj_geo _ (by omega)

theorem isMVtx_geo_rev {α α' : Vtx 𝔛} (hs : Star 𝔛 α α') {i : ℕ} (hi : i ≤ critDist 𝔛)
    (he : Even i) : IsMVtx 𝔛 (geo 𝔛 α' α i) := by
  have hd' : (puAmalgam h.le).treeGraph.dist α' α = critDist 𝔛 := (c.crit_symm hs).2.1
  rw [isMVtx_geo _ (by omega)]
  exact ⟨fun _ => he, fun _ => (c.crit_symm hs).1⟩

theorem not_isMVtx_geo_rev {α α' : Vtx 𝔛} (hs : Star 𝔛 α α') {i : ℕ} (hi : i ≤ critDist 𝔛)
    (ho : ¬ Even i) : ¬ IsMVtx 𝔛 (geo 𝔛 α' α i) := by
  have hd' : (puAmalgam h.le).treeGraph.dist α' α = critDist 𝔛 := (c.crit_symm hs).2.1
  rw [isMVtx_geo _ (by omega)]
  exact fun hh => ho (hh.mp (c.crit_symm hs).1)

theorem critR_le_zloc_of_le {α α' γ : Vtx 𝔛} (hs : Star 𝔛 α α') (hγ : IsMVtx 𝔛 γ)
    (hd : (puAmalgam h.le).treeGraph.dist α γ < critDist 𝔛)
    (hC : critR 𝔛 α α' ≤ stabCenter 𝔛 γ) : critR 𝔛 α α' ≤ Zloc h.le L γ := by
  refine le_trans ?_ (c.zm_inf_stabCenter_le_zloc hγ)
  refine le_inf (fun r hr => ?_) hC
  have hrZ := critR_le_zm h hs hr
  have hrQ : r ∈ Qv 𝔛 γ := zm_le_qv_of_dist_lt _ hs.1.1 hd hrZ
  have hr2 : r ^ 2 = 1 := (isElemAbelian_zm _ h.hyp20 h.critDist_pos hs.1.1).2 r hrZ
  rw [← xm_eq_zm h c.full hγ]
  refine Subgroup.subset_closure ⟨⟨hrQ, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩, hr2⟩
  exact ((mem_stabCenter_iff_comm _).mp (hC hr)).2 y (qv_le_stab _ γ hy)

theorem ell_eq_of_not_le {α α' ρ : Vtx 𝔛} (hs : Star 𝔛 α α') (hαρ : 𝔄 α ρ)
    (hgen : Gab 𝔛 α ρ ⊔ ZM 𝔛 α' = stab 𝔛 α)
    (hR0C : critR0 𝔛 α α' ≤ stabCenter 𝔛 (geo 𝔛 α' α 4))
    (hW : ¬ Wnab h.le L α ρ ≤ Qv 𝔛 (geo 𝔛 α' α 4)) :
    Usup 𝔛 α ρ ⊓ Usup 𝔛 α (geo 𝔛 α α' 1) =
      Usup 𝔛 α (geo 𝔛 α α' 1) ⊓ Uloc h.le L (geo 𝔛 α' α 4) := by
  have hb8 := c.eight_le_critDist
  have hα := hs.1.1
  have hρH : ¬ IsMVtx 𝔛 ρ := by rw [← isMVtx_iff_of_adj _ hαρ]; exact hα
  have hηM := c.isMVtx_geo_rev hs (i := 4) (by omega) (by decide)
  have hηκ : 𝔄 (geo 𝔛 α' α 4) (geo 𝔛 α' α 5) := c.adj_geo_rev hs (i := 4) (by omega)
  have hdη := c.dist_geo_rev hs (i := 4) (by omega)
  have hdκ := c.dist_geo_rev hs (i := 5) (by omega)
  obtain ⟨μ, hρμ, hαμ, hVμ⟩ := exists_vv_not_le_of_wnab h hW
  have hμM : IsMVtx 𝔛 μ := by have := isMVtx_iff_of_adj _ hρμ; tauto
  have hdμα : (puAmalgam h.le).treeGraph.dist μ α = 2 := hαμ.1
  have hVc : ¬ Vcirc h.le L μ ≤ Qv 𝔛 (geo 𝔛 α' α 4) := by
    intro hle
    apply hVμ
    refine (vv_le_vi_sup_commutator h c.full hμM hρμ.symm).trans (sup_le ?_ hle)
    refine vi_one_le_qv_of_dist h hρH ?_
    have := dist_triangle (puAmalgam h.le) ρ α (geo 𝔛 α' α 4)
    rw [dist_eq_one_of_adj _ hαρ.symm] at this
    omega
  have hVV : Vcirc h.le L μ ≤ Vv 𝔛 μ :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp
      ((ltil_le_stab h μ).trans (stab_le_normalizer_vv h μ))
  have hdμη : (puAmalgam h.le).treeGraph.dist μ (geo 𝔛 α' α 4) ≤ critDist 𝔛 - 2 := by
    have := dist_triangle (puAmalgam h.le) μ α (geo 𝔛 α' α 4)
    omega
  have hline := c.commutator_vcirc_zm_eq hs hαρ hgen hρμ hαμ hηM hηκ
    (zm_le_qv_of_dist_lt _ hηM (by rw [tdist_comm]; omega))
    (hVV.trans (vv_le_qv_of_dist h hμM (by
      have := dist_triangle (puAmalgam h.le) μ α (geo 𝔛 α' α 5)
      omega)))
    hVc (zm_le_centralizer_zm h hηM (c.crit_symm hs).1 (by
      rw [tdist_comm, dist_geo _ (by have := (c.crit_symm hs).2.1; omega)]; omega))
  have hle : Usup 𝔛 α ρ ⊓ Usup 𝔛 α (geo 𝔛 α α' 1) ≤
      Usup 𝔛 α (geo 𝔛 α α' 1) ⊓ Uloc h.le L (geo 𝔛 α' α 4) :=
    le_inf inf_le_right (hline.1 ▸ hline.2)
  have hRZ : critR 𝔛 α α' ≤ Zloc h.le L (geo 𝔛 α' α 4) :=
    c.critR_le_zloc_of_le hs hηM (by omega) ((critR_le_critR0 h hs).trans hR0C)
  have hαβ : 𝔄 α (geo 𝔛 α α' 1) := adj_geo_one_of_isCritical _ h.critDist_pos hs.1
  have hUZ : Usup 𝔛 α (geo 𝔛 α α' 1) ≤ ZM 𝔛 α :=
    (c.usup_le_uloc hα hαβ).trans (uloc_le_zm h c.full hα)
  have hinf : (Usup 𝔛 α (geo 𝔛 α α' 1) ⊓ Uloc h.le L (geo 𝔛 α' α 4)) ⊓ critR 𝔛 α α' = ⊥ := by
    rw [eq_bot_iff, ← uloc_inf_zloc h c.full (geo 𝔛 α' α 4)]
    exact fun x hx => ⟨hx.1.2, hRZ hx.2⟩
  have hcomm : critR 𝔛 α α' ≤ Subgroup.centralizer
      ((Usup 𝔛 α (geo 𝔛 α α' 1) ⊓ Uloc h.le L (geo 𝔛 α' α 4) : Subgroup 𝔘) : Set 𝔘) :=
    (critR_le_zm h hs).trans ((zm_le_centralizer_qv _ h.hyp20 hα).trans
      (Subgroup.centralizer_le ((inf_le_left.trans hUZ).trans (zm_le_qv_self _ hα h.critDist_pos))))
  have hfinU : Finite ↥(Usup 𝔛 α (geo 𝔛 α α' 1)) := by
    have := finite_qv _ h.hyp20 (by rw [← isMVtx_iff_of_adj _ hαβ]; exact hα)
    exact Finite.of_injective _ (Subgroup.inclusion_injective
      ((c.usup_le_zh hα hαβ).trans (zh_le_qv _ _)))
  have hfinS : Finite ↥(Usup 𝔛 α (geo 𝔛 α α' 1) ⊓ Uloc h.le L (geo 𝔛 α' α 4)) :=
    Finite.of_injective _ (Subgroup.inclusion_injective inf_le_left)
  have hfinR : Finite ↥(critR 𝔛 α α') :=
    Finite.of_injective _ (Subgroup.inclusion_injective (c.critR_le_usup hs))
  have hcard := card_sup_of_commute hcomm hinf
  have hle2 : (Usup 𝔛 α (geo 𝔛 α α' 1) ⊓ Uloc h.le L (geo 𝔛 α' α 4)) ⊔ critR 𝔛 α α' ≤
      Usup 𝔛 α (geo 𝔛 α α' 1) := sup_le inf_le_left (c.critR_le_usup hs)
  have h3 := Subgroup.card_le_of_le hle2
  rw [hcard, c.card_usup hα hαβ, c.card_critR hs] at h3
  have hq : 0 < Fintype.card F := Fintype.card_pos
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [c.card_ell hs hαρ hgen]
  nlinarith

theorem exists_gen_wnab_le {α α' : Vtx 𝔛} (hs : Star 𝔛 α α') :
    ∃ ρ, 𝔄 α ρ ∧ Gab 𝔛 α ρ ⊔ ZM 𝔛 α' = stab 𝔛 α ∧
      Wnab h.le L α ρ ≤ Qv 𝔛 (geo 𝔛 α' α 4) := by
  have hαβ : 𝔄 α (geo 𝔛 α α' 1) := adj_geo_one_of_isCritical _ h.critDist_pos hs.1
  obtain ⟨ρ₀, hρ₀, hg₀, -⟩ := c.exists_gen_ne hs hαβ
  by_cases hW₀ : Wnab h.le L α ρ₀ ≤ Qv 𝔛 (geo 𝔛 α' α 4)
  · exact ⟨ρ₀, hρ₀, hg₀, hW₀⟩
  have hR0C : critR0 𝔛 α α' ≤ stabCenter 𝔛 (geo 𝔛 α' α 4) := by
    by_contra hnC
    exact hW₀ ((c.concl436 hs hnC).2 ρ₀ hρ₀ hg₀)
  obtain ⟨ρ₁, hρ₁, hg₁, hne⟩ := c.exists_gen_ne hs hρ₀
  by_cases hW₁ : Wnab h.le L α ρ₁ ≤ Qv 𝔛 (geo 𝔛 α' α 4)
  · exact ⟨ρ₁, hρ₁, hg₁, hW₁⟩
  exact absurd ((c.ell_eq_of_not_le hs hρ₁ hg₁ hR0C hW₁).trans
    (c.ell_eq_of_not_le hs hρ₀ hg₀ hR0C hW₀).symm) hne

theorem commutator_wnab_ltil_le {α α' ρ : Vtx 𝔛} (hs : Star 𝔛 α α') (hαρ : 𝔄 α ρ)
    (hgen : Gab 𝔛 α ρ ⊔ ZM 𝔛 α' = stab 𝔛 α)
    (hW2 : Wnab h.le L α ρ ≤ Qv 𝔛 (geo 𝔛 α' α 2)) :
    ⁅Wnab h.le L α ρ ⊔ Vv 𝔛 α, Ltil h.le L α⁆ ≤ Vcirc h.le L α := by
  have hα := hs.1.1
  have hb8 := c.eight_le_critDist
  have hαβ : 𝔄 α (geo 𝔛 α α' 1) := adj_geo_one_of_isCritical _ h.critDist_pos hs.1
  have hZs := zm_le_stab_of_star h hs
  have hVn := stab_le_normalizer_vv h α
  have hWn : Gab 𝔛 α ρ ≤ Subgroup.normalizer (Wnab h.le L α ρ : Set 𝔘) :=
    gab_le_normalizer_wnab h (by omega) hα hαρ
  have hWZ : ⁅Wnab h.le L α ρ, ZM 𝔛 α'⁆ ≤ Vv 𝔛 α := by
    have hγε := c.adj_geo_rev hs (i := 1) (by omega)
    have hγM := c.isMVtx_geo_two' hs
    refine le_trans ?_ (critR0_le_vv h hs)
    rw [c.critR0_eq hs, Usup, zv_of_isMVtx _ (c.crit_symm hs).1, Subgroup.commutator_comm]
    exact Subgroup.commutator_mono le_rfl (hW2.trans (qv_le_qv _ h.hyp20 hγM hγε.symm))
  have hWs : Wnab h.le L α ρ ≤ stab 𝔛 α := (iSup₂_le fun μ hμ => by
    have hμM : IsMVtx 𝔛 μ := by
      have := isMVtx_iff_of_adj _ hμ.1; have := isMVtx_iff_of_adj _ hαρ; tauto
    exact vv_le_qv_of_dist h hμM (by rw [dist_eq_one_of_adj _ hμ.1.symm]; omega)).trans
    (qv_le_stab_of_adj _ hαρ.symm)
  have hVs : Vv 𝔛 α ≤ stab 𝔛 α := (vv_le_qv h c.hb hα).trans (qv_le_stab _ α)
  have hVZ : ⁅Vv 𝔛 α, ZM 𝔛 α'⁆ ≤ Vv 𝔛 α :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp (hZs.trans hVn)
  have hNZ : ⁅Wnab h.le L α ρ ⊔ Vv 𝔛 α, ZM 𝔛 α'⁆ ≤ Vv 𝔛 α :=
    S4A.commutator_sup_le_of hWZ hVZ (hWs.trans hVn) (hVs.trans hVn)
  have hNn : stab 𝔛 α ≤ Subgroup.normalizer ((Wnab h.le L α ρ ⊔ Vv 𝔛 α : Subgroup 𝔘) : Set 𝔘) := by
    rw [← hgen]
    refine sup_le ((le_inf hWn (inf_le_left.trans hVn)).trans
      (Subgroup.inf_normalizer_le_normalizer_sup _ _)) ?_
    exact le_normalizer_sup_of_comm_le (hZs.trans hVn) (hWZ.trans le_sup_right)
  have hker := commutator_ltil_le_of_comm_le h c.full hα hαβ hNn
    (zm_le_qv_geo_one_of_star h hs) (c.not_zm_le_qv hs) hVn hNZ
  exact commutator_ltil_le_vcirc h hα (sup_le hWs hVs) hker

theorem concl437i_of_le {α α' ρ : Vtx 𝔛} (hs : Star 𝔛 α α') (hαρ : 𝔄 α ρ)
    (hgen : Gab 𝔛 α ρ ⊔ ZM 𝔛 α' = stab 𝔛 α)
    (hW2 : Wnab h.le L α ρ ≤ Qv 𝔛 (geo 𝔛 α' α 2)) {μ : Vtx 𝔛} (hρμ : 𝔄 ρ μ)
    (hαμ : α ∈ nablaSet h.le L μ) :
    stab 𝔛 α ≤ Subgroup.normalizer ((Vv 𝔛 μ ⊔ Vv 𝔛 α : Subgroup 𝔘) : Set 𝔘) ∧
      ⁅Vv 𝔛 μ, Ltil h.le L α⁆ ≤ Vcirc h.le L α := by
  have hα := hs.1.1
  have hμM : IsMVtx 𝔛 μ := by
    have := isMVtx_iff_of_adj _ hρμ; have := isMVtx_iff_of_adj _ hαρ; tauto
  have hb8 := c.eight_le_critDist
  have hVL : ⁅Vv 𝔛 μ, Ltil h.le L α⁆ ≤ Vcirc h.le L α :=
    (Subgroup.commutator_mono ((vv_le_wnab h hρμ hαμ).trans le_sup_left) le_rfl).trans
      (c.commutator_wnab_ltil_le hs hαρ hgen hW2)
  refine ⟨?_, hVL⟩
  have hVn := stab_le_normalizer_vv h α
  have hVcV : Vcirc h.le L α ≤ Vv 𝔛 α :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp ((ltil_le_stab h α).trans hVn)
  rw [stab_eq_ltil_sup_qv h c.full hα]
  refine sup_le ?_ ?_
  · refine le_normalizer_sup_of_comm_le ((ltil_le_stab h α).trans hVn) ?_
    exact hVL.trans (hVcV.trans le_sup_right)
  · refine (le_inf ?_ ((qv_le_stab _ α).trans hVn)).trans
      (Subgroup.inf_normalizer_le_normalizer_sup _ _)
    exact (qv_le_qv _ h.hyp20 hα hαρ).trans ((qv_le_stab_of_adj _ hρμ).trans
      (stab_le_normalizer_vv h μ))

theorem ell_le_of_not_le_two {α α' ρ : Vtx 𝔛} (hs : Star 𝔛 α α') (hαρ : 𝔄 α ρ)
    (hgen : Gab 𝔛 α ρ ⊔ ZM 𝔛 α' = stab 𝔛 α)
    (hW4 : Wnab h.le L α ρ ≤ Qv 𝔛 (geo 𝔛 α' α 4))
    (hW2 : ¬ Wnab h.le L α ρ ≤ Qv 𝔛 (geo 𝔛 α' α 2)) :
    Usup 𝔛 α ρ ⊓ Usup 𝔛 α (geo 𝔛 α α' 1) ≤ Usup 𝔛 (geo 𝔛 α' α 2) (geo 𝔛 α' α 3) ∧
      Usup 𝔛 α ρ ⊓ Usup 𝔛 α (geo 𝔛 α α' 1) ≤ stabCenter 𝔛 (geo 𝔛 α' α 4) := by
  have hb8 := c.eight_le_critDist
  have hα := hs.1.1
  have hρH : ¬ IsMVtx 𝔛 ρ := by rw [← isMVtx_iff_of_adj _ hαρ]; exact hα
  have hγM := c.isMVtx_geo_rev hs (i := 2) (by omega) (by decide)
  have hηM := c.isMVtx_geo_rev hs (i := 4) (by omega) (by decide)
  have hζH := c.not_isMVtx_geo_rev hs (i := 3) (by omega) (by decide)
  have hγζ : 𝔄 (geo 𝔛 α' α 2) (geo 𝔛 α' α 3) := c.adj_geo_rev hs (i := 2) (by omega)
  have hζη : 𝔄 (geo 𝔛 α' α 3) (geo 𝔛 α' α 4) := c.adj_geo_rev hs (i := 3) (by omega)
  have hdγ := c.dist_geo_rev hs (i := 2) (by omega)
  obtain ⟨μ, hρμ, hαμ, hVμ⟩ := exists_vv_not_le_of_wnab h hW2
  have hμM : IsMVtx 𝔛 μ := by have := isMVtx_iff_of_adj _ hρμ; tauto
  have hVV : Vcirc h.le L μ ≤ Vv 𝔛 μ :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp
      ((ltil_le_stab h μ).trans (stab_le_normalizer_vv h μ))
  have hVc : ¬ Vcirc h.le L μ ≤ Qv 𝔛 (geo 𝔛 α' α 2) := by
    intro hle
    apply hVμ
    refine (vv_le_vi_sup_commutator h c.full hμM hρμ.symm).trans (sup_le ?_ hle)
    refine le_trans ?_ hs.2
    refine iSup₂_le fun x hx => zv_le_vv h ?_
    have := dist_triangle (puAmalgam h.le) α ρ x
    rw [dist_eq_one_of_adj _ hαρ] at this
    have hx' : (puAmalgam h.le).treeGraph.dist ρ x ≤ 1 := hx
    omega
  have hZγQμ : ZM 𝔛 (geo 𝔛 α' α 2) ≤ Qv 𝔛 μ := by
    rw [← c.cent μ ρ hμM hρμ.symm]
    refine le_inf (zm_le_qv_of_not_isMVtx _ h.hyp20 hγM hρH ?_) ?_
    · have := dist_triangle (puAmalgam h.le) (geo 𝔛 α' α 2) α ρ
      rw [dist_eq_one_of_adj _ hαρ, tdist_comm _ _ α, hdγ] at this
      omega
    · rw [Subgroup.le_centralizer_iff]
      refine le_trans ?_ (Subgroup.le_centralizer_iff.mp (zm_le_centralizer_qv _ h.hyp20 hγM))
      refine le_trans ?_ hs.2
      rw [← zv_of_isMVtx _ hμM]
      exact zv_le_vv h (by rw [tdist_comm]; exact hαμ.1.le)
  have hVT : Vcirc h.le L μ ≤ Qv 𝔛 (geo 𝔛 α' α 3) :=
    hVV.trans ((vv_le_wnab h hρμ hαμ).trans (hW4.trans (qv_le_qv _ h.hyp20 hηM hζη.symm)))
  have hline := c.commutator_vcirc_zm_eq hs hαρ hgen hρμ hαμ hγM hγζ hZγQμ hVT hVc
    (zm_le_centralizer_zm h hγM (c.crit_symm hs).1 (by
      rw [tdist_comm, dist_geo _ (by have := (c.crit_symm hs).2.1; omega)]; omega))
  have hNU : Usup 𝔛 α ρ ⊓ Usup 𝔛 α (geo 𝔛 α α' 1) ≤
      Usup 𝔛 (geo 𝔛 α' α 2) (geo 𝔛 α' α 3) := by
    rw [← hline.1, Usup, zv_of_isMVtx _ hγM, Subgroup.commutator_comm]
    exact Subgroup.commutator_mono le_rfl hVT
  refine ⟨hNU, ?_⟩
  by_cases hQ : Qv 𝔛 (geo 𝔛 α' α 2) = Qv 𝔛 (geo 𝔛 α' α 4)
  · exfalso
    have hZeq : ZM 𝔛 (geo 𝔛 α' α 2) = ZM 𝔛 (geo 𝔛 α' α 4) := by
      rw [← xm_eq_zm h c.full hγM, ← xm_eq_zm h c.full hηM, XM, XM, hQ]
    have hbot : ⁅Vcirc h.le L μ, ZM 𝔛 (geo 𝔛 α' α 2)⁆ = ⊥ := by
      rw [hZeq, Subgroup.commutator_eq_bot_iff_le_centralizer]
      exact Subgroup.le_centralizer_iff.mp ((zm_le_centralizer_qv _ h.hyp20 hηM).trans
        (Subgroup.centralizer_le ((hVV.trans (vv_le_wnab h hρμ hαμ)).trans hW4)))
    have hcard := c.card_ell hs hαρ hgen
    rw [← hline.1, hbot, Subgroup.card_bot] at hcard
    have : 1 < Fintype.card F := Fintype.one_lt_card
    omega
  · exact hNU.trans ((c.usup_le_zloc_of_ne hζH hγζ.symm hζη hQ).trans (c.zloc_le_stabCenter hηM))

theorem exists_gen_wnab_le_two {α α' ρ₁ : Vtx 𝔛} (hs : Star 𝔛 α α') (hαρ₁ : 𝔄 α ρ₁)
    (hg₁ : Gab 𝔛 α ρ₁ ⊔ ZM 𝔛 α' = stab 𝔛 α)
    (hW4₁ : Wnab h.le L α ρ₁ ≤ Qv 𝔛 (geo 𝔛 α' α 4))
    (hW2₁ : ¬ Wnab h.le L α ρ₁ ≤ Qv 𝔛 (geo 𝔛 α' α 2)) :
    ∃ ρ, 𝔄 α ρ ∧ Gab 𝔛 α ρ ⊔ ZM 𝔛 α' = stab 𝔛 α ∧
      Wnab h.le L α ρ ≤ Qv 𝔛 (geo 𝔛 α' α 2) := by
  have hb8 := c.eight_le_critDist
  have hγM := c.isMVtx_geo_rev hs (i := 2) (by omega) (by decide)
  have hηM := c.isMVtx_geo_rev hs (i := 4) (by omega) (by decide)
  have hγζ : 𝔄 (geo 𝔛 α' α 2) (geo 𝔛 α' α 3) := c.adj_geo_rev hs (i := 2) (by omega)
  obtain ⟨ρ₂, hαρ₂, hg₂, hne⟩ := c.exists_gen_ne hs hαρ₁
  obtain ⟨hℓ₁U, hℓ₁C⟩ := c.ell_le_of_not_le_two hs hαρ₁ hg₁ hW4₁ hW2₁
  have hcrit : ¬ critR 𝔛 α α' = ⊥ := ms22_ii _ h.hyp20 h.critDist_pos c.cent hs.1
  by_cases hW4₂ : Wnab h.le L α ρ₂ ≤ Qv 𝔛 (geo 𝔛 α' α 4)
  · by_cases hW2₂ : Wnab h.le L α ρ₂ ≤ Qv 𝔛 (geo 𝔛 α' α 2)
    · exact ⟨ρ₂, hαρ₂, hg₂, hW2₂⟩
    exfalso
    obtain ⟨hℓ₂U, -⟩ := c.ell_le_of_not_le_two hs hαρ₂ hg₂ hW4₂ hW2₂
    have hUβ : Usup 𝔛 α (geo 𝔛 α α' 1) ≤ Usup 𝔛 (geo 𝔛 α' α 2) (geo 𝔛 α' α 3) := by
      rw [← c.ell_sup_ell hs hαρ₂ hg₂ hαρ₁ hg₁ hne]
      exact sup_le hℓ₂U hℓ₁U
    apply hcrit
    rw [eq_bot_iff, ← uloc_inf_zloc h c.full (geo 𝔛 α' α 2)]
    exact le_inf ((c.critR_le_usup hs).trans (hUβ.trans (c.usup_le_uloc hγM hγζ)))
      ((critR_le_critR0 h hs).trans (c.critR0_le_zloc hs))
  · exfalso
    have hR0C : critR0 𝔛 α α' ≤ stabCenter 𝔛 (geo 𝔛 α' α 4) := by
      by_contra hnC
      exact hW4₂ ((c.concl436 hs hnC).2 ρ₂ hαρ₂ hg₂)
    have hℓ₂ := c.ell_eq_of_not_le hs hαρ₂ hg₂ hR0C hW4₂
    have hUβC : Usup 𝔛 α (geo 𝔛 α α' 1) ≤ stabCenter 𝔛 (geo 𝔛 α' α 4) := by
      rw [← c.ell_sup_critR hs hαρ₁ hg₁]
      exact sup_le hℓ₁C ((critR_le_critR0 h hs).trans hR0C)
    have hbot : Usup 𝔛 α ρ₂ ⊓ Usup 𝔛 α (geo 𝔛 α α' 1) ≤
        Uloc h.le L (geo 𝔛 α' α 4) ⊓ stabCenter 𝔛 (geo 𝔛 α' α 4) := by
      rw [hℓ₂]
      exact le_inf inf_le_right (inf_le_left.trans hUβC)
    rw [c.uloc_inf_stabCenter hηM, le_bot_iff] at hbot
    have hcard := c.card_ell hs hαρ₂ hg₂
    rw [hbot, Subgroup.card_bot] at hcard
    have : 1 < Fintype.card F := Fintype.one_lt_card
    omega

theorem concl437_i {α α' : Vtx 𝔛} (hs : Star 𝔛 α α') {μ : Vtx 𝔛}
    (hd : (puAmalgam h.le).treeGraph.dist α μ = 2) (hαμ : α ∈ nablaSet h.le L μ) :
    stab 𝔛 α ≤ Subgroup.normalizer ((Vv 𝔛 μ ⊔ Vv 𝔛 α : Subgroup 𝔘) : Set 𝔘) ∧
      ⁅Vv 𝔛 μ, Ltil h.le L α⁆ ≤ Vcirc h.le L α := by
  have hα := hs.1.1
  obtain ⟨ρ, hαρ, hgen, hW2⟩ : ∃ ρ, 𝔄 α ρ ∧ Gab 𝔛 α ρ ⊔ ZM 𝔛 α' = stab 𝔛 α ∧
      Wnab h.le L α ρ ≤ Qv 𝔛 (geo 𝔛 α' α 2) := by
    obtain ⟨ρ₁, hαρ₁, hg₁, hW4₁⟩ := c.exists_gen_wnab_le hs
    by_cases hW2₁ : Wnab h.le L α ρ₁ ≤ Qv 𝔛 (geo 𝔛 α' α 2)
    · exact ⟨ρ₁, hαρ₁, hg₁, hW2₁⟩
    · exact c.exists_gen_wnab_le_two hs hαρ₁ hg₁ hW4₁ hW2₁
  have hα1 : 𝔄 α (geo 𝔛 α μ 1) := adj_geo_one _ (by omega)
  have h1μ : 𝔄 (geo 𝔛 α μ 1) μ := by
    have := adj_geo (puAmalgam h.le) (u := α) (w := μ) (i := 1) (by omega)
    rwa [show geo 𝔛 α μ (1 + 1) = μ from geo_of_le _ (by omega)] at this
  obtain ⟨g, hg, hgρ⟩ := exists_mem_stab_smul _ hα1 hαρ
  have hgα : g • α = α := (mem_stab _).mp hg
  have hρgμ : 𝔄 ρ (g • μ) := by
    have := (adj_smul _ g _ _).mpr h1μ
    rwa [hgρ] at this
  have hαgμ : α ∈ nablaSet h.le L (g • μ) := by
    rw [← hgα]
    exact (mem_nablaSet_smul h g μ α).mpr hαμ
  obtain ⟨hN, hC⟩ := c.concl437i_of_le hs hαρ hgen hW2 hρgμ hαgμ
  have hVgμ : Vv 𝔛 (g • μ) = (Vv 𝔛 μ).map (MulAut.conj g).toMonoidHom := vi_smul _ g μ 2
  have hVα : (Vv 𝔛 α).map (MulAut.conj g).toMonoidHom = Vv 𝔛 α :=
    map_conj_eq_of_mem_normalizer (stab_le_normalizer_vv h α hg)
  have hLα : (Ltil h.le L α).map (MulAut.conj g).toMonoidHom = Ltil h.le L α :=
    map_conj_eq_of_mem_normalizer (stab_le_normalizer_ltil h α hg)
  have hVcα : (Vcirc h.le L α).map (MulAut.conj g).toMonoidHom = Vcirc h.le L α :=
    map_conj_eq_of_mem_normalizer
      (le_normalizer_commutator (stab_le_normalizer_vv h α) (stab_le_normalizer_ltil h α) hg)
  constructor
  · intro s hs'
    have hgs : g * s * g⁻¹ ∈ stab 𝔛 α :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hs') (Subgroup.inv_mem _ hg)
    have h1 := hN hgs
    rw [hVgμ, ← hVα, ← Subgroup.map_sup, normalizer_map_conj, mem_map_conj] at h1
    simpa [mul_assoc] using h1
  · have h2 := hC
    rw [hVgμ, ← hLα, ← Subgroup.map_commutator, ← hVcα] at h2
    exact (Subgroup.map_le_map_iff_of_injective (MulAut.conj g).injective).mp h2

end Ctx43

end CFSG.Quasithin.MS93.S4A
