module

public import CFSG.Quasithin.MS93.S4A432F

public section

namespace CFSG.Quasithin.MS93.S4A

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

section Dist

universe u v

variable {A B : Type u} {C : Type v} [Group A] [Group C] [Group B] (X : GoldAmalgam A C B)

theorem zv_le_qv_of_dist_lt {ν μ : Vtx X} (hd : X.treeGraph.dist ν μ < critDist X) :
    Zv X ν ≤ Qv X μ := by
  by_cases hν : IsMVtx X ν
  · rw [zv_of_isMVtx X hν]; exact zm_le_qv_of_dist_lt X hν hd
  · rw [zv_of_not_isMVtx X hν]
    by_cases hνμ : ν = μ
    · subst hνμ; exact zh_le_qv X ν
    have hpos : 0 < X.treeGraph.dist ν μ := by
      rcases Nat.eq_zero_or_pos (X.treeGraph.dist ν μ) with h0 | h0
      · exact absurd ((dist_eq_zero_iff X).mp h0) hνμ
      · exact h0
    have hadj := adj_geo_one X hpos
    have hρ : IsMVtx X (geo X ν μ 1) := by
      by_contra hρ; exact hν ((isMVtx_iff_of_adj X hadj).mpr hρ)
    refine (zh_le_zm X hadj.symm).trans (zm_le_qv_of_dist_lt X hρ ?_)
    rw [dist_geo_right X (show 1 ≤ X.treeGraph.dist ν μ by omega)]
    omega

theorem dist_geo_of_adj_of_ne {u w x : Vtx X} {i : ℕ} (hi : 1 ≤ i)
    (hiw : i ≤ X.treeGraph.dist u w) (hux : X.treeGraph.Adj u x) (hne : x ≠ geo X u w 1) :
    X.treeGraph.dist x (geo X u w i) = i + 1 := by
  have hgeo : geo X u (geo X u w i) 1 = geo X u w 1 := geo_geo X hi hiw
  have hne' : u ≠ geo X u w i := by
    intro heq
    have := dist_geo X hiw
    rw [← heq, SimpleGraph.dist_self] at this
    omega
  rw [dist_eq_add_one_of_adj_of_ne X hux (by rw [hgeo]; exact hne) hne', dist_geo X hiw]

end Dist

section Lines

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
  (hfull : IsSL3Full M T L)
include h hfull

theorem eq_bot_of_le_usup_all {F : Type} [Field F] [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)}
    (hφ : IsSL3FullVia M T L φ) {ω : Vtx (puAmalgam h.le)} (hω : IsMVtx _ ω)
    (hUq : ∀ l : Vtx (puAmalgam h.le), (puAmalgam h.le).treeGraph.Adj ω l →
      Nat.card ↥(Usup (puAmalgam h.le) ω l) = Fintype.card F ^ 2)
    {R' : Subgroup (puAmalgam h.le).Universal}
    (hall : ∀ l : Vtx (puAmalgam h.le), (puAmalgam h.le).treeGraph.Adj ω l →
      R' ≤ Usup (puAmalgam h.le) ω l) : R' = ⊥ := by
  have hb0 := h.critDist_pos
  set I : Subgroup (puAmalgam h.le).Universal :=
    ⨅ l ∈ (puAmalgam h.le).treeGraph.neighborSet ω, Usup (puAmalgam h.le) ω l with hIdef
  have hR'I : R' ≤ I := le_iInf₂ fun l hl => hall l hl
  obtain ⟨l₀, hl₀⟩ := exists_adj (puAmalgam h.le) ω
  have hIl₀ : I ≤ Usup (puAmalgam h.le) ω l₀ := iInf₂_le l₀ hl₀
  have hUn : stab (puAmalgam h.le) ω ≤
      Subgroup.normalizer (Uloc h.le L ω : Set (puAmalgam h.le).Universal) :=
    stab_le_normalizer_puTrans h.le (S4A.Uq_normal h) ω
  have hUsU : ∀ l : Vtx (puAmalgam h.le), (puAmalgam h.le).treeGraph.Adj ω l →
      Usup (puAmalgam h.le) ω l ≤ Uloc h.le L ω := by
    intro l hl
    rw [usup_eq_commutator_uloc h hfull hω hl]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp
      ((qv_le_stab_of_adj _ hl.symm).trans hUn)
  have hIU : I ≤ Uloc h.le L ω := hIl₀.trans (hUsU l₀ hl₀)
  have hIn : stab (puAmalgam h.le) ω ≤
      Subgroup.normalizer (I : Set (puAmalgam h.le).Universal) := by
    refine le_normalizer_of_map_conj_le fun g hg => le_iInf₂ fun l hl => ?_
    have hgω : g • ω = ω := (mem_stab _).mp hg
    have hl' : (puAmalgam h.le).treeGraph.Adj ω (g⁻¹ • l) := by
      have := (adj_smul _ g⁻¹ ω l).mpr hl
      rwa [show g⁻¹ • ω = ω from inv_smul_eq_iff.mpr hgω.symm] at this
    have h1 : I ≤ Usup (puAmalgam h.le) ω (g⁻¹ • l) := iInf₂_le _ hl'
    refine (Subgroup.map_mono h1).trans ?_
    rw [← usup_smul, hgω, smul_inv_smul]
  have hIZ : I ≤ Zloc h.le L ω := by
    by_contra hIZ
    have hUI := uloc_le_of_normal h hfull hφ hω (hIU.trans (uloc_le_zm h hfull hω)) hIn hIZ
    have := finite_stab h hω
    have hfinU : Finite ↥(Uloc h.le L ω) := Finite.of_injective _
      (Subgroup.inclusion_injective ((uloc_le_zm h hfull hω).trans
        ((zm_le_qv_self _ hω hb0).trans (qv_le_stab _ ω))))
    have hfinS : Finite ↥(Usup (puAmalgam h.le) ω l₀) :=
      Finite.of_injective _ (Subgroup.inclusion_injective (hUsU l₀ hl₀))
    have h1 := Subgroup.card_le_of_le (hUI.trans hIl₀)
    obtain ⟨ψ, -, hψ⟩ := exists_natural_Uloc h hφ hω
    rw [card_eq_of_natural hψ, hUq l₀ hl₀, Nat.card_eq_fintype_card (α := F)] at h1
    have hq : 2 ≤ Fintype.card F := Fintype.one_lt_card
    have : Fintype.card F ^ 2 < Fintype.card F ^ 3 :=
      Nat.pow_lt_pow_right (by omega) (by norm_num)
    omega
  rw [eq_bot_iff]
  intro x hx
  have hmem : x ∈ Uloc h.le L ω ⊓ Zloc h.le L ω := ⟨hIU (hR'I hx), hIZ (hR'I hx)⟩
  rw [uloc_inf_zloc h hfull ω] at hmem
  exact hmem

end Lines

section Six

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
  (hfull : IsSL3Full M T L) {F : Type} [Field F] [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)}
  (hH : Hyp40 h φ) (hC : CentHyp (puAmalgam h.le)) (h42 : S42) (h431A : S431A)
  (h431B : S431B) (hb : 4 < critDist (puAmalgam h.le)) {α₀ α₀' : Vtx (puAmalgam h.le)}
  (hs : Star (puAmalgam h.le) α₀ α₀')
  (hk : ∀ μ : Vtx (puAmalgam h.le), IsMVtx _ μ → KindAt h.le L F true μ)
  (hCH : ∀ μ : Vtx (puAmalgam h.le), IsMVtx _ μ →
    ¬ ⁅Vv (puAmalgam h.le) μ, Qv (puAmalgam h.le) μ⁆ ≤ Dloc h.le L μ)
include h hfull hH hC h42 h431A h431B hb hs hk hCH

theorem exists_adj_mem_nablaSet_of_dual {ω l : Vtx (puAmalgam h.le)} (hω : IsMVtx _ ω)
    (hωl : (puAmalgam h.le).treeGraph.Adj ω l) :
    ∃ μ : Vtx (puAmalgam h.le), (puAmalgam h.le).treeGraph.Adj l μ ∧ μ ∈ nablaSet h.le L ω := by
  obtain ⟨ν₀, γ₀, hων₀, hν₀γ₀, hγ₀⟩ :=
    exists_mem_nablaSet_of_dual h hfull hH hC h42 h431A h431B hb hs hk hCH hω
  obtain ⟨g, hgω, hgν⟩ := exists_smul_edge_of_isMVtx _ hω hων₀ hω hωl
  refine ⟨g • γ₀, ?_, ?_⟩
  · rw [← hgν]
    exact (adj_smul _ g ν₀ γ₀).mpr hν₀γ₀
  · rw [← hgω]
    exact (mem_nablaSet_smul h g ω γ₀).mpr hγ₀

theorem vv_le_qv_of_dual (hb6 : 6 < critDist (puAmalgam h.le)) {α α' : Vtx (puAmalgam h.le)}
    (hsα : Star (puAmalgam h.le) α α') {ν₁ μ₂ : Vtx (puAmalgam h.le)}
    (hαν₁ : (puAmalgam h.le).treeGraph.Adj α ν₁) (hν₁μ₂ : (puAmalgam h.le).treeGraph.Adj ν₁ μ₂)
    (hμ₂ : μ₂ ∈ nablaSet h.le L α)
    (hR : ¬ critR (puAmalgam h.le) α α' ≤ Usup (puAmalgam h.le) α ν₁) :
    Vv (puAmalgam h.le) μ₂ ≤ Qv (puAmalgam h.le) (geo (puAmalgam h.le) α' α 4) := by
  classical
  have h20 := h.hyp20
  have hb0 := h.critDist_pos
  have hb2 : 2 < critDist (puAmalgam h.le) := by omega
  have hα := hsα.1.1
  have hd : (puAmalgam h.le).treeGraph.dist α α' = critDist (puAmalgam h.le) := hsα.1.2.1
  have hc' := ms22_iii _ h20 hb0 hC hsα.1
  have hd' : (puAmalgam h.le).treeGraph.dist α' α = critDist (puAmalgam h.le) := hc'.2.1
  have hα' := hc'.1
  set ω := geo (puAmalgam h.le) α' α 4 with hωdef
  have hω : IsMVtx (puAmalgam h.le) ω := by
    rw [hωdef, isMVtx_geo _ (by omega)]
    exact ⟨fun _ => ⟨2, rfl⟩, fun _ => hα'⟩
  have hωeq : ω = geo (puAmalgam h.le) α α' (critDist (puAmalgam h.le) - 4) := by
    rw [hωdef, ← geo_symm _ (show critDist (puAmalgam h.le) - 4 ≤
      (puAmalgam h.le).treeGraph.dist α α' by omega), hd]
    congr 1
    omega
  have hdαω : (puAmalgam h.le).treeGraph.dist α ω = critDist (puAmalgam h.le) - 4 := by
    rw [hωeq, dist_geo _ (by omega)]
  have hdα'ω : (puAmalgam h.le).treeGraph.dist α' ω = 4 := by
    rw [hωdef, dist_geo _ (by omega)]
  set β := geo (puAmalgam h.le) α α' 1 with hβdef
  have hαβ : (puAmalgam h.le).treeGraph.Adj α β := adj_geo_one_of_isCritical _ hb0 hsα.1
  have hZ'β : ZM (puAmalgam h.le) α' ≤ Qv _ β := zm_le_qv_geo_one _ h20 hb0 hsα.1
  have hZ's : ZM (puAmalgam h.le) α' ≤ stab _ α := zm_le_stab_right _ h20 hb0 hC hc'
  have hRβ : critR (puAmalgam h.le) α α' ≤ Usup (puAmalgam h.le) α β := by
    rw [critR, Usup, zv_of_isMVtx _ hα]
    exact Subgroup.commutator_mono le_rfl hZ'β
  have hν₁β : ν₁ ≠ β := by
    rintro rfl
    exact hR hRβ
  have hβω : geo (puAmalgam h.le) α ω 1 = β := by
    rw [hωeq, hβdef]
    exact geo_geo _ (by omega) (by omega)
  have hαω : α ≠ ω := by
    intro heq
    rw [← heq, SimpleGraph.dist_self] at hdαω
    omega
  have hdν₁ω : (puAmalgam h.le).treeGraph.dist ν₁ ω = critDist (puAmalgam h.le) - 3 := by
    rw [dist_eq_add_one_of_adj_of_ne _ hαν₁ (by rw [hβω]; exact hν₁β) hαω, hdαω]
    omega
  have hν₁ω : geo (puAmalgam h.le) ν₁ ω 1 = α :=
    (eq_geo_one _ hαν₁.symm (by rw [hdν₁ω, hdαω]; omega)).symm
  obtain ⟨hμ₂M, hZμ₂V⟩ := zm_le_vv_of_mem_nablaSet h hα hμ₂
  have hμ₂α : μ₂ ≠ α := by
    rintro rfl
    have := hμ₂.1
    rw [SimpleGraph.dist_self] at this
    omega
  have hν₁ne : ν₁ ≠ ω := by
    rintro rfl
    exact (isMVtx_iff_of_adj _ hαν₁).mp hα hω
  have hdμ₂ω : (puAmalgam h.le).treeGraph.dist μ₂ ω = critDist (puAmalgam h.le) - 2 := by
    rw [dist_eq_add_one_of_adj_of_ne _ hν₁μ₂ (by rw [hν₁ω]; exact hμ₂α) hν₁ne, hdν₁ω]
    omega
  refine iSup₂_le fun σ hσ => ?_
  have hσ' : (puAmalgam h.le).treeGraph.dist μ₂ σ ≤ 2 := hσ
  by_cases hlt : (puAmalgam h.le).treeGraph.dist σ ω < critDist (puAmalgam h.le)
  · exact zv_le_qv_of_dist_lt _ hlt
  have hdσω : (puAmalgam h.le).treeGraph.dist σ ω = critDist (puAmalgam h.le) := by
    have := dist_triangle (puAmalgam h.le) σ μ₂ ω
    rw [tdist_comm _ σ μ₂] at this
    omega
  have hdμ₂σ : (puAmalgam h.le).treeGraph.dist μ₂ σ = 2 := by
    have := dist_triangle (puAmalgam h.le) σ μ₂ ω
    rw [tdist_comm _ σ μ₂] at this
    omega
  have hσM : IsMVtx (puAmalgam h.le) σ :=
    ((even_dist_iff (puAmalgam h.le) μ₂ σ).mp (by rw [hdμ₂σ]; decide)).mp hμ₂M
  rw [zv_of_isMVtx _ hσM]
  by_contra hσQ
  set κ := σ with hκdef
  have hcrit : IsCritical (puAmalgam h.le) κ ω := ⟨hσM, hdσω, hσQ⟩
  have hcrit' := ms22_iii _ h20 hb0 hC hcrit
  have hZκs : ZM (puAmalgam h.le) κ ≤ stab _ ω := zm_le_stab_right _ h20 hb0 hC hcrit
  have hZωs : ZM (puAmalgam h.le) ω ≤ stab _ κ := zm_le_stab_right _ h20 hb0 hC hcrit'
  set R4 := critR (puAmalgam h.le) κ ω with hR4def
  have hR4ne : R4 ≠ ⊥ := ms22_ii _ h20 hb0 hC hcrit
  have hdκω : (puAmalgam h.le).treeGraph.dist κ ω = critDist (puAmalgam h.le) := hdσω
  have hdωκ : (puAmalgam h.le).treeGraph.dist ω κ = critDist (puAmalgam h.le) := by
    rw [tdist_comm]; exact hdσω
  have hμ₂eq : μ₂ = geo (puAmalgam h.le) κ ω 2 :=
    eq_geo_of_dist _ (by rw [tdist_comm]; exact hdμ₂σ)
      (by rw [tdist_comm _ κ μ₂, hdμ₂σ, hdμ₂ω, hdκω]; omega)
  have hκnab : κ ∈ nablaSet h.le L μ₂ := by
    rw [hμ₂eq]
    exact mem_nablaSet_geo_two h hfull hC hb2 hcrit
  set ν₃ := geo (puAmalgam h.le) μ₂ κ 1 with hν₃def
  have hμ₂ν₃ : (puAmalgam h.le).treeGraph.Adj μ₂ ν₃ := adj_geo_one _ (by rw [hdμ₂σ]; omega)
  have hν₃κ : (puAmalgam h.le).treeGraph.Adj ν₃ κ := by
    have := adj_geo (puAmalgam h.le) (u := μ₂) (w := κ) (i := 1) (by rw [hdμ₂σ]; omega)
    rwa [geo_of_le _ (show (puAmalgam h.le).treeGraph.dist μ₂ κ ≤ 1 + 1 by rw [hdμ₂σ])] at this
  obtain ⟨hcommκ, hUeqκ⟩ := commutator_zm_qv_eq_usup_of_dual h hfull hH hC h42 h431A h431B hb hs
    hk hCH hμ₂M hμ₂ν₃ hν₃κ hκnab
  have hZωQμ₂ : ZM (puAmalgam h.le) ω ≤ Qv _ μ₂ :=
    zm_le_qv_of_dist_lt _ hω (by rw [tdist_comm, hdμ₂ω]; omega)
  have hR4U : R4 ≤ Usup (puAmalgam h.le) μ₂ ν₃ := by
    rw [hR4def, critR, ← hcommκ]
    exact Subgroup.commutator_mono le_rfl hZωQμ₂
  have hUsμ₂ : Usup (puAmalgam h.le) μ₂ ν₃ ≤ Uloc h.le L μ₂ := by
    rw [usup_eq_commutator_uloc h hfull hμ₂M hμ₂ν₃]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp
      ((qv_le_stab_of_adj _ hμ₂ν₃.symm).trans
        (stab_le_normalizer_puTrans h.le (S4A.Uq_normal h) μ₂))
  have hR4Zω : R4 ≤ ZM (puAmalgam h.le) ω := by
    rw [hR4def, critR, Subgroup.commutator_comm]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp (hZκs.trans (stab_le_normalizer_zm _ ω))
  have hZα'cZω : ZM (puAmalgam h.le) ω ≤
      Subgroup.centralizer (ZM (puAmalgam h.le) α' : Set (puAmalgam h.le).Universal) :=
    zm_le_centralizer_zm h hω hα' (by rw [tdist_comm, hdα'ω]; omega)
  obtain ⟨-, hUαν₁q, -, -⟩ := concl433_edge h hfull h42 h431A h431B hH hC hs hα hαν₁
  obtain ⟨hUμ₂ν₁Z, -, -, -⟩ := concl433_edge h hfull h42 h431A h431B hH hC hs hμ₂M hν₁μ₂.symm
  have hcα := isC1_of_star h hH h431A hs hα
  have hRUα : critR (puAmalgam h.le) α α' = ⁅Uloc h.le L α, ZM (puAmalgam h.le) α'⁆ := by
    rw [critR, commutator_zm_eq_uloc h hfull hα hZ's]
  have hperp : ∀ v ∈ ZM (puAmalgam h.le) μ₂, v ∉ Bloc h.le L α →
      (∀ c ∈ ZM (puAmalgam h.le) α', ⁅v, c⁆ ∈ Bloc h.le L α) → False := by
    intro v hv hvB hvc
    apply hR
    rw [hRUα]
    exact commutator_uloc_le_usup_of_dual h hfull hb2 hα hcα (hk α hα) hαν₁ hν₁μ₂ hUαν₁q
      hUμ₂ν₁Z hv hvB hZ's hvc
  have hR4B : R4 ≤ Bloc h.le L α := by
    intro v hv
    by_contra hvB
    refine hperp v (uloc_le_zm h hfull hμ₂M (hUsμ₂ (hR4U hv))) hvB fun c hc => ?_
    have : ⁅v, c⁆ = 1 := by
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact (Subgroup.mem_centralizer_iff.mp (hZα'cZω (hR4Zω hv)) c hc).symm
    rw [this]
    exact Subgroup.one_mem _
  have hS2 := uloc_inf_bloc_eq_usup_of_dual h hfull hH hC h42 h431A h431B hb hs hk hCH hα hαν₁
    hν₁μ₂ hμ₂
  have hR4X : R4 ≤ Usup (puAmalgam h.le) α ν₁ := hS2 ▸ le_inf (hR4U.trans hUsμ₂) hR4B
  obtain ⟨ψ, -, hψ⟩ := exists_natural_Uloc h hH.2.2 hα
  have hTν₁s : Qv (puAmalgam h.le) ν₁ ≤ stab _ α := qv_le_stab_of_adj _ hαν₁.symm
  have hTβs : Qv (puAmalgam h.le) β ≤ stab _ α := qv_le_stab_of_adj _ hαβ.symm
  obtain ⟨hUαβZ, hUαβq, -, -⟩ := concl433_edge h hfull h42 h431A h431B hH hC hs hα hαβ
  have hq : 2 ≤ Nat.card F := Finite.one_lt_card
  have hfixZ' : fixN (natImage ψ (ZM (puAmalgam h.le) α')) =
      commN (natImage ψ (Qv (puAmalgam h.le) β)) :=
    fixN_eq_commN_of_le_qv h hfull hH.2.2 hα hαβ hUαβZ hUαβq hψ hZ'β hc'.2.2
  have hfinrk : ∀ ρ : Vtx (puAmalgam h.le), (puAmalgam h.le).treeGraph.Adj α ρ →
      Module.finrank F (commN (natImage ψ (Qv (puAmalgam h.le) ρ))) = 2 := by
    intro ρ hρ
    have := (concl433_edge h hfull h42 h431A h431B hH hC hs hα hρ).2.1
    rw [usup_eq_commutator_uloc h hfull hα hρ, card_commutator_eq hψ (qv_le_stab_of_adj _ hρ.symm),
      Module.natCard_eq_pow_finrank (K := F), ← Nat.card_eq_fintype_card] at this
    exact Nat.pow_right_injective hq this
  have hUU : ∀ ρ : Vtx (puAmalgam h.le), (puAmalgam h.le).treeGraph.Adj α ρ →
      Usup (puAmalgam h.le) α ρ ≤ Uloc h.le L α := by
    intro ρ hρ
    rw [usup_eq_commutator_uloc h hfull hα hρ]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp
      ((qv_le_stab_of_adj _ hρ.symm).trans (stab_le_normalizer_puTrans h.le (S4A.Uq_normal h) α))
  have hneW : commN (natImage ψ (Qv (puAmalgam h.le) ν₁)) ≠
      commN (natImage ψ (Qv (puAmalgam h.le) β)) := by
    intro heq
    apply hR
    intro u hu
    have huU : u ∈ Uloc h.le L α := hUU β hαβ (hRβ hu)
    have h1 := (mem_commutator_iff_natVec hψ hTβs ⟨u, huU⟩).mp
      (by rw [← usup_eq_commutator_uloc h hfull hα hαβ]; exact hRβ hu)
    rw [← heq] at h1
    rw [usup_eq_commutator_uloc h hfull hα hαν₁]
    exact (mem_commutator_iff_natVec hψ hTν₁s ⟨u, huU⟩).mpr h1
  have hinf1 := finrank_inf_planes_eq_one (hfinrk ν₁ hαν₁) (hfinrk β hαβ) hneW
  set P₀ := Usup (puAmalgam h.le) α ν₁ ⊓
    Subgroup.centralizer (ZM (puAmalgam h.le) α' : Set (puAmalgam h.le).Universal) with hP₀def
  have hZ'αs : ZM (puAmalgam h.le) α' ≤ stab (puAmalgam h.le) α := hZ's
  have hP₀card : Nat.card ↥P₀ ≤ Fintype.card F := by
    have hmem : ∀ x : ↥P₀, natVec hψ ⟨(x : (puAmalgam h.le).Universal), hUU ν₁ hαν₁ x.2.1⟩ ∈
        commN (natImage ψ (Qv (puAmalgam h.le) ν₁)) ⊓ commN (natImage ψ (Qv _ β)) := by
      intro x
      refine ⟨?_, ?_⟩
      · refine (mem_commutator_iff_natVec hψ hTν₁s _).mp ?_
        rw [← usup_eq_commutator_uloc h hfull hα hαν₁]
        exact x.2.1
      · rw [← hfixZ']
        exact (mem_centralizer_iff_natVec hψ hZ'αs _).mp x.2.2
    have hinj : Function.Injective (fun x : ↥P₀ =>
        (⟨_, hmem x⟩ : ↥(commN (natImage ψ (Qv (puAmalgam h.le) ν₁)) ⊓
          commN (natImage ψ (Qv _ β))))) := by
      intro x y hxy
      have := natVec_injective hψ (congrArg Subtype.val hxy)
      exact Subtype.ext (by simpa using congrArg Subtype.val this)
    calc Nat.card ↥P₀ ≤ Nat.card ↥(commN (natImage ψ (Qv (puAmalgam h.le) ν₁)) ⊓
          commN (natImage ψ (Qv _ β))) := Nat.card_le_card_of_injective _ hinj
      _ = Fintype.card F := by
        rw [Module.natCard_eq_pow_finrank (K := F), hinf1, pow_one, Nat.card_eq_fintype_card]
  have hR4P₀ : R4 ≤ P₀ := le_inf hR4X fun v hv => hZα'cZω (hR4Zω hv)
  have hR4card : Fintype.card F ≤ Nat.card ↥R4 := by
    have e : R4 = ⁅Uloc h.le L ω, ZM (puAmalgam h.le) κ⁆ := by
      rw [hR4def, critR, Subgroup.commutator_comm, commutator_zm_eq_uloc h hfull hω hZκs]
    rw [e]
    exact le_card_commutator_uloc_of_not_le h hH.2.2 hω hZκs hσQ
  have hUωq : ∀ l : Vtx (puAmalgam h.le), (puAmalgam h.le).treeGraph.Adj ω l →
      Nat.card ↥(Usup (puAmalgam h.le) ω l) = Fintype.card F ^ 2 := fun l hl =>
    (concl433_edge h hfull h42 h431A h431B hH hC hs hω hl).2.1
  obtain ⟨l, hωl, hlR4⟩ : ∃ l : Vtx (puAmalgam h.le), (puAmalgam h.le).treeGraph.Adj ω l ∧
      ¬ R4 ≤ Usup (puAmalgam h.le) ω l := by
    by_contra hall
    push Not at hall
    exact hR4ne (eq_bot_of_le_usup_all h hfull hH.2.2 hω hUωq hall)
  obtain ⟨μ, hlμ, hμ⟩ := exists_adj_mem_nablaSet_of_dual h hfull hH hC h42 h431A h431B hb hs hk
    hCH hω hωl
  obtain ⟨hμM, hZμV⟩ := zm_le_vv_of_mem_nablaSet h hω hμ
  have hR4ε : R4 ≤ Usup (puAmalgam h.le) ω (geo (puAmalgam h.le) ω κ 1) := by
    rw [hR4def, critR, Subgroup.commutator_comm, Usup, zv_of_isMVtx _ hω]
    exact Subgroup.commutator_mono le_rfl (zm_le_qv_geo_one_left _ h20 hb0 hC hcrit)
  have hlε : l ≠ geo (puAmalgam h.le) ω κ 1 := by
    rintro rfl
    exact hlR4 hR4ε
  have hαeq : α = geo (puAmalgam h.le) ω κ (critDist (puAmalgam h.le) - 4) := by
    have hdακ : (puAmalgam h.le).treeGraph.dist α κ ≤ 4 := by
      have h1 := dist_triangle (puAmalgam h.le) α ν₁ κ
      have h2 := dist_triangle (puAmalgam h.le) ν₁ μ₂ κ
      rw [dist_eq_one_of_adj _ hαν₁] at h1
      rw [dist_eq_one_of_adj _ hν₁μ₂, hdμ₂σ] at h2
      omega
    have h3 := dist_triangle (puAmalgam h.le) ω α κ
    rw [tdist_comm _ ω α, hdαω, hdωκ] at h3
    refine eq_geo_of_dist _ (by rw [tdist_comm, hdαω]) ?_
    rw [tdist_comm _ ω α, hdαω, hdωκ]
    omega
  have hμ₂eq' : μ₂ = geo (puAmalgam h.le) ω κ (critDist (puAmalgam h.le) - 2) := by
    refine eq_geo_of_dist _ (by rw [tdist_comm, hdμ₂ω]) ?_
    rw [tdist_comm _ ω μ₂, hdμ₂ω, hdμ₂σ, hdωκ]
    omega
  have hν₁eq : ν₁ = geo (puAmalgam h.le) ω κ (critDist (puAmalgam h.le) - 3) := by
    have hdν₁κ : (puAmalgam h.le).treeGraph.dist ν₁ κ ≤ 3 := by
      have h2 := dist_triangle (puAmalgam h.le) ν₁ μ₂ κ
      rw [dist_eq_one_of_adj _ hν₁μ₂, hdμ₂σ] at h2
      omega
    have h3 := dist_triangle (puAmalgam h.le) ω ν₁ κ
    rw [tdist_comm _ ω ν₁, hdν₁ω, hdωκ] at h3
    refine eq_geo_of_dist _ (by rw [tdist_comm, hdν₁ω]) ?_
    rw [tdist_comm _ ω ν₁, hdν₁ω, hdωκ]
    omega
  have hdl : ∀ i : ℕ, 1 ≤ i → i ≤ critDist (puAmalgam h.le) →
      (puAmalgam h.le).treeGraph.dist l (geo (puAmalgam h.le) ω κ i) = i + 1 := fun i hi hib =>
    dist_geo_of_adj_of_ne _ hi (by rw [hdωκ]; exact hib) hωl hlε
  have hμω : μ ≠ ω := by
    rintro rfl
    have := hμ.1
    rw [SimpleGraph.dist_self] at this
    omega
  have hdμ : ∀ i : ℕ, 1 ≤ i → i ≤ critDist (puAmalgam h.le) →
      (puAmalgam h.le).treeGraph.dist μ (geo (puAmalgam h.le) ω κ i) = i + 2 := by
    intro i hi hib
    have hli := hdl i hi hib
    have hz : (puAmalgam h.le).treeGraph.dist ω (geo (puAmalgam h.le) ω κ i) = i :=
      dist_geo _ (by rw [hdωκ]; exact hib)
    have hgeo : geo (puAmalgam h.le) l (geo (puAmalgam h.le) ω κ i) 1 = ω :=
      (eq_geo_one _ hωl.symm (by rw [hz, hli])).symm
    have hlz : l ≠ geo (puAmalgam h.le) ω κ i := by
      intro heq
      rw [← heq, SimpleGraph.dist_self] at hli
      omega
    rw [dist_eq_add_one_of_adj_of_ne _ hlμ (by rw [hgeo]; exact hμω) hlz, hli]
  have hdμα : (puAmalgam h.le).treeGraph.dist μ α = critDist (puAmalgam h.le) - 2 := by
    rw [hαeq, hdμ _ (by omega) (by omega)]
    omega
  have hdμν₁ : (puAmalgam h.le).treeGraph.dist μ ν₁ = critDist (puAmalgam h.le) - 1 := by
    rw [hν₁eq, hdμ _ (by omega) (by omega)]
    omega
  have hdμμ₂ : (puAmalgam h.le).treeGraph.dist μ μ₂ = critDist (puAmalgam h.le) := by
    rw [hμ₂eq', hdμ _ (by omega) (by omega)]
    omega
  have hdμα' : (puAmalgam h.le).treeGraph.dist μ α' ≤ 6 := by
    have := dist_triangle (puAmalgam h.le) μ ω α'
    rw [tdist_comm _ μ ω, hμ.1, tdist_comm _ ω α', hdα'ω] at this
    exact this
  have hP₀U : P₀ ≤ Uloc h.le L α := inf_le_left.trans (hUU ν₁ hαν₁)
  have hfinα := finite_stab h hα
  have hP₀fin : Finite ↥P₀ := Finite.of_injective _ (Subgroup.inclusion_injective
    (hP₀U.trans ((uloc_le_zm h hfull hα).trans ((zm_le_qv_self _ hα hb0).trans (qv_le_stab _ α)))))
  have hR4eq : R4 = P₀ := Subgroup.eq_of_le_of_card_ge hR4P₀ (hP₀card.trans hR4card)
  by_cases hA : ⁅ZM (puAmalgam h.le) μ₂, ZM (puAmalgam h.le) μ⁆ = ⊥
  ·
    have hZμQμ₂ : ZM (puAmalgam h.le) μ ≤ Qv _ μ₂ := by
      intro z hz
      have hzT : z ∈ Qv (puAmalgam h.le) ν₁ :=
        zm_le_qv_of_dist_lt _ hμM (by rw [hdμν₁]; omega) hz
      refine S46.stab_inf_centralizer_uloc_le_qv h hH.2.2 hμ₂M
        ⟨qv_le_stab_of_adj _ hν₁μ₂ hzT, ?_⟩
      show z ∈ Subgroup.centralizer (Uloc h.le L μ₂ : Set (puAmalgam h.le).Universal)
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      have h1 : ⁅u, z⁆ ∈ ⁅ZM (puAmalgam h.le) μ₂, ZM (puAmalgam h.le) μ⁆ :=
        Subgroup.commutator_mem_commutator (uloc_le_zm h hfull hμ₂M hu) hz
      rw [hA, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
      exact h1
    have hcω := isC1_of_star h hH h431A hs hω
    have hR4eq' : R4 = ⁅Uloc h.le L ω, ZM (puAmalgam h.le) κ⁆ := by
      rw [hR4def, critR, Subgroup.commutator_comm, commutator_zm_eq_uloc h hfull hω hZκs]
    obtain ⟨v, hv, c, hc, hvc⟩ : ∃ v ∈ ZM (puAmalgam h.le) μ, ∃ c ∈ ZM (puAmalgam h.le) κ,
        ⁅v, c⁆ ∉ Bloc h.le L ω := by
      by_contra hall
      push Not at hall
      have hZμB : ¬ ZM (puAmalgam h.le) μ ≤ Bloc h.le L ω := by
        have := hμ.2
        rwa [zv_of_isMVtx _ hμM] at this
      obtain ⟨v₀, hv₀, hv₀B⟩ := Set.not_subset.mp hZμB
      obtain ⟨hUμlZ, -, -, -⟩ := concl433_edge h hfull h42 h431A h431B hH hC hs hμM hlμ.symm
      have := commutator_uloc_le_usup_of_dual h hfull hb2 hω hcω (hk ω hω) hωl hlμ
        (hUωq l hωl) hUμlZ hv₀ hv₀B hZκs (fun c hc => hall v₀ hv₀ c hc)
      exact hlR4 (hR4eq' ▸ this)
    have hdων₃ : (puAmalgam h.le).treeGraph.dist ω ν₃ ≤ critDist (puAmalgam h.le) - 1 := by
      have := dist_triangle (puAmalgam h.le) ω μ₂ ν₃
      rw [tdist_comm _ ω μ₂, hdμ₂ω, dist_eq_one_of_adj _ hμ₂ν₃] at this
      omega
    have hZμT : ZM (puAmalgam h.le) μ ≤ Qv _ ν₃ := hZμQμ₂.trans (qv_le_qv _ h20 hμ₂M hμ₂ν₃)
    have hZωT : ZM (puAmalgam h.le) ω ≤ Qv _ ν₃ := zm_le_qv_of_dist_lt _ hω (by omega)
    obtain ⟨ψκ, -, hψκ⟩ := exists_natural_Uloc h hH.2.2 hσM
    have hTν₃s : Qv (puAmalgam h.le) ν₃ ≤ stab _ κ := qv_le_stab_of_adj _ hν₃κ
    set Y := ZM (puAmalgam h.le) μ ⊔ ZM (puAmalgam h.le) ω with hYdef
    have hYT : Y ≤ Qv (puAmalgam h.le) ν₃ := sup_le hZμT hZωT
    have hYs : Y ≤ stab (puAmalgam h.le) κ := hYT.trans hTν₃s
    have hfinκ : Module.finrank F (commN (natImage ψκ (Qv (puAmalgam h.le) ν₃))) = 2 := by
      have := (concl433_edge h hfull h42 h431A h431B hH hC hs hσM hν₃κ.symm).2.1
      rw [usup_eq_commutator_uloc h hfull hσM hν₃κ.symm, card_commutator_eq hψκ hTν₃s,
        Module.natCard_eq_pow_finrank (K := F), ← Nat.card_eq_fintype_card] at this
      exact Nat.pow_right_injective hq this
    have hR4κ : R4 = ⁅Uloc h.le L κ, ZM (puAmalgam h.le) ω⁆ := by
      rw [hR4def, critR, commutator_zm_eq_uloc h hfull hσM hZωs]
    have hcommY : commN (natImage ψκ Y) = commN (natImage ψκ (Qv (puAmalgam h.le) ν₃)) := by
      have hle := commN_mono (natImage_mono (φ := ψκ) hYT)
      refine Submodule.eq_of_le_of_finrank_eq hle ?_
      rw [hfinκ]
      have hle2 := Submodule.finrank_mono hle
      rw [hfinκ] at hle2
      by_contra hne
      have hωY : commN (natImage ψκ (ZM (puAmalgam h.le) ω)) ≤ commN (natImage ψκ Y) :=
        commN_mono (natImage_mono le_sup_right)
      have hμY : commN (natImage ψκ (ZM (puAmalgam h.le) μ)) ≤ commN (natImage ψκ Y) :=
        commN_mono (natImage_mono le_sup_left)
      have hωne : commN (natImage ψκ (ZM (puAmalgam h.le) ω)) ≠ ⊥ := by
        intro hbot
        apply hR4ne
        rw [hR4κ]
        have hc1 := card_commutator_eq hψκ hZωs
        rw [hbot] at hc1
        have : Nat.card ↥⁅Uloc h.le L κ, ZM (puAmalgam h.le) ω⁆ = 1 := by
          rw [hc1]; simp
        exact Subgroup.eq_bot_of_card_eq _ this
      have hωpos : 0 < Module.finrank F (commN (natImage ψκ (ZM (puAmalgam h.le) ω))) :=
        Nat.pos_of_ne_zero fun h0 => hωne (Submodule.finrank_eq_zero.mp h0)
      have heq : commN (natImage ψκ (ZM (puAmalgam h.le) ω)) = commN (natImage ψκ Y) :=
        Submodule.eq_of_le_of_finrank_le hωY (by omega)
      apply hvc
      have hcv : ⁅c, v⁆ ∈ ⁅Uloc h.le L κ, ZM (puAmalgam h.le) μ⁆ := by
        rw [← commutator_zm_eq_uloc h hfull hσM (hZμT.trans hTν₃s)]
        exact Subgroup.commutator_mem_commutator hc hv
      have hcvU : ⁅c, v⁆ ∈ Uloc h.le L κ := Subgroup.le_normalizer_iff_commutator_le_left.mp
        ((hZμT.trans hTν₃s).trans (stab_le_normalizer_puTrans h.le (S4A.Uq_normal h) κ)) hcv
      have h1 := (mem_commutator_iff_natVec hψκ (hZμT.trans hTν₃s) ⟨_, hcvU⟩).mp hcv
      have h2 : natVec hψκ ⟨_, hcvU⟩ ∈ commN (natImage ψκ (ZM (puAmalgam h.le) ω)) :=
        heq ▸ hμY h1
      have h3 := (mem_commutator_iff_natVec hψκ hZωs ⟨_, hcvU⟩).mpr h2
      rw [← hR4κ] at h3
      have h4 := zm_le_bloc h hb2 hω (hR4Zω h3)
      have e : ⁅v, c⁆ = ⁅c, v⁆⁻¹ := by rw [commutatorElement_inv]
      rw [e]
      exact Subgroup.inv_mem _ h4
    have hW₃Y : Usup (puAmalgam h.le) κ ν₃ ≤ ⁅Uloc h.le L κ, Y⁆ := by
      intro u hu
      rw [usup_eq_commutator_uloc h hfull hσM hν₃κ.symm] at hu
      have huU : u ∈ Uloc h.le L κ := Subgroup.le_normalizer_iff_commutator_le_left.mp
        (hTν₃s.trans (stab_le_normalizer_puTrans h.le (S4A.Uq_normal h) κ)) hu
      have h1 := (mem_commutator_iff_natVec hψκ hTν₃s ⟨u, huU⟩).mp hu
      rw [← hcommY] at h1
      exact (mem_commutator_iff_natVec hψκ hYs ⟨u, huU⟩).mpr h1
    have hYV : Y ≤ Vv (puAmalgam h.le) ω := sup_le hZμV (zm_le_vv h hω)
    have hUκs : Uloc h.le L κ ≤ stab (puAmalgam h.le) ω := (uloc_le_zm h hfull hσM).trans hZκs
    have hUκYV : ⁅Uloc h.le L κ, Y⁆ ≤ Vv (puAmalgam h.le) ω := by
      rw [Subgroup.commutator_comm]
      exact (Subgroup.commutator_mono hYV le_rfl).trans
        (Subgroup.le_normalizer_iff_commutator_le_left.mp (hUκs.trans (stab_le_normalizer_vv h ω)))
    have hVωQ : Vv (puAmalgam h.le) ω ≤ Qv _ α' :=
      vv_le_qv_of_dist h hω (by rw [tdist_comm, hdα'ω]; omega)
    have hW₃Q : Usup (puAmalgam h.le) μ₂ ν₃ ≤ Qv _ α' :=
      hUeqκ ▸ (hW₃Y.trans hUκYV).trans hVωQ
    have hZ'cQ := zm_le_centralizer_qv _ h20 hα'
    have hW₃B : Usup (puAmalgam h.le) μ₂ ν₃ ≤ Bloc h.le L α := by
      intro v hv
      by_contra hvB
      refine hperp v (uloc_le_zm h hfull hμ₂M (hUsμ₂ hv)) hvB fun c hc => ?_
      have : ⁅v, c⁆ = 1 := by
        rw [commutatorElement_eq_one_iff_mul_comm]
        exact Subgroup.mem_centralizer_iff.mp (hZ'cQ hc) v (hW₃Q hv)
      rw [this]
      exact Subgroup.one_mem _
    have hW₃X : Usup (puAmalgam h.le) μ₂ ν₃ ≤ Usup (puAmalgam h.le) α ν₁ :=
      hS2 ▸ le_inf hUsμ₂ hW₃B
    have hfinX : Finite ↥(Usup (puAmalgam h.le) α ν₁) := Finite.of_injective _
      (Subgroup.inclusion_injective ((hUU ν₁ hαν₁).trans ((uloc_le_zm h hfull hα).trans
        ((zm_le_qv_self _ hα hb0).trans (qv_le_stab _ α)))))
    have hW₃eq : Usup (puAmalgam h.le) μ₂ ν₃ = Usup (puAmalgam h.le) α ν₁ :=
      Subgroup.eq_of_le_of_card_ge hW₃X (by
        rw [(concl433_edge h hfull h42 h431A h431B hH hC hs hμ₂M hμ₂ν₃).2.1, hUαν₁q])
    apply hneW
    refine Submodule.eq_of_le_of_finrank_eq ?_ (by rw [hfinrk ν₁ hαν₁, hfinrk β hαβ])
    intro x hx
    obtain ⟨u, rfl⟩ := natVec_surjective hψ x
    have hu : (u : (puAmalgam h.le).Universal) ∈ Usup (puAmalgam h.le) α ν₁ := by
      rw [usup_eq_commutator_uloc h hfull hα hαν₁]
      exact (mem_commutator_iff_natVec hψ hTν₁s u).mpr hx
    have huQ : (u : (puAmalgam h.le).Universal) ∈ Qv (puAmalgam h.le) α' := hW₃Q (hW₃eq ▸ hu)
    have huC : (u : (puAmalgam h.le).Universal) ∈
        Subgroup.centralizer (ZM (puAmalgam h.le) α' : Set (puAmalgam h.le).Universal) :=
      Subgroup.le_centralizer_iff.mp hZ'cQ huQ
    rw [← hfixZ']
    exact (mem_centralizer_iff_natVec hψ hZ'αs u).mp huC
  ·
    have hZμQ : ZM (puAmalgam h.le) μ₂ ≤ Qv _ μ → False := fun hle => hA
      ((Subgroup.commutator_eq_bot_iff_le_centralizer).mpr
        (hle.trans (Subgroup.le_centralizer_iff.mp (zm_le_centralizer_qv _ h20 hμM))))
    have hcritA : IsCritical (puAmalgam h.le) μ₂ μ :=
      ⟨hμ₂M, by rw [tdist_comm, hdμμ₂], hZμQ⟩
    have hZμ₂sμ : ZM (puAmalgam h.le) μ₂ ≤ stab _ μ := zm_le_stab_right _ h20 hb0 hC hcritA
    set Rμ := ⁅ZM (puAmalgam h.le) μ₂, ZM (puAmalgam h.le) μ⁆ with hRμdef
    have hRμZ : Rμ ≤ ZM (puAmalgam h.le) μ := by
      rw [hRμdef, Subgroup.commutator_comm]
      exact Subgroup.le_normalizer_iff_commutator_le_left.mp
        (hZμ₂sμ.trans (stab_le_normalizer_zm _ μ))
    have hZμcZα' : ZM (puAmalgam h.le) μ ≤
        Subgroup.centralizer (ZM (puAmalgam h.le) α' : Set (puAmalgam h.le).Universal) :=
      zm_le_centralizer_zm h hμM hα' (by omega)
    have hZμQα : ZM (puAmalgam h.le) μ ≤ Qv _ α :=
      zm_le_qv_of_dist_lt _ hμM (by rw [hdμα]; omega)
    obtain ⟨hcommμ₂, -⟩ := commutator_zm_qv_eq_usup_of_dual h hfull hH hC h42 h431A h431B hb hs
      hk hCH hα hαν₁ hν₁μ₂ hμ₂
    have hRμX : Rμ ≤ Usup (puAmalgam h.le) α ν₁ := by
      rw [hRμdef, ← hcommμ₂]
      exact Subgroup.commutator_mono le_rfl hZμQα
    have hRμP₀ : Rμ ≤ P₀ := le_inf hRμX fun v hv => hZμcZα' (hRμZ hv)
    have hRμcard : Fintype.card F ≤ Nat.card ↥Rμ := by
      have e : Rμ = ⁅Uloc h.le L μ, ZM (puAmalgam h.le) μ₂⁆ := by
        rw [hRμdef, Subgroup.commutator_comm, commutator_zm_eq_uloc h hfull hμM hZμ₂sμ]
      rw [e]
      exact le_card_commutator_uloc_of_not_le h hH.2.2 hμM hZμ₂sμ hZμQ
    have hRμeq : Rμ = P₀ := Subgroup.eq_of_le_of_card_ge hRμP₀ (hP₀card.trans hRμcard)
    have hZμ₂Qω : ZM (puAmalgam h.le) μ₂ ≤ Qv _ ω :=
      zm_le_qv_of_dist_lt _ hμ₂M (by rw [hdμ₂ω]; omega)
    obtain ⟨hcommμ, -⟩ := commutator_zm_qv_eq_usup_of_dual h hfull hH hC h42 h431A h431B hb hs
      hk hCH hω hωl hlμ hμ
    have hRμl : Rμ ≤ Usup (puAmalgam h.le) ω l := by
      rw [hRμdef, Subgroup.commutator_comm, ← hcommμ]
      exact Subgroup.commutator_mono le_rfl hZμ₂Qω
    apply hlR4
    rw [hR4eq, ← hRμeq]
    exact hRμl

end Six

end CFSG.Quasithin.MS93.S4A
