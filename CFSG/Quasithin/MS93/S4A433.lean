module

public import CFSG.Quasithin.MS93.S4A431D

public section

namespace CFSG.Quasithin.MS93.S4A

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

section Lin

variable {F : Type} [Field F]

theorem card_le_card_commN_of_finrank_fixN [Finite F] {S : Subgroup (SL3 F)}
    (hfix : Module.finrank F (fixN S) = 2) : Nat.card S ≤ Nat.card (commN S) := by
  obtain ⟨u, hu⟩ : ∃ u : Fin 3 → F, u ∉ fixN S := by
    by_contra hcon
    push Not at hcon
    have htop : fixN S = ⊤ := eq_top_iff.mpr fun x _ => hcon x
    rw [htop, finrank_top, Module.finrank_fin_fun] at hfix
    omega
  have hu0 : u ≠ 0 := fun h0 => hu (h0 ▸ (fixN S).zero_mem)
  have htop : fixN S ⊔ Submodule.span F {u} = ⊤ := by
    have hinf : fixN S ⊓ Submodule.span F {u} = ⊥ := by
      rw [eq_bot_iff]
      rintro x ⟨hx1, hx2⟩
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx2
      by_cases hc : c = 0
      · simp [hc]
      · exact absurd (by simpa [hc] using (fixN S).smul_mem c⁻¹ hx1) hu
    have hd := Submodule.finrank_sup_add_finrank_inf_eq (fixN S) (Submodule.span F {u})
    rw [hinf, finrank_bot, add_zero, finrank_span_singleton hu0, hfix] at hd
    exact Submodule.eq_top_of_finrank_eq (by rw [hd, Module.finrank_fin_fun])
  refine Nat.card_le_card_of_injective
    (fun g : ↥S => (⟨((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ u - u,
      sub_mem_commN g.2 u⟩ : ↥(commN S))) ?_
  intro g g' hgg'
  have he : ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ u =
      ((g' : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ u := by
    have := congrArg Subtype.val hgg'
    simpa using this
  have hk : ∀ v, (((g⁻¹ * g' : ↥S) : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v = v := by
    intro v
    have hv : v ∈ fixN S ⊔ Submodule.span F {u} := htop ▸ Submodule.mem_top
    obtain ⟨w, hw, y, hy, rfl⟩ := Submodule.mem_sup.mp hv
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
    have hwk : (((g⁻¹ * g' : ↥S) : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ w = w :=
      hw _ (g⁻¹ * g').2
    have huk : (((g⁻¹ * g' : ↥S) : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ u = u := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, Matrix.SpecialLinearGroup.coe_mul,
        ← Matrix.mulVec_mulVec, ← he, Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul,
        inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, hwk, huk]
  have h1 : g⁻¹ * g' = 1 := Subtype.ext (eq_one_of_mulVec_eq_self hk)
  rw [← mul_left_cancel_iff (a := g⁻¹), h1, inv_mul_cancel]

end Lin

section Edge

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
  (hfull : IsSL3Full M T L)
include h hfull

theorem usup_le_bloc_of (hb : 2 < critDist (puAmalgam h.le)) {α β : Vtx (puAmalgam h.le)}
    (hα : IsMVtx _ α) (hαβ : (puAmalgam h.le).treeGraph.Adj α β) {q : ℕ}
    (hc : IsC1 h.le L q α (Vv (puAmalgam h.le) α) (ZM (puAmalgam h.le) α))
    (hvii : ∀ δ ∈ nablaSet h.le L α, ⁅ZM (puAmalgam h.le) δ, Qv (puAmalgam h.le) α⁆ =
      Usup (puAmalgam h.le) δ (geo (puAmalgam h.le) α δ 1))
    {δ : Vtx (puAmalgam h.le)} (hβδ : (puAmalgam h.le).treeGraph.Adj β δ) :
    Usup (puAmalgam h.le) δ β ≤ Bloc h.le L α := by
  have hδM : IsMVtx (puAmalgam h.le) δ := by
    have h1 := isMVtx_iff_of_adj _ hαβ
    have h2 := isMVtx_iff_of_adj _ hβδ
    tauto
  have hUZ : Usup (puAmalgam h.le) δ β ≤ Zv _ δ := by
    rw [Usup, zv_of_isMVtx _ hδM]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp
      ((qv_le_stab_of_adj _ hβδ).trans (stab_le_normalizer_zm _ δ))
  by_cases hδα : δ = α
  · subst hδα
    exact hUZ.trans (by rw [zv_of_isMVtx _ hα]; exact zm_le_bloc h hb hα)
  have hd : (puAmalgam h.le).treeGraph.dist α δ = 2 :=
    dist_eq_two_of_adj_adj _ hαβ hβδ (Ne.symm hδα)
  by_cases hn : δ ∈ nablaSet h.le L α
  · have hgeo : geo (puAmalgam h.le) α δ 1 = β :=
      (eq_geo_one _ hαβ (by rw [dist_eq_one_of_adj _ hβδ, hd])).symm
    rw [← hgeo, ← hvii δ hn]
    refine (Subgroup.commutator_mono ?_ le_rfl).trans (isC1_bloc h hfull hb hα hc).1
    rw [← zv_of_isMVtx _ hδM]
    exact zv_le_vv h hd.le
  · have hZB : Zv (puAmalgam h.le) δ ≤ Bloc h.le L α := by
      by_contra hcon
      exact hn ⟨hd, hcon⟩
    exact hUZ.trans hZB

omit hfull in
theorem card_usup_of_star (hC : CentHyp (puAmalgam h.le)) {F : Type} [Field F] [Fintype F]
    {φ : ↥M →* ↥(StatedSL 3 F)} (hφ : IsSL3FullVia M T L φ) (hb : 2 < critDist (puAmalgam h.le))
    {α₀ α₀' : Vtx (puAmalgam h.le)} (hs : Star (puAmalgam h.le) α₀ α₀')
    {α β : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α) (hαβ : (puAmalgam h.le).treeGraph.Adj α β) :
    Nat.card ↥(Usup (puAmalgam h.le) α β) = Nat.card F ^ 2 := by
  obtain ⟨hR0U, hR0q, -⟩ := concl431_i_ii h hC hφ hb hs
  have hc' := ms22_iii _ h.hyp20 h.critDist_pos hC hs.1
  obtain ⟨g, hg1, hg2⟩ := exists_smul_edge_of_isMVtx _ hc'.1
    (adj_geo_one_of_isCritical _ h.critDist_pos hc') hα hαβ
  rw [← hg1, ← hg2, usup_smul, Subgroup.card_map_of_injective (MulAut.conj g).injective, ← hR0U,
    hR0q]

theorem usup_le_zh_of_star (h42 : S42) (hmin : PUMin M T L) (hC : CentHyp (puAmalgam h.le))
    {F : Type} [Field F] [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)} (hφ : IsSL3FullVia M T L φ)
    (hb : 2 < critDist (puAmalgam h.le)) {α₀ α₀' : Vtx (puAmalgam h.le)}
    (hs : Star (puAmalgam h.le) α₀ α₀') {α β : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α)
    (hαβ : (puAmalgam h.le).treeGraph.Adj α β)
    (hc : IsC1 h.le L (Fintype.card F) α (Vv (puAmalgam h.le) α) (ZM (puAmalgam h.le) α))
    (hvii : ∀ δ ∈ nablaSet h.le L α, ⁅ZM (puAmalgam h.le) δ, Qv (puAmalgam h.le) α⁆ =
      Usup (puAmalgam h.le) δ (geo (puAmalgam h.le) α δ 1)) :
    Usup (puAmalgam h.le) α β ≤ ZH (puAmalgam h.le) β := by
  refine (h42 G M T L h hmin hb F inferInstance inferInstance φ hφ α β hα hαβ).1
    (fun δ hδ => usup_le_bloc_of h hfull hb hα hαβ hc hvii hδ) ?_
  rw [card_usup_of_star h hC hφ hb hs hα hαβ, Nat.card_eq_fintype_card]

omit hfull in
theorem commutator_vv_qv_le_zm (hb : 2 < critDist (puAmalgam h.le))
    (hU : ∀ δ ρ : Vtx (puAmalgam h.le), IsMVtx _ δ → (puAmalgam h.le).treeGraph.Adj δ ρ →
      Usup (puAmalgam h.le) δ ρ ≤ ZH (puAmalgam h.le) ρ)
    {α : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α) :
    ⁅Vv (puAmalgam h.le) α, Qv (puAmalgam h.le) α⁆ ≤ ZM (puAmalgam h.le) α := by
  have h20 := h.hyp20
  have hZn := stab_le_normalizer_zm (puAmalgam h.le) α
  have hQZ : ⁅ZM (puAmalgam h.le) α, Qv (puAmalgam h.le) α⁆ ≤ ZM _ α :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp ((qv_le_stab _ α).trans hZn)
  have hVs : Vv (puAmalgam h.le) α ≤ stab _ α := (vv_le_qv h hb hα).trans (qv_le_stab _ α)
  have hgen : ∀ ρ : {ρ : Vtx (puAmalgam h.le) // (puAmalgam h.le).treeGraph.dist α ρ ≤ 2},
      ⁅Zv (puAmalgam h.le) (ρ : Vtx (puAmalgam h.le)), Qv (puAmalgam h.le) α⁆ ≤ ZM _ α := by
    rintro ⟨ρ, hρ⟩
    rcases isMVtx_of_dist_le_two h hα hρ with hρM | hadj
    · by_cases hρα : ρ = α
      · subst hρα
        rw [zv_of_isMVtx _ hα]
        exact hQZ
      ·
        have hd : (puAmalgam h.le).treeGraph.dist α ρ = 2 := by
          have hne : (puAmalgam h.le).treeGraph.dist α ρ ≠ 0 :=
            fun h0 => hρα ((dist_eq_zero_iff _).mp h0).symm
          have hev : Even ((puAmalgam h.le).treeGraph.dist α ρ) := by
            rw [even_dist_iff]
            tauto
          obtain ⟨k, hk⟩ := hev
          omega
        have hαβ : (puAmalgam h.le).treeGraph.Adj α (geo (puAmalgam h.le) α ρ 1) :=
          adj_geo_one _ (by omega)
        have hβρ : (puAmalgam h.le).treeGraph.Adj (geo (puAmalgam h.le) α ρ 1) ρ := by
          have := adj_geo (puAmalgam h.le) (u := α) (w := ρ) (i := 1) (by omega)
          rwa [show geo (puAmalgam h.le) α ρ (1 + 1) = ρ from geo_of_le _ (by omega)] at this
        have h1 : ⁅Zv (puAmalgam h.le) ρ, Qv (puAmalgam h.le) α⁆ ≤
            Usup (puAmalgam h.le) ρ (geo (puAmalgam h.le) α ρ 1) :=
          Subgroup.commutator_mono le_rfl (qv_le_qv _ h20 hα hαβ)
        exact h1.trans ((hU ρ _ hρM hβρ.symm).trans (zh_le_zm _ hαβ))
    · have hβH : ¬ IsMVtx (puAmalgam h.le) ρ := by
        rw [← isMVtx_iff_of_adj _ hadj]
        exact hα
      rw [zv_of_not_isMVtx _ hβH]
      exact (Subgroup.commutator_mono (zh_le_zm _ hadj) le_rfl).trans hQZ
  have hVeq : Vv (puAmalgam h.le) α = ⨆ ρ : {ρ : Vtx (puAmalgam h.le) //
      (puAmalgam h.le).treeGraph.dist α ρ ≤ 2}, Zv (puAmalgam h.le) (ρ : Vtx (puAmalgam h.le)) :=
    iSup_subtype'
  rw [hVeq]
  exact commutator_iSup_le_of hgen (hVeq ▸ hVs.trans hZn)

theorem zh_inf_uloc {α β : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α)
    (hαβ : (puAmalgam h.le).treeGraph.Adj α β) :
    ZH (puAmalgam h.le) β ⊓ Uloc h.le L α =
      Uloc h.le L α ⊓ Subgroup.centralizer (Qv (puAmalgam h.le) β : Set _) := by
  have hb0 := h.critDist_pos
  apply le_antisymm
  · rintro x ⟨hxZ, hxU⟩
    refine ⟨hxU, ?_⟩
    exact zh_le_centralizer _ β hxZ
  · rintro x ⟨hxU, hxc⟩
    refine ⟨?_, hxU⟩
    have hxZ := uloc_le_zm h hfull hα hxU
    have hxQ : x ∈ Qv _ β :=
      qv_le_qv _ h.hyp20 hα hαβ (zm_le_qv_self _ hα hb0 hxZ)
    have hx2 : x ^ 2 = 1 := (isElemAbelian_zm _ h.hyp20 hb0 hα).2 x hxZ
    exact Subgroup.subset_closure ⟨⟨hxQ, hxc⟩, hx2⟩

theorem relIndex_zh_zm {F : Type} [Field F] [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)}
    (hφ : IsSL3FullVia M T L φ) {α β : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α)
    (hαβ : (puAmalgam h.le).treeGraph.Adj α β)
    (hUZ : Usup (puAmalgam h.le) α β ≤ ZH (puAmalgam h.le) β)
    (hUq : Nat.card ↥(Usup (puAmalgam h.le) α β) = Nat.card F ^ 2) :
    (ZH (puAmalgam h.le) β).relIndex (ZM (puAmalgam h.le) α) = Nat.card F := by
  have h20 := h.hyp20
  have hb0 := h.critDist_pos
  have hq : 2 ≤ Nat.card F := Finite.one_lt_card
  have hβH : ¬ IsMVtx (puAmalgam h.le) β := by
    rw [← isMVtx_iff_of_adj _ hαβ]
    exact hα
  have hQs : Qv (puAmalgam h.le) β ≤ stab _ α := qv_le_stab_of_adj _ hαβ.symm
  obtain ⟨ψ, -, hψ⟩ := exists_natural_Uloc h hφ hα
  have hZQ : ZM (puAmalgam h.le) α ≤ Qv _ β :=
    (zm_le_qv_self _ hα hb0).trans (qv_le_qv _ h20 hα hαβ)
  have hfQ := finite_qv _ h20 hβH
  have hfU : Finite ↥(Uloc h.le L α) :=
    Finite.of_injective _ (Subgroup.inclusion_injective ((uloc_le_zm h hfull hα).trans hZQ))
  have hfW : Finite ↥(Zloc h.le L α) :=
    Finite.of_injective _ (Subgroup.inclusion_injective ((zloc_le_zm h hfull hα).trans hZQ))
  rw [zm_eq_uloc_sup_zloc h hfull hα, relIndex_sup_eq_of_le (zloc_le_zh h hfull hα hαβ)
    ((zloc_le_centralizer_stab h hfull hα).trans (Subgroup.centralizer_le
      ((uloc_le_zm h hfull hα).trans ((zm_le_qv_self _ hα hb0).trans (qv_le_stab _ α)))))
    (uloc_inf_zloc h hfull α)]
  have hW : commN (natImage ψ (Qv (puAmalgam h.le) β)) ≤ fixN (natImage ψ (Qv _ β)) := by
    intro x hx
    obtain ⟨u, rfl⟩ := natVec_surjective hψ x
    have hu : (u : (puAmalgam h.le).Universal) ∈ ⁅Uloc h.le L α, Qv (puAmalgam h.le) β⁆ :=
      (mem_commutator_iff_natVec hψ hQs u).mpr hx
    rw [← usup_eq_commutator_uloc h hfull hα hαβ] at hu
    have huC : (u : (puAmalgam h.le).Universal) ∈
        Subgroup.centralizer (Qv (puAmalgam h.le) β : Set _) :=
      ((zh_inf_uloc h hfull hα hαβ).le ⟨hUZ hu, u.2⟩).2
    exact (mem_centralizer_iff_natVec hψ hQs u).mp huC
  have hC2 : Module.finrank F (commN (natImage ψ (Qv (puAmalgam h.le) β))) = 2 := by
    have := hUq
    rw [usup_eq_commutator_uloc h hfull hα hαβ, card_commutator_eq hψ hQs,
      Module.natCard_eq_pow_finrank (K := F)] at this
    exact Nat.pow_right_injective hq this
  have hF2 : Module.finrank F (fixN (natImage ψ (Qv (puAmalgam h.le) β))) = 2 := by
    have h1 := Submodule.finrank_mono hW
    have h3 : Module.finrank F (fixN (natImage ψ (Qv (puAmalgam h.le) β))) ≠ 3 := by
      intro h3
      have htop : fixN (natImage ψ (Qv (puAmalgam h.le) β)) = ⊤ :=
        Submodule.eq_top_of_finrank_eq (by rw [h3, Module.finrank_fin_fun])
      have hbot : commN (natImage ψ (Qv (puAmalgam h.le) β)) = ⊥ := by
        rw [eq_bot_iff]
        refine Submodule.span_le.mpr ?_
        rintro _ ⟨g, hg, x, rfl⟩
        have : x ∈ fixN (natImage ψ (Qv (puAmalgam h.le) β)) := htop ▸ Submodule.mem_top
        rw [mem_fixN] at this
        rw [this g hg, sub_self]
        exact Submodule.zero_mem _
      rw [hbot, finrank_bot] at hC2
      omega
    have h4 := Submodule.finrank_le (fixN (natImage ψ (Qv (puAmalgam h.le) β)))
    rw [Module.finrank_fin_fun] at h4
    omega
  have hcard : Nat.card ↥(ZH (puAmalgam h.le) β ⊓ Uloc h.le L α) = Nat.card F ^ 2 := by
    rw [zh_inf_uloc h hfull hα hαβ, card_inf_centralizer_eq hψ hQs,
      Module.natCard_eq_pow_finrank (K := F), hF2]
  have hmul := relIndex_mul_card_inf (ZH (puAmalgam h.le) β) (Uloc h.le L α)
  rw [hcard, card_eq_of_natural hψ] at hmul
  have hpos : 0 < Nat.card F ^ 2 := by positivity
  exact Nat.eq_of_mul_eq_mul_right hpos (by rw [hmul]; ring)

theorem exists_mem_toSL3_ne_one (hb : 2 < critDist (puAmalgam h.le))
    {α β : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α) (hαβ : (puAmalgam h.le).treeGraph.Adj α β)
    {q : ℕ} (hc : IsC1 h.le L q α (Vv (puAmalgam h.le) α) (ZM (puAmalgam h.le) α))
    {F' : Type} [Field F'] {ψ' : ↥(stab (puAmalgam h.le) α) →* ↥(StatedSL 3 F')}
    (hnat : IsSumOfNaturalModulesVia (stab (puAmalgam h.le) α)
      (⁅Vv (puAmalgam h.le) α, stab (puAmalgam h.le) α⁆ ⊔ ZM (puAmalgam h.le) α)
      (⁅Vv (puAmalgam h.le) α, Qv (puAmalgam h.le) α⁆ ⊔ ZM (puAmalgam h.le) α) ψ' false 1)
    (hPiB : (⁅Vv (puAmalgam h.le) α, stab (puAmalgam h.le) α⁆ ⊔ ZM (puAmalgam h.le) α) ⊓
      Bloc h.le L α = ⁅Vv (puAmalgam h.le) α, Qv (puAmalgam h.le) α⁆ ⊔ ZM (puAmalgam h.le) α)
    (hPB : (⁅Vv (puAmalgam h.le) α, stab (puAmalgam h.le) α⁆ ⊔ ZM (puAmalgam h.le) α) ⊔
      Bloc h.le L α = Vv (puAmalgam h.le) α)
    {X : Subgroup (puAmalgam h.le).Universal} (hXβ : X ≤ Qv _ β) (hXα : ¬ X ≤ Qv _ α) :
    ∃ x, ∃ hx : x ∈ X, toSL3 ψ' ⟨x, hXβ.trans (qv_le_stab_of_adj _ hαβ.symm) hx⟩ ≠ 1 := by
  have hXs : X ≤ stab (puAmalgam h.le) α := hXβ.trans (qv_le_stab_of_adj _ hαβ.symm)
  have hVQ := vv_le_qv h hb hα
  have hVn := stab_le_normalizer_vv h α
  have hZn := stab_le_normalizer_zm (puAmalgam h.le) α
  have hPn : stab (puAmalgam h.le) α ≤ Subgroup.normalizer
      ((⁅Vv (puAmalgam h.le) α, stab (puAmalgam h.le) α⁆ ⊔ ZM (puAmalgam h.le) α :
        Subgroup _) : Set _) :=
    (le_inf (le_normalizer_commutator hVn Subgroup.le_normalizer) hZn).trans
      (Subgroup.inf_normalizer_le_normalizer_sup _ _)
  have hKB : ⁅Vv (puAmalgam h.le) α, Qv (puAmalgam h.le) α⁆ ⊔ ZM (puAmalgam h.le) α ≤
      Bloc h.le L α := hPiB ▸ inf_le_right
  have hBn : stab (puAmalgam h.le) α ≤
      Subgroup.normalizer (Bloc h.le L α : Set (puAmalgam h.le).Universal) :=
    stab_le_normalizer_of_smul (F := fun δ => Bloc h.le L δ) _ (fun g δ => bloc_smul h g δ) α
  have hBs : Bloc h.le L α ≤ stab _ α := (bloc_le_vv h α).trans (hVQ.trans (qv_le_stab _ α))
  have hPs : ⁅Vv (puAmalgam h.le) α, stab (puAmalgam h.le) α⁆ ⊔ ZM (puAmalgam h.le) α ≤
      stab _ α :=
    (sup_le (Subgroup.le_normalizer_iff_commutator_le_left.mp hVn) (zm_le_vv h hα)).trans
      (hVQ.trans (qv_le_stab _ α))
  by_contra hcon
  push Not at hcon
  apply not_commutator_vv_ltil_le_bloc h hfull hb hα hc
  refine commutator_vv_ltil_le_of h hfull hα hαβ hXβ hXα hBn ?_
  have hPX : ⁅⁅Vv (puAmalgam h.le) α, stab (puAmalgam h.le) α⁆ ⊔ ZM (puAmalgam h.le) α, X⁆ ≤
      Bloc h.le L α := by
    rw [Subgroup.commutator_le]
    intro p hp x hx
    have h1 := hcon x hx
    have hsp : x * p * x⁻¹ ∈ ⁅Vv (puAmalgam h.le) α, stab (puAmalgam h.le) α⁆ ⊔
        ZM (puAmalgam h.le) α := (Subgroup.mem_normalizer_iff.mp (hPn (hXs hx)) _).mp hp
    have heq := secVec_conj hnat ⟨x, hXs hx⟩ ⟨p, hp⟩ ⟨_, hsp⟩ rfl
    rw [h1, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec] at heq
    have hdiff : secVec hnat (⟨_, hsp⟩ * (⟨p, hp⟩ : ↥(⁅Vv (puAmalgam h.le) α,
        stab (puAmalgam h.le) α⁆ ⊔ ZM (puAmalgam h.le) α))⁻¹) = 0 := by
      rw [secVec_mul, secVec_inv, heq, add_neg_cancel]
    have hK := (secVec_eq_zero_iff hnat _).mp hdiff
    have hrw : ⁅p, x⁆ = (x * p * x⁻¹ * p⁻¹)⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [hrw]
    exact hKB (Subgroup.inv_mem _ (by simpa using hK))
  calc ⁅Vv (puAmalgam h.le) α, X⁆ = ⁅(⁅Vv (puAmalgam h.le) α, stab (puAmalgam h.le) α⁆ ⊔
        ZM (puAmalgam h.le) α) ⊔ Bloc h.le L α, X⁆ := by rw [hPB]
    _ ≤ Bloc h.le L α := S4A.commutator_sup_le_of hPX
        (Subgroup.le_normalizer_iff_commutator_le_left.mp (hXs.trans hBn))
        (hPs.trans hBn) (hBs.trans hBn)

theorem le_relIndex_vv_of_isC1_bloc (hb : 2 < critDist (puAmalgam h.le))
    {α β : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α) (hαβ : (puAmalgam h.le).treeGraph.Adj α β)
    {q : ℕ} (hc : IsC1 h.le L q α (Vv (puAmalgam h.le) α) (ZM (puAmalgam h.le) α))
    {X : Subgroup (puAmalgam h.le).Universal} (hXβ : X ≤ Qv _ β) (hXα : ¬ X ≤ Qv _ α)
    {D : Subgroup (puAmalgam h.le).Universal} (hDX : ⁅D, X⁆ ≤ Bloc h.le L α) :
    q ≤ D.relIndex (Vv (puAmalgam h.le) α) := by
  have h20 := h.hyp20
  have hβH : ¬ IsMVtx (puAmalgam h.le) β := by
    rw [← isMVtx_iff_of_adj _ hαβ]
    exact hα
  obtain ⟨F', _, _, ψ', hcard', -, hnat, hPiB, hPB, -, -⟩ := isC1_normal h hfull hb hα hc
  obtain ⟨x₀, hx₀, hg₀⟩ := exists_mem_toSL3_ne_one h hfull hb hα hαβ hc hnat hPiB hPB hXβ hXα
  have hXs : X ≤ stab (puAmalgam h.le) α := hXβ.trans (qv_le_stab_of_adj _ hαβ.symm)
  have hVn := stab_le_normalizer_vv h α
  have hZn := stab_le_normalizer_zm (puAmalgam h.le) α
  have hPn : stab (puAmalgam h.le) α ≤ Subgroup.normalizer
      ((⁅Vv (puAmalgam h.le) α, stab (puAmalgam h.le) α⁆ ⊔ ZM (puAmalgam h.le) α :
        Subgroup _) : Set _) :=
    (le_inf (le_normalizer_commutator hVn Subgroup.le_normalizer) hZn).trans
      (Subgroup.inf_normalizer_le_normalizer_sup _ _)
  have hPV : ⁅Vv (puAmalgam h.le) α, stab (puAmalgam h.le) α⁆ ⊔ ZM (puAmalgam h.le) α ≤
      Vv _ α := sup_le (Subgroup.le_normalizer_iff_commutator_le_left.mp hVn) (zm_le_vv h hα)
  have hVfin : Finite ↥(Vv (puAmalgam h.le) α) := by
    have := finite_qv _ h20 hβH
    exact Finite.of_injective _ (Subgroup.inclusion_injective
      ((vv_le_qv h hb hα).trans (qv_le_qv _ h20 hα hαβ)))
  set g₀ := toSL3 ψ' ⟨x₀, hXs hx₀⟩ with hg₀def
  let θ : (Fin 3 → F') →+ (Fin 3 → F') :=
    ((Matrix.toLin' ((g₀ : SL3 F') : Matrix (Fin 3) (Fin 3) F') - LinearMap.id :
      (Fin 3 → F') →ₗ[F'] (Fin 3 → F'))).toAddMonoidHom
  let f : ↥(⁅Vv (puAmalgam h.le) α, stab (puAmalgam h.le) α⁆ ⊔ ZM (puAmalgam h.le) α) →*
      Multiplicative (Fin 3 → F') := (AddMonoidHom.toMultiplicative θ).comp (secHom hnat)
  have hf : ∀ p, f p = Multiplicative.ofAdd
      (((g₀ : SL3 F') : Matrix (Fin 3) (Fin 3) F') *ᵥ secVec hnat p - secVec hnat p) := by
    intro p
    rfl
  have hDker : D.subgroupOf (⁅Vv (puAmalgam h.le) α, stab (puAmalgam h.le) α⁆ ⊔
      ZM (puAmalgam h.le) α) ≤ f.ker := by
    intro p hp
    rw [Subgroup.mem_subgroupOf] at hp
    rw [MonoidHom.mem_ker, hf, ofAdd_eq_one, sub_eq_zero]
    have hsp : x₀ * p * x₀⁻¹ ∈ ⁅Vv (puAmalgam h.le) α, stab (puAmalgam h.le) α⁆ ⊔
        ZM (puAmalgam h.le) α := (Subgroup.mem_normalizer_iff.mp (hPn (hXs hx₀)) _).mp p.2
    have hcomm : ⁅(p : (puAmalgam h.le).Universal), x₀⁆ ∈ Bloc h.le L α :=
      hDX (Subgroup.commutator_mem_commutator hp hx₀)
    have hK : (p : (puAmalgam h.le).Universal) * (x₀ * p * x₀⁻¹)⁻¹ ∈
        ⁅Vv (puAmalgam h.le) α, Qv (puAmalgam h.le) α⁆ ⊔ ZM (puAmalgam h.le) α := by
      have e : (p : (puAmalgam h.le).Universal) * (x₀ * p * x₀⁻¹)⁻¹ =
          ⁅(p : (puAmalgam h.le).Universal), x₀⁆ := by
        simp only [commutatorElement_def]
        group
      rw [← hPiB, e]
      refine ⟨?_, hcomm⟩
      rw [← e]
      exact Subgroup.mul_mem _ p.2 (Subgroup.inv_mem _ hsp)
    have h0 := (secVec_eq_zero_iff hnat (p * (⟨_, hsp⟩ : ↥(⁅Vv (puAmalgam h.le) α,
      stab (puAmalgam h.le) α⁆ ⊔ ZM (puAmalgam h.le) α))⁻¹)).mpr hK
    rw [secVec_mul, secVec_inv, secVec_conj hnat ⟨x₀, hXs hx₀⟩ p ⟨_, hsp⟩ rfl,
      add_neg_eq_zero] at h0
    exact h0.symm
  have hrange : Nat.card F' ≤ Nat.card f.range := by
    set W : Submodule F' (Fin 3 → F') :=
      LinearMap.range (Matrix.toLin' ((g₀ : SL3 F') : Matrix (Fin 3) (Fin 3) F') -
        LinearMap.id) with hW
    have hWne : W ≠ ⊥ := by
      intro hbot
      apply hg₀
      refine eq_one_of_mulVec_eq_self fun v => ?_
      have : ((Matrix.toLin' ((g₀ : SL3 F') : Matrix (Fin 3) (Fin 3) F') - LinearMap.id :
          (Fin 3 → F') →ₗ[F'] (Fin 3 → F')) v) ∈ W := ⟨v, rfl⟩
      rw [hbot, Submodule.mem_bot, LinearMap.sub_apply, Matrix.toLin'_apply, LinearMap.id_apply,
        sub_eq_zero] at this
      exact this
    have hmem : ∀ w ∈ W, Multiplicative.ofAdd w ∈ f.range := by
      rintro _ ⟨v, rfl⟩
      obtain ⟨p, hp⟩ := secVec_surjective hnat v
      refine ⟨p, ?_⟩
      rw [hf, hp, LinearMap.sub_apply, Matrix.toLin'_apply, LinearMap.id_apply]
    calc Nat.card F' ≤ Nat.card ↥W := card_le_of_ne_bot hWne
      _ ≤ Nat.card f.range :=
        Nat.card_le_card_of_injective (fun w : ↥W => (⟨_, hmem w w.2⟩ : ↥f.range))
          (fun w w' hww' => Subtype.ext (Multiplicative.ofAdd.injective
            (congrArg (Subtype.val : ↥f.range → Multiplicative (Fin 3 → F')) hww')))
  have hPfin : Finite ↥(⁅Vv (puAmalgam h.le) α, stab (puAmalgam h.le) α⁆ ⊔
      ZM (puAmalgam h.le) α) := Finite.of_injective _ (Subgroup.inclusion_injective hPV)
  have hidx : Nat.card f.range ≤ D.relIndex (⁅Vv (puAmalgam h.le) α,
      stab (puAmalgam h.le) α⁆ ⊔ ZM (puAmalgam h.le) α) := by
    rw [← Subgroup.index_ker]
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
      (Subgroup.index_dvd_of_le hDker)
  have hle : D.relIndex (⁅Vv (puAmalgam h.le) α, stab (puAmalgam h.le) α⁆ ⊔
      ZM (puAmalgam h.le) α) ≤ D.relIndex (Vv (puAmalgam h.le) α) :=
    Subgroup.relIndex_le_of_le_right hPV
      (show (D.subgroupOf (Vv (puAmalgam h.le) α)).index ≠ 0 from Subgroup.index_ne_zero_of_finite)
  rw [← hcard', ← Nat.card_eq_fintype_card]
  exact hrange.trans (hidx.trans hle)

theorem le_relIndex_vv_of_isC1 (hb : 2 < critDist (puAmalgam h.le))
    {α β : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α) (hαβ : (puAmalgam h.le).treeGraph.Adj α β)
    {q : ℕ} (hc : IsC1 h.le L q α (Vv (puAmalgam h.le) α) (ZM (puAmalgam h.le) α))
    {X : Subgroup (puAmalgam h.le).Universal} (hXβ : X ≤ Qv _ β) (hXα : ¬ X ≤ Qv _ α)
    {D : Subgroup (puAmalgam h.le).Universal} (hDX : ⁅D, X⁆ ≤ ZM (puAmalgam h.le) α) :
    q ≤ D.relIndex (Vv (puAmalgam h.le) α) :=
  le_relIndex_vv_of_isC1_bloc h hfull hb hα hαβ hc hXβ hXα (hDX.trans (zm_le_bloc h hb hα))

omit hfull in
theorem le_relIndex_zm_of_isCritical (hC : CentHyp (puAmalgam h.le)) {F : Type} [Field F]
    [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)} (hφ : IsSL3FullVia M T L φ)
    {α α' : Vtx (puAmalgam h.le)} (hc : IsCritical (puAmalgam h.le) α α') :
    Nat.card F ≤ (Qv (puAmalgam h.le) α').relIndex (ZM (puAmalgam h.le) α) := by
  have hc' := ms22_iii _ h.hyp20 h.critDist_pos hC hc
  obtain ⟨ψ, -, hψ⟩ := exists_natural_Uloc h hφ hc.1
  obtain ⟨ψ', -, hψ'⟩ := exists_natural_Uloc h hφ hc'.1
  obtain ⟨-, -, hrel, -, -, hne⟩ := s35_core h hC hφ hc hψ hψ'
  have hf : Module.finrank F (fixN (natImage ψ (ZM (puAmalgam h.le) α'))) ≤ 2 := by
    have h3 := Submodule.finrank_le (fixN (natImage ψ (ZM (puAmalgam h.le) α')))
    rw [Module.finrank_fin_fun] at h3
    by_contra hcon
    have htop : fixN (natImage ψ (ZM (puAmalgam h.le) α')) = ⊤ :=
      Submodule.eq_top_of_finrank_eq (by rw [Module.finrank_fin_fun]; omega)
    apply hne
    rw [eq_bot_iff]
    intro g hg
    rw [Subgroup.mem_bot]
    refine eq_one_of_mulVec_eq_self fun v => ?_
    have : v ∈ fixN (natImage ψ (ZM (puAmalgam h.le) α')) := htop ▸ Submodule.mem_top
    exact this g hg
  rw [hrel]
  calc Nat.card F = Nat.card F ^ 1 := (pow_one _).symm
    _ ≤ _ := Nat.pow_le_pow_right Nat.card_pos (by omega)

theorem sq_le_relIndex_vv_of_star (hC : CentHyp (puAmalgam h.le)) {F : Type} [Field F]
    [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)} (hφ : IsSL3FullVia M T L φ)
    (hb : 2 < critDist (puAmalgam h.le)) {α α' : Vtx (puAmalgam h.le)}
    (hs : Star (puAmalgam h.le) α α')
    (hc : IsC1 h.le L (Fintype.card F) α (Vv (puAmalgam h.le) α) (ZM (puAmalgam h.le) α)) :
    Fintype.card F ^ 2 ≤ (Qv (puAmalgam h.le) α').relIndex (Vv (puAmalgam h.le) α) := by
  have h20 := h.hyp20
  have hb0 := h.critDist_pos
  have hc' := ms22_iii _ h20 hb0 hC hs.1
  have hα := hs.1.1
  have hα' := hc'.1
  have hαβ := adj_geo_one_of_isCritical _ hb0 hs.1
  have hZ'β : ZM (puAmalgam h.le) α' ≤ Qv _ (geo (puAmalgam h.le) α α' 1) :=
    zm_le_qv_geo_one _ h20 hb0 hs.1
  have hα'ε : (puAmalgam h.le).treeGraph.Adj α' (geo (puAmalgam h.le) α' α 1) :=
    adj_geo_one_of_isCritical _ hb0 hc'
  have hεγ : (puAmalgam h.le).treeGraph.Adj (geo (puAmalgam h.le) α' α 1)
      (geo (puAmalgam h.le) α' α 2) := adj_geo _ (i := 1) (by rw [hc'.2.1]; omega)
  have hγ : IsMVtx (puAmalgam h.le) (geo (puAmalgam h.le) α' α 2) := isMVtx_geo_two _ h20 hb0 hc'
  have hεH : ¬ IsMVtx (puAmalgam h.le) (geo (puAmalgam h.le) α' α 1) := by
    rw [← isMVtx_iff_of_adj _ hα'ε]
    exact hα'
  have hVε : Vv (puAmalgam h.le) α ≤ Qv _ (geo (puAmalgam h.le) α' α 1) :=
    hs.2.trans (qv_le_qv _ h20 hγ hεγ.symm)
  have hfε := finite_qv _ h20 hεH
  have hVfin : Finite ↥(Vv (puAmalgam h.le) α) :=
    Finite.of_injective _ (Subgroup.inclusion_injective hVε)
  have hZn := stab_le_normalizer_zm (puAmalgam h.le) α
  have hZ's : ZM (puAmalgam h.le) α' ≤ stab _ α := zm_le_stab_right _ h20 hb0 hC hc'
  have hVs : Vv (puAmalgam h.le) α ≤ stab _ α := (vv_le_qv h hb hα).trans (qv_le_stab _ α)
  have hDX : ⁅Vv (puAmalgam h.le) α ⊓ Qv (puAmalgam h.le) α' ⊔ ZM (puAmalgam h.le) α,
      ZM (puAmalgam h.le) α'⁆ ≤ ZM (puAmalgam h.le) α := by
    refine S4A.commutator_sup_le_of ?_ ?_ ?_ ?_
    · rw [(Subgroup.commutator_eq_bot_iff_le_centralizer).mpr ?_]
      · exact bot_le
      · intro z hz
        rw [Subgroup.mem_centralizer_iff]
        intro x hx
        exact (Subgroup.mem_centralizer_iff.mp
          (zm_le_centralizer_qv _ h20 hα' hx) z hz.2).symm
    · exact Subgroup.le_normalizer_iff_commutator_le_left.mp (hZ's.trans hZn)
    · exact (inf_le_left.trans hVs).trans hZn
    · exact ((zm_le_vv h hα).trans hVs).trans hZn
  have hmod := le_relIndex_vv_of_isC1 h hfull hb hα hαβ hc hZ'β hc'.2.2 hDX
  have hZq := le_relIndex_zm_of_isCritical h hC hφ hs.1
  have hD1 : Qv (puAmalgam h.le) α' ⊓ Vv (puAmalgam h.le) α ≤
      Vv (puAmalgam h.le) α ⊓ Qv (puAmalgam h.le) α' ⊔ ZM (puAmalgam h.le) α :=
    (inf_comm _ _).le.trans le_sup_left
  have hD2 : Vv (puAmalgam h.le) α ⊓ Qv (puAmalgam h.le) α' ⊔ ZM (puAmalgam h.le) α ≤
      Vv (puAmalgam h.le) α := sup_le inf_le_left (zm_le_vv h hα)
  have hDfin : Finite ↥(Vv (puAmalgam h.le) α ⊓ Qv (puAmalgam h.le) α' ⊔
      ZM (puAmalgam h.le) α) := Finite.of_injective _ (Subgroup.inclusion_injective hD2)
  have htower := Subgroup.relIndex_mul_relIndex _ _ _ hD1 hD2
  rw [Subgroup.inf_relIndex_right] at htower
  have hZD : (Qv (puAmalgam h.le) α' ⊓ Vv (puAmalgam h.le) α).relIndex (ZM (puAmalgam h.le) α) ≤
      (Qv (puAmalgam h.le) α' ⊓ Vv (puAmalgam h.le) α).relIndex
        (Vv (puAmalgam h.le) α ⊓ Qv (puAmalgam h.le) α' ⊔ ZM (puAmalgam h.le) α) :=
    Subgroup.relIndex_le_of_le_right le_sup_right
      (show (Subgroup.subgroupOf _ _).index ≠ 0 from Subgroup.index_ne_zero_of_finite)
  have hZeq : (Qv (puAmalgam h.le) α' ⊓ Vv (puAmalgam h.le) α).relIndex (ZM (puAmalgam h.le) α) =
      (Qv (puAmalgam h.le) α').relIndex (ZM (puAmalgam h.le) α) := by
    have := Subgroup.relIndex_inf_mul_relIndex (Qv (puAmalgam h.le) α') (Vv (puAmalgam h.le) α)
      (ZM (puAmalgam h.le) α)
    rw [inf_of_le_right (zm_le_vv h hα), Subgroup.relIndex_eq_one.mpr (zm_le_vv h hα),
      mul_one] at this
    exact this.symm
  rw [← htower, sq]
  rw [Nat.card_eq_fintype_card] at hZq
  exact Nat.mul_le_mul (hZq.trans (hZeq ▸ hZD)) hmod

theorem sq_le_relIndex_qv_of_star (hC : CentHyp (puAmalgam h.le)) {F : Type} [Field F]
    [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)} (hφ : IsSL3FullVia M T L φ)
    (hb : 2 < critDist (puAmalgam h.le)) {α α' : Vtx (puAmalgam h.le)}
    (hs : Star (puAmalgam h.le) α α')
    (hc : IsC1 h.le L (Fintype.card F) α (Vv (puAmalgam h.le) α) (ZM (puAmalgam h.le) α)) :
    Fintype.card F ^ 2 ≤
      (Qv (puAmalgam h.le) α').relIndex (Qv _ (geo (puAmalgam h.le) α' α 1)) := by
  have h20 := h.hyp20
  have hb0 := h.critDist_pos
  have hc' := ms22_iii _ h20 hb0 hC hs.1
  have hα'ε : (puAmalgam h.le).treeGraph.Adj α' (geo (puAmalgam h.le) α' α 1) :=
    adj_geo_one_of_isCritical _ hb0 hc'
  have hεγ : (puAmalgam h.le).treeGraph.Adj (geo (puAmalgam h.le) α' α 1)
      (geo (puAmalgam h.le) α' α 2) := adj_geo _ (i := 1) (by rw [hc'.2.1]; omega)
  have hγ : IsMVtx (puAmalgam h.le) (geo (puAmalgam h.le) α' α 2) := isMVtx_geo_two _ h20 hb0 hc'
  have hεH : ¬ IsMVtx (puAmalgam h.le) (geo (puAmalgam h.le) α' α 1) := by
    rw [← isMVtx_iff_of_adj _ hα'ε]
    exact hc'.1
  have hVε : Vv (puAmalgam h.le) α ≤ Qv _ (geo (puAmalgam h.le) α' α 1) :=
    hs.2.trans (qv_le_qv _ h20 hγ hεγ.symm)
  have hfε := finite_qv _ h20 hεH
  refine (sq_le_relIndex_vv_of_star h hfull hC hφ hb hs hc).trans ?_
  exact Subgroup.relIndex_le_of_le_right hVε
    (show (Subgroup.subgroupOf _ _).index ≠ 0 from Subgroup.index_ne_zero_of_finite)

theorem vv_sup_qv_eq_of_star (hC : CentHyp (puAmalgam h.le)) {F : Type} [Field F]
    [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)} (hφ : IsSL3FullVia M T L φ)
    (hb : 2 < critDist (puAmalgam h.le)) {α α' : Vtx (puAmalgam h.le)}
    (hs : Star (puAmalgam h.le) α α')
    (hc : IsC1 h.le L (Fintype.card F) α (Vv (puAmalgam h.le) α) (ZM (puAmalgam h.le) α))
    (hT : (Qv (puAmalgam h.le) α').relIndex (Qv _ (geo (puAmalgam h.le) α' α 1)) ≤
      Fintype.card F ^ 2) :
    Vv (puAmalgam h.le) α ⊔ Qv (puAmalgam h.le) α' = Qv _ (geo (puAmalgam h.le) α' α 1) := by
  have h20 := h.hyp20
  have hb0 := h.critDist_pos
  have hc' := ms22_iii _ h20 hb0 hC hs.1
  have hα'ε : (puAmalgam h.le).treeGraph.Adj α' (geo (puAmalgam h.le) α' α 1) :=
    adj_geo_one_of_isCritical _ hb0 hc'
  have hεγ : (puAmalgam h.le).treeGraph.Adj (geo (puAmalgam h.le) α' α 1)
      (geo (puAmalgam h.le) α' α 2) := adj_geo _ (i := 1) (by rw [hc'.2.1]; omega)
  have hγ : IsMVtx (puAmalgam h.le) (geo (puAmalgam h.le) α' α 2) := isMVtx_geo_two _ h20 hb0 hc'
  have hεH : ¬ IsMVtx (puAmalgam h.le) (geo (puAmalgam h.le) α' α 1) := by
    rw [← isMVtx_iff_of_adj _ hα'ε]
    exact hc'.1
  have hVε : Vv (puAmalgam h.le) α ≤ Qv _ (geo (puAmalgam h.le) α' α 1) :=
    hs.2.trans (qv_le_qv _ h20 hγ hεγ.symm)
  have hQε : Qv (puAmalgam h.le) α' ≤ Qv _ (geo (puAmalgam h.le) α' α 1) :=
    qv_le_qv _ h20 hc'.1 hα'ε
  have hfε := finite_qv _ h20 hεH
  have hle : Vv (puAmalgam h.le) α ⊔ Qv (puAmalgam h.le) α' ≤
      Qv _ (geo (puAmalgam h.le) α' α 1) := sup_le hVε hQε
  have hfin : Finite ↥(Vv (puAmalgam h.le) α ⊔ Qv (puAmalgam h.le) α') :=
    Finite.of_injective _ (Subgroup.inclusion_injective hle)
  have htower := Subgroup.relIndex_mul_relIndex _ _ _
    (le_sup_right : Qv (puAmalgam h.le) α' ≤ Vv (puAmalgam h.le) α ⊔ Qv (puAmalgam h.le) α') hle
  have h1 := sq_le_relIndex_vv_of_star h hfull hC hφ hb hs hc
  have h2 : (Qv (puAmalgam h.le) α').relIndex (Vv (puAmalgam h.le) α) ≤
      (Qv (puAmalgam h.le) α').relIndex (Vv (puAmalgam h.le) α ⊔ Qv (puAmalgam h.le) α') :=
    Subgroup.relIndex_le_of_le_right le_sup_left
      (show (Subgroup.subgroupOf _ _).index ≠ 0 from Subgroup.index_ne_zero_of_finite)
  have hpos : 0 < (Vv (puAmalgam h.le) α ⊔ Qv (puAmalgam h.le) α').relIndex
      (Qv _ (geo (puAmalgam h.le) α' α 1)) :=
    Nat.pos_of_ne_zero (show (Subgroup.subgroupOf _ _).index ≠ 0 from
      Subgroup.index_ne_zero_of_finite)
  have hq2 : 0 < Fintype.card F ^ 2 := by positivity
  have h3 : (Vv (puAmalgam h.le) α ⊔ Qv (puAmalgam h.le) α').relIndex
      (Qv _ (geo (puAmalgam h.le) α' α 1)) = 1 := by
    by_contra hne
    have h4 : 2 ≤ (Vv (puAmalgam h.le) α ⊔ Qv (puAmalgam h.le) α').relIndex
        (Qv _ (geo (puAmalgam h.le) α' α 1)) := by omega
    have := Nat.mul_le_mul (h1.trans h2) h4
    rw [htower] at this
    nlinarith
  exact le_antisymm hle (Subgroup.relIndex_eq_one.mp h3)

theorem relIndex_qv_qv_le {F : Type} [Field F] [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)}
    (hφ : IsSL3FullVia M T L φ) {α β : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α)
    (hαβ : (puAmalgam h.le).treeGraph.Adj α β)
    (hUZ : Usup (puAmalgam h.le) α β ≤ ZH (puAmalgam h.le) β)
    (hUq : Nat.card ↥(Usup (puAmalgam h.le) α β) = Nat.card F ^ 2) :
    (Qv (puAmalgam h.le) α).relIndex (Qv (puAmalgam h.le) β) ≤ Nat.card F ^ 2 := by
  have h20 := h.hyp20
  have hb0 := h.critDist_pos
  have hq : 2 ≤ Nat.card F := Finite.one_lt_card
  have hβH : ¬ IsMVtx (puAmalgam h.le) β := by
    rw [← isMVtx_iff_of_adj _ hαβ]
    exact hα
  have hQs : Qv (puAmalgam h.le) β ≤ stab _ α := qv_le_stab_of_adj _ hαβ.symm
  have hQQ : Qv (puAmalgam h.le) α ≤ Qv _ β := qv_le_qv _ h20 hα hαβ
  have hfQ := finite_qv _ h20 hβH
  have hT2 := isPGroup_qv _ h20 hβH
  obtain ⟨ψ, -, hψ⟩ := exists_natural_Uloc h hφ hα
  have hker : Qv (puAmalgam h.le) β ⊓ Subgroup.centralizer (Uloc h.le L α : Set _) =
      Qv (puAmalgam h.le) α := by
    apply le_antisymm
    · rintro x ⟨hxQ, hxc⟩
      obtain ⟨e, he⟩ := hT2 ⟨x, hxQ⟩
      refine mem_qv_of_centralizer_uloc h hα (hQs hxQ) hxc ⟨e, ?_⟩
      have := congrArg Subtype.val he
      simpa using this
    · refine le_inf hQQ ?_
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      exact (Subgroup.mem_centralizer_iff.mp
        (zm_le_centralizer_qv _ h20 hα (uloc_le_zm h hfull hα hu)) x hx).symm
  have h1 := card_natImage_mul hψ hQs
  rw [hker] at h1
  have h2 := relIndex_mul_card_inf (Qv (puAmalgam h.le) α) (Qv (puAmalgam h.le) β)
  rw [inf_of_le_left hQQ] at h2
  have hfα : Finite ↥(Qv (puAmalgam h.le) α) :=
    Finite.of_injective _ (Subgroup.inclusion_injective hQQ)
  have hpos : 0 < Nat.card ↥(Qv (puAmalgam h.le) α) := Nat.card_pos
  have heq : (Qv (puAmalgam h.le) α).relIndex (Qv (puAmalgam h.le) β) =
      Nat.card ↥(natImage ψ (Qv (puAmalgam h.le) β)) :=
    Nat.eq_of_mul_eq_mul_right hpos (h2.trans h1.symm)
  rw [heq]
  have hC2 : Module.finrank F (commN (natImage ψ (Qv (puAmalgam h.le) β))) = 2 := by
    have := hUq
    rw [usup_eq_commutator_uloc h hfull hα hαβ, card_commutator_eq hψ hQs,
      Module.natCard_eq_pow_finrank (K := F)] at this
    exact Nat.pow_right_injective hq this
  have hcard : Nat.card ↥(ZH (puAmalgam h.le) β ⊓ Uloc h.le L α) = Nat.card F ^ 2 := by
    have hrel := relIndex_zh_zm h hfull hφ hα hαβ hUZ hUq
    rw [zm_eq_uloc_sup_zloc h hfull hα] at hrel
    have hZQ : ZM (puAmalgam h.le) α ≤ Qv _ β :=
      (zm_le_qv_self _ hα hb0).trans hQQ
    have hfU : Finite ↥(Uloc h.le L α) :=
      Finite.of_injective _ (Subgroup.inclusion_injective ((uloc_le_zm h hfull hα).trans hZQ))
    have hfW : Finite ↥(Zloc h.le L α) :=
      Finite.of_injective _ (Subgroup.inclusion_injective ((zloc_le_zm h hfull hα).trans hZQ))
    rw [relIndex_sup_eq_of_le (zloc_le_zh h hfull hα hαβ)
      ((zloc_le_centralizer_stab h hfull hα).trans (Subgroup.centralizer_le
        ((uloc_le_zm h hfull hα).trans ((zm_le_qv_self _ hα hb0).trans (qv_le_stab _ α)))))
      (uloc_inf_zloc h hfull α)] at hrel
    have hmul := relIndex_mul_card_inf (ZH (puAmalgam h.le) β) (Uloc h.le L α)
    rw [hrel, card_eq_of_natural hψ] at hmul
    have hqpos : 0 < Nat.card F := Nat.card_pos
    have : Nat.card F * Nat.card ↥(ZH (puAmalgam h.le) β ⊓ Uloc h.le L α) =
        Nat.card F * Nat.card F ^ 2 := by rw [hmul]; ring
    exact Nat.eq_of_mul_eq_mul_left hqpos this
  have hF2 : Module.finrank F (fixN (natImage ψ (Qv (puAmalgam h.le) β))) = 2 := by
    rw [zh_inf_uloc h hfull hα hαβ, card_inf_centralizer_eq hψ hQs,
      Module.natCard_eq_pow_finrank (K := F)] at hcard
    exact Nat.pow_right_injective hq hcard
  calc Nat.card ↥(natImage ψ (Qv (puAmalgam h.le) β)) ≤
        Nat.card ↥(commN (natImage ψ (Qv (puAmalgam h.le) β))) :=
      card_le_card_commN_of_finrank_fixN hF2
    _ = Nat.card F ^ 2 := by rw [Module.natCard_eq_pow_finrank (K := F), hC2]

omit hfull in
theorem relIndex_qv_qv_eq {α β α' β' : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α)
    (hαβ : (puAmalgam h.le).treeGraph.Adj α β) (hα' : IsMVtx _ α')
    (hαβ' : (puAmalgam h.le).treeGraph.Adj α' β') :
    (Qv (puAmalgam h.le) α').relIndex (Qv (puAmalgam h.le) β') =
      (Qv (puAmalgam h.le) α).relIndex (Qv (puAmalgam h.le) β) := by
  obtain ⟨g, hg1, hg2⟩ := exists_smul_edge_of_isMVtx _ hα hαβ hα' hαβ'
  rw [← hg1, ← hg2, qv_smul, qv_smul,
    Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective]

theorem concl433_edge (h42 : S42) (h431A : S431A) (h431B : S431B) {F : Type} [Field F]
    [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)} (hH : Hyp40 h φ) (hC : CentHyp (puAmalgam h.le))
    {α₀ α₀' : Vtx (puAmalgam h.le)} (hs : Star (puAmalgam h.le) α₀ α₀')
    {α β : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α) (hαβ : (puAmalgam h.le).treeGraph.Adj α β) :
    Usup (puAmalgam h.le) α β ≤ ZH (puAmalgam h.le) β ∧
      Nat.card ↥(Usup (puAmalgam h.le) α β) = Fintype.card F ^ 2 ∧
      (ZH (puAmalgam h.le) β).relIndex (ZM (puAmalgam h.le) α) = Fintype.card F ∧
      (Qv (puAmalgam h.le) α).relIndex (Qv (puAmalgam h.le) β) = Fintype.card F ^ 2 := by
  obtain ⟨hmin, hb, hφ⟩ := hH
  obtain ⟨α', hsα⟩ := exists_star_at _ hs hα
  have hcα := (h431A G M T L h F inferInstance inferInstance φ ⟨hmin, hb, hφ⟩ α α' hsα).2.2.2.1
  have hvii := (h431B G M T L h F inferInstance inferInstance φ ⟨hmin, hb, hφ⟩ α α' hsα).2.2
  have hUZ := usup_le_zh_of_star h hfull h42 hmin hC hφ hb hs hα hαβ hcα hvii
  have hUq := card_usup_of_star h hC hφ hb hs hα hαβ
  have hZ := relIndex_zh_zm h hfull hφ hα hαβ hUZ hUq
  have hTle := relIndex_qv_qv_le h hfull hφ hα hαβ hUZ hUq
  have hc₀ := (h431A G M T L h F inferInstance inferInstance φ ⟨hmin, hb, hφ⟩ α₀ α₀' hs).2.2.2.1
  have hTge := sq_le_relIndex_qv_of_star h hfull hC hφ hb hs hc₀
  have hc' := ms22_iii _ h.hyp20 h.critDist_pos hC hs.1
  rw [relIndex_qv_qv_eq h hα hαβ hc'.1 (adj_geo_one_of_isCritical _ h.critDist_pos hc')] at hTge
  rw [Nat.card_eq_fintype_card (α := F)] at hUq hZ hTle
  exact ⟨hUZ, hUq, hZ, le_antisymm hTle hTge⟩

theorem bloc_le_of_star (hC : CentHyp (puAmalgam h.le)) {F : Type} [Field F]
    [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)} (hφ : IsSL3FullVia M T L φ)
    (hb : 2 < critDist (puAmalgam h.le)) {α α' : Vtx (puAmalgam h.le)}
    (hs : Star (puAmalgam h.le) α α')
    (hc : IsC1 h.le L (Fintype.card F) α (Vv (puAmalgam h.le) α) (ZM (puAmalgam h.le) α))
    (hT : (Qv (puAmalgam h.le) α').relIndex (Qv _ (geo (puAmalgam h.le) α' α 1)) ≤
      Fintype.card F ^ 2) :
    Bloc h.le L α ≤ Vv (puAmalgam h.le) α ⊓ Qv (puAmalgam h.le) α' ⊔ ZM (puAmalgam h.le) α := by
  have h20 := h.hyp20
  have hb0 := h.critDist_pos
  have hc' := ms22_iii _ h20 hb0 hC hs.1
  have hα := hs.1.1
  have hαβ := adj_geo_one_of_isCritical _ hb0 hs.1
  have hZ'β : ZM (puAmalgam h.le) α' ≤ Qv _ (geo (puAmalgam h.le) α α' 1) :=
    zm_le_qv_geo_one _ h20 hb0 hs.1
  have hα'ε : (puAmalgam h.le).treeGraph.Adj α' (geo (puAmalgam h.le) α' α 1) :=
    adj_geo_one_of_isCritical _ hb0 hc'
  have hεγ : (puAmalgam h.le).treeGraph.Adj (geo (puAmalgam h.le) α' α 1)
      (geo (puAmalgam h.le) α' α 2) := adj_geo _ (i := 1) (by rw [hc'.2.1]; omega)
  have hγ : IsMVtx (puAmalgam h.le) (geo (puAmalgam h.le) α' α 2) := isMVtx_geo_two _ h20 hb0 hc'
  have hεH : ¬ IsMVtx (puAmalgam h.le) (geo (puAmalgam h.le) α' α 1) := by
    rw [← isMVtx_iff_of_adj _ hα'ε]
    exact hc'.1
  have hVε : Vv (puAmalgam h.le) α ≤ Qv _ (geo (puAmalgam h.le) α' α 1) :=
    hs.2.trans (qv_le_qv _ h20 hγ hεγ.symm)
  have hfε := finite_qv _ h20 hεH
  have hVfin : Finite ↥(Vv (puAmalgam h.le) α) :=
    Finite.of_injective _ (Subgroup.inclusion_injective hVε)
  have hZn := stab_le_normalizer_zm (puAmalgam h.le) α
  have hZ's : ZM (puAmalgam h.le) α' ≤ stab _ α := zm_le_stab_right _ h20 hb0 hC hc'
  have hVs : Vv (puAmalgam h.le) α ≤ stab _ α := (vv_le_qv h hb hα).trans (qv_le_stab _ α)
  have hBn : stab (puAmalgam h.le) α ≤
      Subgroup.normalizer (Bloc h.le L α : Set (puAmalgam h.le).Universal) :=
    stab_le_normalizer_of_smul (F := fun δ => Bloc h.le L δ) _ (fun g δ => bloc_smul h g δ) α
  have hBV : Bloc h.le L α ≤ Vv _ α := bloc_le_vv h α
  have hZB : ZM (puAmalgam h.le) α ≤ Bloc h.le L α := zm_le_bloc h hb hα
  set D' := Vv (puAmalgam h.le) α ⊓ Qv (puAmalgam h.le) α' ⊔ ZM (puAmalgam h.le) α with hD'
  have hD'V : D' ≤ Vv _ α := sup_le inf_le_left (zm_le_vv h hα)
  have hV2 : (Qv (puAmalgam h.le) α').relIndex (Vv (puAmalgam h.le) α) ≤ Fintype.card F ^ 2 :=
    (Subgroup.relIndex_le_of_le_right hVε
      (show (Subgroup.subgroupOf _ _).index ≠ 0 from Subgroup.index_ne_zero_of_finite)).trans hT
  have hD1 : Qv (puAmalgam h.le) α' ⊓ Vv (puAmalgam h.le) α ≤ D' :=
    (inf_comm _ _).le.trans le_sup_left
  have hD'fin : Finite ↥D' := Finite.of_injective _ (Subgroup.inclusion_injective hD'V)
  have htower := Subgroup.relIndex_mul_relIndex _ _ _ hD1 hD'V
  rw [Subgroup.inf_relIndex_right] at htower
  have hZq := le_relIndex_zm_of_isCritical h hC hφ hs.1
  have hZD : (Qv (puAmalgam h.le) α' ⊓ Vv (puAmalgam h.le) α).relIndex (ZM (puAmalgam h.le) α) ≤
      (Qv (puAmalgam h.le) α' ⊓ Vv (puAmalgam h.le) α).relIndex D' :=
    Subgroup.relIndex_le_of_le_right le_sup_right
      (show (Subgroup.subgroupOf _ _).index ≠ 0 from Subgroup.index_ne_zero_of_finite)
  have hZeq : (Qv (puAmalgam h.le) α' ⊓ Vv (puAmalgam h.le) α).relIndex (ZM (puAmalgam h.le) α) =
      (Qv (puAmalgam h.le) α').relIndex (ZM (puAmalgam h.le) α) := by
    have := Subgroup.relIndex_inf_mul_relIndex (Qv (puAmalgam h.le) α') (Vv (puAmalgam h.le) α)
      (ZM (puAmalgam h.le) α)
    rw [inf_of_le_right (zm_le_vv h hα), Subgroup.relIndex_eq_one.mpr (zm_le_vv h hα),
      mul_one] at this
    exact this.symm
  rw [Nat.card_eq_fintype_card] at hZq
  have hq : 0 < Fintype.card F := Fintype.card_pos
  have hD'q : D'.relIndex (Vv (puAmalgam h.le) α) ≤ Fintype.card F := by
    have h1 := hZq.trans (hZeq ▸ hZD)
    have h2 : Fintype.card F * D'.relIndex (Vv (puAmalgam h.le) α) ≤ Fintype.card F ^ 2 := by
      calc Fintype.card F * D'.relIndex (Vv (puAmalgam h.le) α)
          ≤ (Qv (puAmalgam h.le) α' ⊓ Vv (puAmalgam h.le) α).relIndex D' *
              D'.relIndex (Vv (puAmalgam h.le) α) := Nat.mul_le_mul_right _ h1
        _ = _ := htower
        _ ≤ _ := hV2
    rw [sq] at h2
    exact Nat.le_of_mul_le_mul_left h2 hq
  have hD''X : ⁅D' ⊔ Bloc h.le L α, ZM (puAmalgam h.le) α'⁆ ≤ Bloc h.le L α := by
    refine S4A.commutator_sup_le_of ?_ ?_ ?_ ?_
    · refine (S4A.commutator_sup_le_of ?_ ?_ ?_ ?_).trans le_rfl
      · rw [(Subgroup.commutator_eq_bot_iff_le_centralizer).mpr ?_]
        · exact bot_le
        · intro z hz
          rw [Subgroup.mem_centralizer_iff]
          intro x hx
          exact (Subgroup.mem_centralizer_iff.mp
            (zm_le_centralizer_qv _ h20 hc'.1 hx) z hz.2).symm
      · exact (Subgroup.le_normalizer_iff_commutator_le_left.mp (hZ's.trans hZn)).trans hZB
      · exact (inf_le_left.trans hVs).trans hBn
      · exact ((zm_le_vv h hα).trans hVs).trans hBn
    · exact Subgroup.le_normalizer_iff_commutator_le_left.mp (hZ's.trans hBn)
    · exact (hD'V.trans hVs).trans hBn
    · exact (hBV.trans hVs).trans hBn
  have hge := le_relIndex_vv_of_isC1_bloc h hfull hb hα hαβ hc hZ'β hc'.2.2 hD''X
  have hD''V : D' ⊔ Bloc h.le L α ≤ Vv _ α := sup_le hD'V hBV
  have hD''fin : Finite ↥(D' ⊔ Bloc h.le L α) :=
    Finite.of_injective _ (Subgroup.inclusion_injective hD''V)
  have htower2 := Subgroup.relIndex_mul_relIndex _ _ _ (le_sup_left : D' ≤ D' ⊔ Bloc h.le L α)
    hD''V
  have hpos : 0 < (D' ⊔ Bloc h.le L α).relIndex (Vv (puAmalgam h.le) α) :=
    Nat.pos_of_ne_zero (show (Subgroup.subgroupOf _ _).index ≠ 0 from
      Subgroup.index_ne_zero_of_finite)
  have h1 : D'.relIndex (D' ⊔ Bloc h.le L α) = 1 := by
    have h3 : D'.relIndex (D' ⊔ Bloc h.le L α) *
        (D' ⊔ Bloc h.le L α).relIndex (Vv (puAmalgam h.le) α) ≤
        1 * (D' ⊔ Bloc h.le L α).relIndex (Vv (puAmalgam h.le) α) := by
      rw [htower2, one_mul]
      exact hD'q.trans hge
    have := Nat.le_of_mul_le_mul_right h3 hpos
    have h0 : 0 < D'.relIndex (D' ⊔ Bloc h.le L α) :=
      Nat.pos_of_ne_zero (show (Subgroup.subgroupOf _ _).index ≠ 0 from
        Subgroup.index_ne_zero_of_finite)
    omega
  exact le_sup_right.trans (Subgroup.relIndex_eq_one.mp h1)

end Edge

end CFSG.Quasithin.MS93.S4A
