module

public import CFSG.Quasithin.MS93.S43FFF
public import CFSG.Quasithin.MS93.S46I461
public import CFSG.Quasithin.MS93.S34FGen

public section

namespace CFSG.Quasithin.MS93.S4L

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S4A CFSG.Quasithin.MS93.S46
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

section Crit

variable (h : PUHyp M T L)
include h

theorem exists_ltil_smul_eq_gen {μ ρ ν : Vtx (puAmalgam h.le)} (hμ : IsMVtx _ μ)
    (hμρ : (puAmalgam h.le).treeGraph.Adj μ ρ) (hν : Qv (puAmalgam h.le) ρ ≤ stab _ ν)
    {g : (puAmalgam h.le).Universal} (hg : g ∈ stab _ μ) :
    ∃ l ∈ Ltil h.le L μ, l • ν = g • ν := by
  have hnorm : Qv (puAmalgam h.le) ρ ≤
      Subgroup.normalizer (Ltil h.le L μ : Set (puAmalgam h.le).Universal) :=
    (qv_le_stab_of_adj _ hμρ.symm).trans (stab_le_normalizer_ltil h μ)
  have hg' : g ∈ ((Ltil h.le L μ ⊔ Qv _ ρ : Subgroup _) : Set (puAmalgam h.le).Universal) := by
    rw [← S34F.stab_eq_ltil_sup_qv_gen h hμ hμρ]
    exact hg
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hnorm] at hg'
  obtain ⟨l, hl, y, hy, rfl⟩ := hg'
  exact ⟨l, hl, by rw [mul_smul, (mem_stab _).mp (hν hy)]⟩

theorem ltil_le_normalizer_vvPerp {α : Vtx (puAmalgam h.le)}
    {K : Subgroup (puAmalgam h.le).Universal}
    (hKL : Ltil h.le L α ≤ Subgroup.normalizer (K : Set _))
    (hKV : Vv (puAmalgam h.le) α ≤ Subgroup.normalizer (K : Set _)) :
    Ltil h.le L α ≤ Subgroup.normalizer (vvPerp (X := puAmalgam h.le) α K : Set _) := by
  have hVn := stab_le_normalizer_vv h α
  have hLs := ltil_le_stab h α
  have key : ∀ y ∈ Ltil h.le L α, ∀ v ∈ vvPerp (X := puAmalgam h.le) α K,
      y * v * y⁻¹ ∈ vvPerp (X := puAmalgam h.le) α K := by
    intro y hy v hv
    rw [mem_vvPerp_iff hKV] at hv ⊢
    refine ⟨(Subgroup.mem_normalizer_iff.mp (hVn (hLs hy)) v).mp hv.1, fun w hw => ?_⟩
    have hw' : y⁻¹ * w * y⁻¹⁻¹ ∈ Vv (puAmalgam h.le) α :=
      (Subgroup.mem_normalizer_iff.mp (hVn (hLs (Subgroup.inv_mem _ hy))) w).mp hw
    have e : ⁅y * v * y⁻¹, w⁆ = y * ⁅v, y⁻¹ * w * y⁻¹⁻¹⁆ * y⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hKL hy) _).mp (hv.2 _ hw')
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro v
  constructor
  · exact key g hg v
  · intro hv
    have := key g⁻¹ (Subgroup.inv_mem _ hg) _ hv
    simpa [mul_assoc] using this

theorem commutator_vv_le_of_ltil_flat (hb : 2 < critDist (puAmalgam h.le))
    {α : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α) {K : Subgroup (puAmalgam h.le).Universal}
    (hKL : Ltil h.le L α ≤ Subgroup.normalizer (K : Set _))
    (hKV : Vv (puAmalgam h.le) α ≤ Subgroup.normalizer (K : Set _))
    (hVL : ⁅Vv (puAmalgam h.le) α, Ltil h.le L α⁆ ≤ vvPerp α K) :
    ⁅Vv (puAmalgam h.le) α, Vv (puAmalgam h.le) α⁆ ≤ K := by
  have h20 := h.hyp20
  set Ut := vvPerp (X := puAmalgam h.le) α K with hUt
  have hUtV : Ut ≤ Vv _ α := vvPerp_le α K
  have hUtn : Ltil h.le L α ≤ Subgroup.normalizer (Ut : Set _) :=
    ltil_le_normalizer_vvPerp h hKL hKV
  have hVρα' : ∀ ρ ∈ (puAmalgam h.le).treeGraph.neighborSet α,
      Vv (puAmalgam h.le) ρ ≤ Vv _ α := fun ρ hρ => by
    rw [vv_eq_iSup_vv hα]
    exact le_iSup₂_of_le (f := fun ρ (_ : ρ ∈ (puAmalgam h.le).treeGraph.neighborSet α) =>
      Vv (puAmalgam h.le) ρ) ρ hρ le_rfl
  have hZ : ∀ ρ₀ μ : Vtx (puAmalgam h.le), (puAmalgam h.le).treeGraph.Adj α ρ₀ →
      (puAmalgam h.le).treeGraph.Adj ρ₀ μ → ZM (puAmalgam h.le) μ ≤ Ut := by
    intro ρ₀ μ hαρ hρμ
    have hμM : IsMVtx (puAmalgam h.le) μ := by
      have h1 := (isMVtx_iff_of_adj _ hαρ).mp hα
      have h2 := isMVtx_iff_of_adj _ hρμ
      tauto
    have hZV : ZM (puAmalgam h.le) μ ≤ Vv _ α :=
      (zm_le_vv_of_adj hρμ hμM).trans (hVρα' ρ₀ hαρ)
    set W := ZM (puAmalgam h.le) μ ⊔ Ut with hW
    have hWn : Ltil h.le L α ≤ Subgroup.normalizer (W : Set _) := by
      rw [Subgroup.le_normalizer_iff_commutator_le_left]
      refine S4A.commutator_sup_le_of ?_ ?_ ?_ ?_
      · exact ((Subgroup.commutator_mono hZV le_rfl).trans hVL).trans le_sup_right
      · exact (Subgroup.le_normalizer_iff_commutator_le_left.mp hUtn).trans le_sup_right
      · exact le_sup_left.trans Subgroup.le_normalizer
      · exact le_sup_right.trans Subgroup.le_normalizer
    have hρ : ∀ ρ ∈ (puAmalgam h.le).treeGraph.neighborSet α,
        ⁅ZM (puAmalgam h.le) μ, Vv _ ρ⁆ ≤ K := by
      intro ρ hρ
      obtain ⟨g, hg, hgρ⟩ := exists_mem_stab_smul _ hαρ hρ
      obtain ⟨l, hl, hlρ⟩ := exists_ltil_smul_eq_gen h hα hαρ (qv_le_stab _ ρ₀) hg
      have hgμ : (puAmalgam h.le).treeGraph.Adj ρ (l • μ) := by
        rw [← hgρ, ← hlρ]; exact (adj_smul _ l _ _).mpr hρμ
      have hle : ZM (puAmalgam h.le) μ ≤ Vv _ ρ ⊔ Ut := by
        have h1 : ZM (puAmalgam h.le) μ ≤ W.map (MulAut.conj l).toMonoidHom := by
          rw [map_conj_eq_of_mem_normalizer (hWn hl)]
          exact le_sup_left
        refine h1.trans ?_
        rw [hW, Subgroup.map_sup, ← zm_smul, map_conj_eq_of_mem_normalizer (hUtn hl)]
        have hgμM : IsMVtx (puAmalgam h.le) (l • μ) := (isMVtx_smul _ l μ).mpr hμM
        exact sup_le_sup_right (zm_le_vv_of_adj hgμ hgμM) _
      have hVρab := vv_le_centralizer_of_not_isMVtx h20 hb (ρ := ρ)
        (by have := isMVtx_iff_of_adj _ hρ; tauto)
      refine (Subgroup.commutator_mono hle le_rfl).trans ?_
      refine S4A.commutator_sup_le_of ?_ ?_ ((hVρα' ρ hρ).trans hKV) (hUtV.trans hKV)
      · rw [(Subgroup.commutator_eq_bot_iff_le_centralizer).mpr hVρab]
        exact bot_le
      · rw [Subgroup.commutator_le]
        intro u hu w hw
        exact ((mem_vvPerp_iff hKV).mp hu).2 w (hVρα' ρ hρ hw)
    have hZVK : ⁅ZM (puAmalgam h.le) μ, Vv _ α⁆ ≤ K := by
      rw [vv_eq_iSup_vv hα, iSup_subtype', Subgroup.commutator_comm]
      refine commutator_iSup_le_of (fun ρ => ?_) ?_
      · rw [Subgroup.commutator_comm]; exact hρ ρ.1 ρ.2
      · exact iSup_le fun ρ => (hVρα' ρ.1 ρ.2).trans hKV
    intro z hz
    rw [mem_vvPerp_iff hKV]
    exact ⟨hZV hz, fun w hw => hZVK (Subgroup.commutator_mem_commutator hz hw)⟩
  have hVU : Vv (puAmalgam h.le) α ≤ Ut := by
    rw [vv_eq_iSup_vv hα]
    refine iSup₂_le fun ρ hρ => ?_
    have hρH : ¬ IsMVtx (puAmalgam h.le) ρ := by have := isMVtx_iff_of_adj _ hρ; tauto
    rw [vv_eq_iSup_of_not_isMVtx hρH]
    exact iSup₂_le fun μ hμ => hZ ρ μ hρ hμ
  rw [Subgroup.commutator_le]
  intro v hv w hw
  exact ((mem_vvPerp_iff hKV).mp (hVU hv)).2 w hw

end Crit

section Ker

variable (h : PUHyp M T L) (hU : IsSL3U M T L) {F : Type} [Field F]
include h hU

theorem toSL3_eq_one_iff_mem_qv_flat {δ : Vtx (puAmalgam h.le)} (hδ : IsMVtx _ δ)
    {ψ : ↥(S34F.flat h δ) →* ↥(StatedSL 3 F)}
    (hψ : IsSumOfNaturalModulesVia (S34F.flat h δ) (Uloc h.le L δ) ⊥ ψ false 1)
    (x : ↥(S34F.flat h δ)) :
    toSL3 ψ x = 1 ↔ (x : (puAmalgam h.le).Universal) ∈ Qv _ δ := by
  rw [toSL3_eq_one_iff hψ, ← S43F.flat_inf_centralizer_uloc h hU hδ]
  constructor
  · intro hx
    refine ⟨x.2, ?_⟩
    show (x : (puAmalgam h.le).Universal) ∈ Subgroup.centralizer _
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have := hx u hu
    calc u * (x : (puAmalgam h.le).Universal)
        = (x : (puAmalgam h.le).Universal) * u * ((x : (puAmalgam h.le).Universal))⁻¹ *
            (x : (puAmalgam h.le).Universal) := by rw [this]
      _ = x * u := by group
  · intro hx u hu
    have hc := Subgroup.mem_centralizer_iff.mp hx.2 u hu
    rw [← hc, mul_inv_cancel_right]

theorem pow_two_pow_eq_one_of_toSL3_eq_one_flat {δ : Vtx (puAmalgam h.le)} (hδ : IsMVtx _ δ)
    {ψ : ↥(S34F.flat h δ) →* ↥(StatedSL 3 F)}
    (hψ : IsSumOfNaturalModulesVia (S34F.flat h δ) (Uloc h.le L δ) ⊥ ψ false 1)
    (x : ↥(S34F.flat h δ)) (hx : toSL3 ψ x = 1) : ∃ e : ℕ, x ^ 2 ^ e = 1 := by
  have hxQ := (toSL3_eq_one_iff_mem_qv_flat h hU hδ hψ x).mp hx
  obtain ⟨e, he⟩ := isPGroup_qv_of_isMVtx h hδ ⟨x, hxQ⟩
  refine ⟨e, Subtype.ext ?_⟩
  have := congrArg Subtype.val he
  simpa using this

theorem card_natImage_eq_relIndex_flat {δ : Vtx (puAmalgam h.le)} (hδ : IsMVtx _ δ)
    {ψ : ↥(S34F.flat h δ) →* ↥(StatedSL 3 F)}
    (hψ : IsSumOfNaturalModulesVia (S34F.flat h δ) (Uloc h.le L δ) ⊥ ψ false 1)
    {A : Subgroup (puAmalgam h.le).Universal} (hA : A ≤ S34F.flat h δ) :
    Nat.card ↥(natImage ψ A) = (Qv _ δ).relIndex A := by
  have hfinS := finite_stab h hδ
  have hfinA : Finite ↥A := Finite.of_injective _ (Subgroup.inclusion_injective
    (hA.trans (S43F.flat_le_stab h δ)))
  have h1 := card_natImage_mul hψ hA
  have hinf : A ⊓ Subgroup.centralizer (Uloc h.le L δ : Set (puAmalgam h.le).Universal) =
      Qv _ δ ⊓ A := by
    rw [← S43F.flat_inf_centralizer_uloc h hU hδ]
    apply le_antisymm
    · exact fun x hx => ⟨⟨hA hx.1, hx.2⟩, hx.1⟩
    · exact fun x hx => ⟨hx.2, hx.1.2⟩
  rw [hinf] at h1
  have h2 := relIndex_mul_card_inf (Qv (puAmalgam h.le) δ) A
  have : Finite ↥(Qv (puAmalgam h.le) δ ⊓ A) :=
    Finite.of_injective _ (Subgroup.inclusion_injective (inf_le_right : Qv _ δ ⊓ A ≤ A))
  have hpos : 0 < Nat.card ↥(Qv (puAmalgam h.le) δ ⊓ A) := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_right hpos (h1.trans h2.symm)

end Ker

section Gen

variable (h : PUHyp M T L) (hU : IsSL3U M T L) (hC : CentHyp (puAmalgam h.le))
include h hU hC

omit hC in
theorem vv_le_flat_of_dist_two (hb4 : critDist (puAmalgam h.le) = 4)
    {α μ : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α)
    (hd : (puAmalgam h.le).treeGraph.dist α μ = 2) :
    Vv (puAmalgam h.le) α ≤ S34F.flat h μ := by
  have hμ : IsMVtx (puAmalgam h.le) μ := by
    have he : Even ((puAmalgam h.le).treeGraph.dist α μ) := by rw [hd]; exact ⟨1, rfl⟩
    rw [even_dist_iff] at he
    tauto
  have hQ := S43F.qv_le_flat h hμ
  refine iSup₂_le fun x hx => ?_
  have hx' : (puAmalgam h.le).treeGraph.dist α x ≤ 2 := hx
  have htri := dist_triangle (puAmalgam h.le) x α μ
  rw [tdist_comm _ x α, hd] at htri
  by_cases hxM : IsMVtx (puAmalgam h.le) x
  · rw [zv_of_isMVtx _ hxM]
    by_cases h3 : (puAmalgam h.le).treeGraph.dist x μ ≤ 3
    · exact (zm_le_qv_of_dist_le_three hb4 hxM h3).trans hQ
    · by_cases hZ : ZM (puAmalgam h.le) x ≤ Qv _ μ
      · exact hZ.trans hQ
      · have hc : IsCritical (puAmalgam h.le) x μ := ⟨hxM, by omega, hZ⟩
        exact S34F.zm_le_flat h hU hc
  · rw [zv_of_not_isMVtx _ hxM]
    have hodd : ¬ Even ((puAmalgam h.le).treeGraph.dist α x) := by rw [even_dist_iff]; tauto
    have h1 : (puAmalgam h.le).treeGraph.dist α x = 1 := by
      rcases (by omega : (puAmalgam h.le).treeGraph.dist α x = 0 ∨
          (puAmalgam h.le).treeGraph.dist α x = 1 ∨
          (puAmalgam h.le).treeGraph.dist α x = 2) with e | e | e
      · exact absurd (by rw [e]; exact ⟨0, rfl⟩) hodd
      · exact e
      · exact absurd (by rw [e]; exact ⟨1, rfl⟩) hodd
    have hadj : (puAmalgam h.le).treeGraph.Adj α x := SimpleGraph.dist_eq_one_iff_adj.mp h1
    exact ((zh_le_zm _ hadj).trans (zm_le_qv_of_dist_le_three hb4 hα (by omega))).trans hQ

theorem critGen_le_flat (α γ : Vtx (puAmalgam h.le)) :
    critGen (puAmalgam h.le) α γ ≤ S34F.flat h α := by
  refine iSup₂_le fun δ hδ => ?_
  exact S34F.zm_le_flat h hU (ms22_iii _ h.hyp20 h.critDist_pos hC hδ.1)

end Gen

end CFSG.Quasithin.MS93.S4L
