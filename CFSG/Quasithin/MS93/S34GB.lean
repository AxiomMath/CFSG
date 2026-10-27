module

public import CFSG.Quasithin.MS93.S34FGen
public import CFSG.Quasithin.MS93.S46Gen
public import CFSG.Quasithin.MS93.S4A42

public section

namespace CFSG.Quasithin.MS93.S34G

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S4A CFSG.Quasithin.MS93.S46
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
include h

theorem commutator_vv_ltil_le_of_gen {α β : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α)
    (hαβ : (puAmalgam h.le).treeGraph.Adj α β) {X : Subgroup (puAmalgam h.le).Universal}
    (hXβ : X ≤ Qv _ β) (hXα : ¬ X ≤ Qv _ α) {W₀ : Subgroup (puAmalgam h.le).Universal}
    (hW₀ : stab _ α ≤ Subgroup.normalizer (W₀ : Set (puAmalgam h.le).Universal))
    (hXW : ⁅Vv (puAmalgam h.le) α, X⁆ ≤ W₀) :
    ⁅Vv (puAmalgam h.le) α, Ltil h.le L α⁆ ≤ W₀ := by
  have hVn := stab_le_normalizer_vv h α
  let K : Subgroup (puAmalgam h.le).Universal :=
    { carrier := {g | g ∈ stab (puAmalgam h.le) α ∧ ∀ v ∈ Vv (puAmalgam h.le) α, ⁅v, g⁆ ∈ W₀}
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨Subgroup.mul_mem _ ha hb, fun v hv => ?_⟩
        have hrw : ⁅v, a * b⁆ = ⁅v, a⁆ * (a * ⁅v, b⁆ * a⁻¹) := by
          simp only [commutatorElement_def]
          group
        rw [hrw]
        exact Subgroup.mul_mem _ (ha' v hv) ((Subgroup.mem_normalizer_iff.mp (hW₀ ha) _).mp
          (hb' v hv))
      one_mem' := ⟨Subgroup.one_mem _, fun v _ => by
        rw [commutatorElement_one_right]
        exact Subgroup.one_mem _⟩
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨Subgroup.inv_mem _ ha, fun v hv => ?_⟩
        have hrw : ⁅v, a⁻¹⁆ = a⁻¹ * (⁅v, a⁆)⁻¹ * a⁻¹⁻¹ := by
          simp only [commutatorElement_def]
          group
        rw [hrw]
        exact (Subgroup.mem_normalizer_iff.mp (hW₀ (Subgroup.inv_mem _ ha)) _).mp
          (Subgroup.inv_mem _ (ha' v hv)) }
  have hKs : K ≤ stab (puAmalgam h.le) α := fun g hg => hg.1
  have hKn : stab (puAmalgam h.le) α ≤
      Subgroup.normalizer (K : Set (puAmalgam h.le).Universal) := by
    refine le_normalizer_of_map_conj_le fun s hs => ?_
    rintro _ ⟨k, ⟨hk, hk'⟩, rfl⟩
    refine ⟨?_, fun v hv => ?_⟩
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hs hk) (Subgroup.inv_mem _ hs)
    · have hv' : s⁻¹ * v * s⁻¹⁻¹ ∈ Vv (puAmalgam h.le) α :=
        (Subgroup.mem_normalizer_iff.mp (hVn (Subgroup.inv_mem _ hs)) _).mp hv
      have hrw : ⁅v, (MulAut.conj s).toMonoidHom k⁆ = s * ⁅s⁻¹ * v * s⁻¹⁻¹, k⁆ * s⁻¹ := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, commutatorElement_def]
        group
      rw [hrw]
      exact (Subgroup.mem_normalizer_iff.mp (hW₀ hs) _).mp (hk' _ hv')
  have hXK : X ≤ K := fun x hx =>
    ⟨qv_le_stab_of_adj _ hαβ.symm (hXβ hx), fun v hv =>
      hXW (Subgroup.commutator_mem_commutator hv hx)⟩
  have hLs := ltil_le_stab h α
  have hJL : ⁅K, Ltil h.le L α⁆ ≤ Ltil h.le L α := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp
      (hKs.trans (stab_le_normalizer_ltil h α))
  have hJK : ⁅K, Ltil h.le L α⁆ ≤ K :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp (hLs.trans hKn)
  rcases commutator_ltil_le_or h hα hJL (Subgroup.normalizer_commutator_ge_right _ _) with hc | hc
  · exfalso
    apply hXα
    have hO : pCoreLtil h α ≤ Qv _ α := pCoreLtil_le_qv h hα
    have hQn : stab (puAmalgam h.le) α ≤
        Subgroup.normalizer (Qv (puAmalgam h.le) α : Set (puAmalgam h.le).Universal) :=
      stab_le_normalizer_qv _ α
    have h3 : ⁅⁅Ltil h.le L α, Ltil h.le L α⁆, K⁆ ≤ Qv _ α := by
      refine three_subgroups_le (hLs.trans hQn) (hLs.trans hQn) (hKs.trans hQn) ?_ ?_
      · rw [Subgroup.commutator_comm (Ltil h.le L α) K]
        exact hc.trans hO
      · exact hc.trans hO
    rw [ltil_perfect h hα, Subgroup.commutator_comm] at h3
    exact S34F.le_qv_of_commutator_le_gen h hα hαβ hXβ
      ((Subgroup.commutator_mono hXK le_rfl).trans h3)
  · rw [Subgroup.commutator_le]
    intro v hv l hl
    exact (hJK (hc hl)).2 v hv

theorem vv_le_vi_sup_commutator_gen {α β : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α)
    (hαβ : (puAmalgam h.le).treeGraph.Adj α β) :
    Vv (puAmalgam h.le) α ≤ Vi (puAmalgam h.le) β 1 ⊔ ⁅Vv _ α, Ltil h.le L α⁆ := by
  have h20 := h.hyp20
  have hVi : ∀ ρ, (puAmalgam h.le).treeGraph.dist β ρ ≤ 1 →
      Zv (puAmalgam h.le) ρ ≤ Vi (puAmalgam h.le) β 1 := fun ρ hρ =>
    le_iSup₂_of_le (f := fun ρ (_ : ρ ∈ {ρ : Vtx (puAmalgam h.le) |
      (puAmalgam h.le).treeGraph.dist β ρ ≤ 1}) => Zv (puAmalgam h.le) ρ) ρ hρ le_rfl
  have hViV : Vi (puAmalgam h.le) β 1 ≤ Vv _ α := by
    refine iSup₂_le fun ρ hρ => zv_le_vv h ?_
    have := dist_triangle (puAmalgam h.le) α β ρ
    rw [(SimpleGraph.dist_eq_one_iff_adj).mpr hαβ] at this
    exact this.trans (by simp only [Set.mem_ofPred_eq] at hρ; omega)
  have hZα : ZM (puAmalgam h.le) α ≤ Vi (puAmalgam h.le) β 1 := by
    rw [← zv_of_isMVtx _ hα]
    exact hVi α (by rw [tdist_comm, (SimpleGraph.dist_eq_one_iff_adj).mpr hαβ])
  refine iSup₂_le fun ρ hρ => ?_
  rcases isMVtx_of_dist_le_two h hα hρ with hρM | hadj
  · rcases Nat.lt_or_ge ((puAmalgam h.le).treeGraph.dist α ρ) 1 with h0 | h1
    · have : ρ = α := ((dist_eq_zero_iff (puAmalgam h.le)).mp (Nat.lt_one_iff.mp h0)).symm
      subst this
      rw [zv_of_isMVtx _ hρM]
      exact hZα.trans le_sup_left
    · have hev : Even ((puAmalgam h.le).treeGraph.dist α ρ) :=
        (even_dist_iff (puAmalgam h.le) α ρ).mpr ⟨fun _ => hρM, fun _ => hα⟩
      obtain ⟨k, hk⟩ := hev
      have hd : (puAmalgam h.le).treeGraph.dist α ρ = 2 := by
        show (puAmalgam h.le).treeGraph.dist α ρ = 2
        simp only [Set.mem_ofPred_eq] at hρ
        omega
      have hα1 : (puAmalgam h.le).treeGraph.Adj α (geo (puAmalgam h.le) α ρ 1) :=
        adj_geo_one _ (by omega)
      have h1ρ : (puAmalgam h.le).treeGraph.Adj (geo (puAmalgam h.le) α ρ 1) ρ := by
        have := adj_geo (puAmalgam h.le) (u := α) (w := ρ) (i := 1) (by omega)
        rwa [show geo (puAmalgam h.le) α ρ (1 + 1) = ρ from geo_of_le _ (by omega)] at this
      obtain ⟨g, hg, hgβ⟩ := exists_mem_stab_smul (puAmalgam h.le) hαβ hα1
      rw [S34F.stab_eq_ltil_sup_qv_gen h hα hαβ] at hg
      have hg' : g ∈ ((Ltil h.le L α ⊔ Qv (puAmalgam h.le) β : Subgroup _) : Set _) := hg
      rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _
        ((qv_le_stab_of_adj _ hαβ.symm).trans (stab_le_normalizer_ltil h α))] at hg'
      obtain ⟨l, hl, t, ht, rfl⟩ := hg'
      have htβ : t • β = β := (mem_stab _).mp (qv_le_stab _ β ht)
      have hlβ : l • β = geo (puAmalgam h.le) α ρ 1 := by
        rw [← hgβ, mul_smul, htβ]
      have hadjβ : (puAmalgam h.le).treeGraph.Adj β (l⁻¹ • ρ) := by
        have := (adj_smul _ l⁻¹ _ _).mpr h1ρ
        rwa [← hlβ, inv_smul_smul] at this
      have hZ : Zv (puAmalgam h.le) ρ =
          (Zv (puAmalgam h.le) (l⁻¹ • ρ)).map (MulAut.conj l).toMonoidHom := by
        rw [← zv_smul, smul_inv_smul]
      rw [hZ]
      rintro _ ⟨x, hx, rfl⟩
      have hxV : x ∈ Vi (puAmalgam h.le) β 1 :=
        hVi _ ((SimpleGraph.dist_eq_one_iff_adj).mpr hadjβ).le hx
      have hrw : (MulAut.conj l).toMonoidHom x = x * ⁅x⁻¹, l⁆ := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, commutatorElement_def, inv_inv]
        group
      rw [hrw]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hxV) (Subgroup.mem_sup_right
        (Subgroup.commutator_mem_commutator (hViV (Subgroup.inv_mem _ hxV)) hl))
  · have hρH : ¬ IsMVtx (puAmalgam h.le) ρ := by
      rw [← isMVtx_iff_of_adj (puAmalgam h.le) hadj]
      exact hα
    rw [zv_of_not_isMVtx _ hρH]
    exact (zh_le_zm _ hadj).trans (hZα.trans le_sup_left)

theorem vv_eq_vi_one_gen {α β : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α)
    (hαβ : (puAmalgam h.le).treeGraph.Adj α β)
    (hle : ⁅Vv (puAmalgam h.le) α, Ltil h.le L α⁆ ≤ Vi (puAmalgam h.le) β 1) :
    Vv (puAmalgam h.le) α = Vi (puAmalgam h.le) β 1 := by
  refine le_antisymm ((vv_le_vi_sup_commutator_gen h hα hαβ).trans (sup_le le_rfl hle)) ?_
  refine iSup₂_le fun ρ hρ => zv_le_vv h ?_
  have := dist_triangle (puAmalgam h.le) α β ρ
  rw [(SimpleGraph.dist_eq_one_iff_adj).mpr hαβ] at this
  exact this.trans (by simp only [Set.mem_ofPred_eq] at hρ; omega)

theorem not_commutator_vv_ltil_le_zm_gen (hb : 2 < critDist (puAmalgam h.le))
    {α β : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α) (hαβ : (puAmalgam h.le).treeGraph.Adj α β) :
    ¬ ⁅Vv (puAmalgam h.le) α, Ltil h.le L α⁆ ≤ ZM (puAmalgam h.le) α := by
  intro hle
  have h20 := h.hyp20
  have hβ : ¬ IsMVtx (puAmalgam h.le) β := by
    rw [← isMVtx_iff_of_adj _ hαβ]
    exact hα
  have hZα : ZM (puAmalgam h.le) α ≤ Vi (puAmalgam h.le) β 1 := by
    rw [← zv_of_isMVtx _ hα]
    exact le_iSup₂_of_le (f := fun ρ (_ : ρ ∈ {ρ : Vtx (puAmalgam h.le) |
      (puAmalgam h.le).treeGraph.dist β ρ ≤ 1}) => Zv (puAmalgam h.le) ρ) α
      (by rw [Set.mem_ofPred_eq, tdist_comm, (SimpleGraph.dist_eq_one_iff_adj).mpr hαβ])
      le_rfl
  have heq := vv_eq_vi_one_gen h hα hαβ (hle.trans hZα)
  have hViQ : Vi (puAmalgam h.le) β 1 ≤ Qv _ β := by
    rw [← heq]
    exact (vv_le_qv h hb hα).trans (qv_le_qv _ h20 hα hαβ)
  have hbot := ms21_iii _ h20 hα hαβ hViQ (heq ▸ stab_le_normalizer_vv h α)
    (stab_le_normalizer_of_smul (F := fun ρ => Vi (puAmalgam h.le) ρ 1) _
      (fun g ρ => vi_smul _ g ρ 1) β)
  have hZ : ZH (puAmalgam h.le) β ≤ ⊥ := hbot ▸ (zh_le_zm _ hαβ).trans hZα
  exact zh_ne_bot _ h20 hβ (le_bot_iff.mp hZ)

theorem not_commutator_vv_le_zm_gen (hb : 2 < critDist (puAmalgam h.le))
    {α β : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α) (hαβ : (puAmalgam h.le).treeGraph.Adj α β)
    {X : Subgroup (puAmalgam h.le).Universal} (hXβ : X ≤ Qv _ β) (hXα : ¬ X ≤ Qv _ α) :
    ¬ ⁅Vv (puAmalgam h.le) α, X⁆ ≤ ZM (puAmalgam h.le) α := fun hle =>
  not_commutator_vv_ltil_le_zm_gen h hb hα hαβ
    (commutator_vv_ltil_le_of_gen h hα hαβ hXβ hXα (stab_le_normalizer_zm _ α) hle)

theorem commutator_vv_le_of_ltil_gen (hb : 2 < critDist (puAmalgam h.le))
    {α : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α) {K : Subgroup (puAmalgam h.le).Universal}
    (hK : stab _ α ≤ Subgroup.normalizer (K : Set _))
    (hVL : ⁅Vv (puAmalgam h.le) α, Ltil h.le L α⁆ ≤ vvPerp α K) :
    ⁅Vv (puAmalgam h.le) α, Vv (puAmalgam h.le) α⁆ ≤ K := by
  have h20 := h.hyp20
  have hVs : Vv (puAmalgam h.le) α ≤ stab _ α :=
    (vv_le_qv h hb hα).trans (qv_le_stab _ α)
  have hKV : Vv (puAmalgam h.le) α ≤ Subgroup.normalizer (K : Set _) := hVs.trans hK
  set Ut := vvPerp (X := puAmalgam h.le) α K with hUt
  have hUtV : Ut ≤ Vv _ α := vvPerp_le α K
  have hUtn : stab (puAmalgam h.le) α ≤ Subgroup.normalizer (Ut : Set _) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    have key : ∀ y ∈ stab (puAmalgam h.le) α, ∀ v ∈ Ut, y * v * y⁻¹ ∈ Ut := by
      intro y hy v hv
      rw [mem_vvPerp_iff hKV] at hv ⊢
      have hVn := stab_le_normalizer_vv h α
      refine ⟨(Subgroup.mem_normalizer_iff.mp (hVn hy) v).mp hv.1, fun w hw => ?_⟩
      have hw' : y⁻¹ * w * y⁻¹⁻¹ ∈ Vv (puAmalgam h.le) α :=
        (Subgroup.mem_normalizer_iff.mp (hVn (Subgroup.inv_mem _ hy)) w).mp hw
      have e : ⁅y * v * y⁻¹, w⁆ = y * ⁅v, y⁻¹ * w * y⁻¹⁻¹⁆ * y⁻¹ := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact (Subgroup.mem_normalizer_iff.mp (hK hy) _).mp (hv.2 _ hw')
    intro v
    constructor
    · exact key g hg v
    · intro hv
      have := key g⁻¹ (Subgroup.inv_mem _ hg) _ hv
      simpa [mul_assoc] using this
  have hZ : ∀ ρ₀ μ : Vtx (puAmalgam h.le), (puAmalgam h.le).treeGraph.Adj α ρ₀ →
      (puAmalgam h.le).treeGraph.Adj ρ₀ μ → ZM (puAmalgam h.le) μ ≤ Ut := by
    intro ρ₀ μ hαρ hρμ
    have hμM : IsMVtx (puAmalgam h.le) μ := by
      have h1 := (isMVtx_iff_of_adj _ hαρ).mp hα
      have h2 := isMVtx_iff_of_adj _ hρμ
      tauto
    have hZV : ZM (puAmalgam h.le) μ ≤ Vv _ α := by
      have hd : (puAmalgam h.le).treeGraph.dist α μ ≤ 2 := by
        have := dist_triangle _ α ρ₀ μ
        rw [dist_eq_one_of_adj _ hαρ, dist_eq_one_of_adj _ hρμ] at this
        omega
      have : Zv (puAmalgam h.le) μ ≤ Vv _ α := le_iSup₂_of_le (f := fun x (_ : x ∈
        {x : Vtx (puAmalgam h.le) | (puAmalgam h.le).treeGraph.dist α x ≤ 2}) =>
          Zv (puAmalgam h.le) x) μ hd le_rfl
      rwa [zv_of_isMVtx _ hμM] at this
    set W := ZM (puAmalgam h.le) μ ⊔ Ut with hW
    have hWn : stab (puAmalgam h.le) α ≤ Subgroup.normalizer (W : Set _) := by
      rw [S34F.stab_eq_ltil_sup_qv_gen h hα hαρ]
      refine sup_le ?_ ?_
      · rw [Subgroup.le_normalizer_iff_commutator_le_left]
        refine S4A.commutator_sup_le_of ?_ ?_ ?_ ?_
        · exact ((Subgroup.commutator_mono hZV le_rfl).trans hVL).trans le_sup_right
        · exact (Subgroup.le_normalizer_iff_commutator_le_left.mp
            ((ltil_le_stab h α).trans hUtn)).trans le_sup_right
        · exact le_sup_left.trans Subgroup.le_normalizer
        · exact le_sup_right.trans Subgroup.le_normalizer
      · have hTμ : Qv (puAmalgam h.le) ρ₀ ≤ stab _ μ := qv_le_stab_of_adj _ hρμ
        have hTα : Qv (puAmalgam h.le) ρ₀ ≤ stab _ α := qv_le_stab_of_adj _ hαρ.symm
        exact (le_inf (hTμ.trans (stab_le_normalizer_zm _ μ)) (hTα.trans hUtn)).trans
          (Subgroup.inf_normalizer_le_normalizer_sup _ _)
    have hρ : ∀ ρ ∈ (puAmalgam h.le).treeGraph.neighborSet α,
        ⁅ZM (puAmalgam h.le) μ, Vv _ ρ⁆ ≤ K := by
      intro ρ hρ
      obtain ⟨g, hg, hgρ⟩ := exists_mem_stab_smul _ hαρ hρ
      have hgμ : (puAmalgam h.le).treeGraph.Adj ρ (g • μ) := by
        rw [← hgρ]; exact (adj_smul _ g _ _).mpr hρμ
      have hle : ZM (puAmalgam h.le) μ ≤ Vv _ ρ ⊔ Ut := by
        have h1 : ZM (puAmalgam h.le) μ ≤ W.map (MulAut.conj g).toMonoidHom := by
          rw [map_conj_eq_of_mem_normalizer (hWn hg)]
          exact le_sup_left
        refine h1.trans ?_
        rw [hW, Subgroup.map_sup, ← zm_smul, map_conj_eq_of_mem_normalizer (hUtn hg)]
        have hgμM : IsMVtx (puAmalgam h.le) (g • μ) := (isMVtx_smul _ g μ).mpr hμM
        exact sup_le_sup_right (zm_le_vv_of_adj hgμ hgμM) _
      have hVρab := vv_le_centralizer_of_not_isMVtx h20 hb (ρ := ρ)
        (by have := isMVtx_iff_of_adj _ hρ; tauto)
      have hVρα : Vv (puAmalgam h.le) ρ ≤ Vv _ α := by
        rw [vv_eq_iSup_vv hα]
        exact le_iSup₂_of_le (f := fun ρ (_ : ρ ∈ (puAmalgam h.le).treeGraph.neighborSet α) =>
          Vv (puAmalgam h.le) ρ) ρ hρ le_rfl
      refine (Subgroup.commutator_mono hle le_rfl).trans ?_
      refine S4A.commutator_sup_le_of ?_ ?_ ((hVρα.trans hKV)) (hUtV.trans hKV)
      · rw [(Subgroup.commutator_eq_bot_iff_le_centralizer).mpr hVρab]
        exact bot_le
      · rw [Subgroup.commutator_le]
        intro u hu w hw
        exact ((mem_vvPerp_iff hKV).mp hu).2 w (hVρα hw)
    have hVρα' : ∀ ρ ∈ (puAmalgam h.le).treeGraph.neighborSet α,
        Vv (puAmalgam h.le) ρ ≤ Vv _ α := fun ρ hρ => by
      rw [vv_eq_iSup_vv hα]
      exact le_iSup₂_of_le (f := fun ρ (_ : ρ ∈ (puAmalgam h.le).treeGraph.neighborSet α) =>
        Vv (puAmalgam h.le) ρ) ρ hρ le_rfl
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

end CFSG.Quasithin.MS93.S34G
