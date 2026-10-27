module

public import CFSG.Quasithin.MS93.S4A43Stmt
public import CFSG.Quasithin.MS93.S4A42i

public section

namespace CFSG.Quasithin.MS93.S4A

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

section TwoGroup

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem finrank_commN_le_two {S : Subgroup (SL3 F)} (hS : IsPGroup 2 S) :
    Module.finrank F (commN S) ≤ 2 := by
  obtain ⟨x, hx⟩ := exists_conj_le_sStar hS
  rw [← finrank_commN_map_conj x S, ← finrank_ln01 (F := F)]
  exact Submodule.finrank_mono (commN_le_ln01_of_le_sStar hx)

theorem card_commN_le_sq {S : Subgroup (SL3 F)} (hS : IsPGroup 2 S) :
    Nat.card ↥(commN S) ≤ Nat.card F ^ 2 := by
  have h1 : Nat.card ↥(commN S) = Nat.card F ^ Module.finrank F (commN S) :=
    Module.natCard_eq_pow_finrank
  rw [h1]
  exact Nat.pow_le_pow_right Nat.card_pos (finrank_commN_le_two hS)

end TwoGroup

section Kernel

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
  (hfull : IsSL3Full M T L)
include h hfull

theorem commutator_vv_ltil_le_of {α β : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α)
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
  have hKn : stab (puAmalgam h.le) α ≤ Subgroup.normalizer (K : Set (puAmalgam h.le).Universal) := by
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
    exact le_qv_of_commutator_le h hfull hα hαβ hXβ
      ((Subgroup.commutator_mono hXK le_rfl).trans h3)
  · rw [Subgroup.commutator_le]
    intro v hv l hl
    exact (hJK (hc hl)).2 v hv

theorem vv_le_vi_sup_commutator {α β : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α)
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
      rw [stab_eq_ltil_sup_qv_adj h hfull hα hαβ] at hg
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

theorem vv_eq_vi_one {α β : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α)
    (hαβ : (puAmalgam h.le).treeGraph.Adj α β)
    (hle : ⁅Vv (puAmalgam h.le) α, Ltil h.le L α⁆ ≤ Vi (puAmalgam h.le) β 1) :
    Vv (puAmalgam h.le) α = Vi (puAmalgam h.le) β 1 := by
  refine le_antisymm ((vv_le_vi_sup_commutator h hfull hα hαβ).trans (sup_le le_rfl hle)) ?_
  refine iSup₂_le fun ρ hρ => zv_le_vv h ?_
  have := dist_triangle (puAmalgam h.le) α β ρ
  rw [(SimpleGraph.dist_eq_one_iff_adj).mpr hαβ] at this
  exact this.trans (by simp only [Set.mem_ofPred_eq] at hρ; omega)

theorem not_commutator_vv_ltil_le_zm (hb : 2 < critDist (puAmalgam h.le))
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
  have heq := vv_eq_vi_one h hfull hα hαβ (hle.trans hZα)
  have hViQ : Vi (puAmalgam h.le) β 1 ≤ Qv _ β := by
    rw [← heq]
    exact (vv_le_qv h hb hα).trans (qv_le_qv _ h20 hα hαβ)
  have hbot := ms21_iii _ h20 hα hαβ hViQ (heq ▸ stab_le_normalizer_vv h α)
    (stab_le_normalizer_of_smul (F := fun ρ => Vi (puAmalgam h.le) ρ 1) _
      (fun g ρ => vi_smul _ g ρ 1) β)
  have hZ : ZH (puAmalgam h.le) β ≤ ⊥ := hbot ▸ (zh_le_zm _ hαβ).trans hZα
  exact zh_ne_bot _ h20 hβ (le_bot_iff.mp hZ)

theorem not_commutator_vv_le_zm (hb : 2 < critDist (puAmalgam h.le))
    {α β : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α) (hαβ : (puAmalgam h.le).treeGraph.Adj α β)
    {X : Subgroup (puAmalgam h.le).Universal} (hXβ : X ≤ Qv _ β) (hXα : ¬ X ≤ Qv _ α) :
    ¬ ⁅Vv (puAmalgam h.le) α, X⁆ ≤ ZM (puAmalgam h.le) α := fun hle =>
  not_commutator_vv_ltil_le_zm h hfull hb hα hαβ
    (commutator_vv_ltil_le_of h hfull hα hαβ hXβ hXα (stab_le_normalizer_zm _ α) hle)

end Kernel

section I

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
include h

theorem concl431_i_ii (hC : CentHyp (puAmalgam h.le)) {F : Type} [Field F] [Fintype F]
    {φ : ↥M →* ↥(StatedSL 3 F)} (hφ : IsSL3FullVia M T L φ)
    (hb : 2 < critDist (puAmalgam h.le)) {α α' : Vtx (puAmalgam h.le)}
    (hs : Star (puAmalgam h.le) α α') :
    critR0 (puAmalgam h.le) α α' = Usup (puAmalgam h.le) α' (geo (puAmalgam h.le) α' α 1) ∧
      Nat.card ↥(critR0 (puAmalgam h.le) α α') = Nat.card F ^ 2 ∧
      Nat.card ↥(critR (puAmalgam h.le) α α') = Nat.card F := by
  obtain ⟨hc, hstar⟩ := hs
  have h20 := h.hyp20
  have hb0 := h.critDist_pos
  have hfull : IsSL3Full M T L :=
    isSL3Full_iff_exists_via.mpr ⟨F, inferInstance, inferInstance, φ, hφ⟩
  obtain ⟨n, hn⟩ := hφ.1
  have hFn : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card, hn]
  have : CharP F 2 := FFC.charP_two_of_card_pow hFn
  have hq : 2 ≤ Nat.card F := Finite.one_lt_card
  have hc' := ms22_iii _ h20 hb0 hC hc
  have hα := hc.1
  have hα' := hc'.1
  have hd : (puAmalgam h.le).treeGraph.dist α' α = critDist (puAmalgam h.le) := hc'.2.1
  have hα'β' : (puAmalgam h.le).treeGraph.Adj α' (geo (puAmalgam h.le) α' α 1) :=
    adj_geo_one_of_isCritical _ hb0 hc'
  have hβ'γ' : (puAmalgam h.le).treeGraph.Adj (geo (puAmalgam h.le) α' α 1)
      (geo (puAmalgam h.le) α' α 2) := adj_geo _ (i := 1) (by omega)
  have hγ' : IsMVtx (puAmalgam h.le) (geo (puAmalgam h.le) α' α 2) :=
    isMVtx_geo_two _ h20 hb0 hc'
  have hβ'H : ¬ IsMVtx (puAmalgam h.le) (geo (puAmalgam h.le) α' α 1) := by
    rw [← isMVtx_iff_of_adj _ hα'β']
    exact hα'
  have hVβ' : Vv (puAmalgam h.le) α ≤ Qv _ (geo (puAmalgam h.le) α' α 1) :=
    hstar.trans (qv_le_qv _ h20 hγ' hβ'γ'.symm)
  have hβ's : Qv (puAmalgam h.le) (geo (puAmalgam h.le) α' α 1) ≤ stab _ α' :=
    qv_le_stab_of_adj _ hα'β'.symm
  have hVs' : Vv (puAmalgam h.le) α ≤ stab _ α' := hVβ'.trans hβ's
  have hfin : Finite ↥(Qv (puAmalgam h.le) (geo (puAmalgam h.le) α' α 1)) := finite_qv _ h20 hβ'H
  have hT2 := isPGroup_qv _ h20 hβ'H
  obtain ⟨ψ', -, hψ'⟩ := exists_natural_Uloc h hφ hα'
  obtain ⟨ψ, -, hψ⟩ := exists_natural_Uloc h hφ hα
  have hnat2 : ∀ {A : Subgroup (puAmalgam h.le).Universal},
      A ≤ Qv (puAmalgam h.le) (geo (puAmalgam h.le) α' α 1) → IsPGroup 2 ↥(natImage ψ' A) := by
    intro A hA
    have h1 : IsPGroup 2 ↥(A.subgroupOf (stab (puAmalgam h.le) α')) :=
      (hT2.to_le hA).of_equiv (Subgroup.subgroupOfEquivOfLe (hA.trans hβ's)).symm
    exact h1.map _
  have hZ's : ZM (puAmalgam h.le) α' ≤ stab _ α := zm_le_stab_right _ h20 hb0 hC hc'
  have hR0V : critR0 (puAmalgam h.le) α α' ≤ Vv _ α :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp
      (hZ's.trans (stab_le_normalizer_vv h α))
  have hR0 : critR0 (puAmalgam h.le) α α' = ⁅Uloc h.le L α', Vv (puAmalgam h.le) α⁆ := by
    rw [critR0, Subgroup.commutator_comm, commutator_zm_eq_uloc h hfull hα' hVs']
  have hR0card : Nat.card ↥(critR0 (puAmalgam h.le) α α') =
      Nat.card F ^ Module.finrank F (commN (natImage ψ' (Vv (puAmalgam h.le) α))) := by
    rw [hR0, card_commutator_eq hψ' hVs']
    exact Module.natCard_eq_pow_finrank
  have hRcard : Nat.card ↥(critR (puAmalgam h.le) α α') =
      Nat.card F ^ Module.finrank F (commN (natImage ψ' (ZM (puAmalgam h.le) α))) := by
    have := card_commN_eq_card_critR h hfull hc' hψ'
    rw [critR, Subgroup.commutator_comm, ← critR, ← this]
    exact Module.natCard_eq_pow_finrank
  have hEne : natImage ψ' (ZM (puAmalgam h.le) α) ≠ ⊥ :=
    (s35_core h hC hφ hc' hψ' hψ).2.2.2.2.2
  have hc1 : 1 ≤ Module.finrank F (commN (natImage ψ' (ZM (puAmalgam h.le) α))) := by
    rw [Nat.one_le_iff_ne_zero, Ne, Submodule.finrank_eq_zero]
    exact commN_ne_bot hEne
  have ha2 : Module.finrank F (commN (natImage ψ' (Vv (puAmalgam h.le) α))) ≤ 2 :=
    finrank_commN_le_two (hnat2 hVβ')
  have hRle : critR (puAmalgam h.le) α α' ≤ critR0 _ α α' :=
    Subgroup.commutator_mono (zm_le_vv h hα) le_rfl
  have hfinR0 : Finite ↥(critR0 (puAmalgam h.le) α α') :=
    Finite.of_injective _ (Subgroup.inclusion_injective (hR0V.trans hVβ'))
  have hca : Module.finrank F (commN (natImage ψ' (ZM (puAmalgam h.le) α))) ≤
      Module.finrank F (commN (natImage ψ' (Vv (puAmalgam h.le) α))) := by
    have := Subgroup.card_le_of_le hRle
    rw [hRcard, hR0card] at this
    exact (Nat.pow_le_pow_iff_right hq).mp this
  have hne : Module.finrank F (commN (natImage ψ' (ZM (puAmalgam h.le) α))) ≠
      Module.finrank F (commN (natImage ψ' (Vv (puAmalgam h.le) α))) := by
    intro heq
    have hRR0 : critR (puAmalgam h.le) α α' = critR0 _ α α' :=
      Subgroup.eq_of_le_of_card_ge hRle (by rw [hRcard, hR0card, heq])
    apply not_commutator_vv_le_zm h hfull hb hα (adj_geo_one_of_isCritical _ hb0 hc)
      (zm_le_qv_geo_one _ h20 hb0 hc) hc'.2.2
    rw [← critR0, ← hRR0, critR]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp
      (hZ's.trans (stab_le_normalizer_zm _ α))
  have hc_eq : Module.finrank F (commN (natImage ψ' (ZM (puAmalgam h.le) α))) = 1 := by omega
  have ha_eq : Module.finrank F (commN (natImage ψ' (Vv (puAmalgam h.le) α))) = 2 := by omega
  have hR0q : Nat.card ↥(critR0 (puAmalgam h.le) α α') = Nat.card F ^ 2 := by
    rw [hR0card, ha_eq]
  have hR0U : critR0 (puAmalgam h.le) α α' ≤
      Usup (puAmalgam h.le) α' (geo (puAmalgam h.le) α' α 1) := by
    rw [critR0, Usup, zv_of_isMVtx _ hα', Subgroup.commutator_comm]
    exact Subgroup.commutator_mono le_rfl hVβ'
  have hUcard : Nat.card ↥(Usup (puAmalgam h.le) α' (geo (puAmalgam h.le) α' α 1)) ≤
      Nat.card F ^ 2 := by
    rw [usup_eq_commutator_uloc h hfull hα' hα'β', card_commutator_eq hψ' hβ's]
    exact card_commN_le_sq (hnat2 le_rfl)
  have hfinU : Finite ↥(Usup (puAmalgam h.le) α' (geo (puAmalgam h.le) α' α 1)) := by
    have hUQ : Usup (puAmalgam h.le) α' (geo (puAmalgam h.le) α' α 1) ≤
        Qv _ (geo (puAmalgam h.le) α' α 1) := by
      rw [Usup, zv_of_isMVtx _ hα']
      exact commutator_le_of_le ((zm_le_qv_self _ hα' hb0).trans (qv_le_qv _ h20 hα' hα'β'))
        le_rfl
    exact Finite.of_injective _ (Subgroup.inclusion_injective hUQ)
  refine ⟨Subgroup.eq_of_le_of_card_ge hR0U (hUcard.trans hR0q.ge), hR0q, ?_⟩
  rw [hRcard, hc_eq, pow_one]

end I

end CFSG.Quasithin.MS93.S4A
