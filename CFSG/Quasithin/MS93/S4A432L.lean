module

public import CFSG.Quasithin.MS93.S4A432K
public import CFSG.Quasithin.MS93.ML3PairDual
import CFSG.Quasithin.MS93.S45Vtx
import CFSG.Quasithin.MS93.S45Path

public section

namespace CFSG.Quasithin.MS93.S4A.D432

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

section Lines

variable {F : Type} [Field F]

theorem exists_map_eq_of_finrank_eq {P H : Submodule F (Fin 3 → F)}
    (hPH : Module.finrank F P = Module.finrank F H) :
    ∃ s : SL3 F, P.map (Matrix.SpecialLinearGroup.toLin' s : (Fin 3 → F) →ₗ[F] (Fin 3 → F)) =
      H := by
  obtain ⟨g₁, hg₁⟩ := CFSG.LocalAnalysis.ComponentInitial.LinearFlag.exists_map_flagSpace_eq P
  obtain ⟨g₂, hg₂⟩ := CFSG.LocalAnalysis.ComponentInitial.LinearFlag.exists_map_flagSpace_eq H
  rw [← hPH] at hg₂
  generalize Module.finrank F P = d at hg₁ hg₂
  refine ⟨g₂ * g₁⁻¹, ?_⟩
  have hlin : ∀ g : SL3 F, ((Matrix.SpecialLinearGroup.toLin' g : (Fin 3 → F) ≃ₗ[F] (Fin 3 → F)) :
      (Fin 3 → F) →ₗ[F] (Fin 3 → F)) =
        Matrix.mulVecLin ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) := by
    intro g
    ext x
    simp [Matrix.SpecialLinearGroup.toLin'_apply, Matrix.toLin'_apply]
  rw [hlin, ← hg₁, ← hg₂, ← Submodule.map_comp, ← Matrix.mulVecLin_mul, ← coe_mul_SL3,
    inv_mul_cancel_right]

end Lines

section Smul

universe u v

variable {A B : Type u} {C : Type v} [Group A] [Group C] [Group B] (X : GoldAmalgam A C B)

theorem critR_smul' (g : X.Universal) (δ δ' : Vtx X) :
    critR X (g • δ) (g • δ') = (critR X δ δ').map (MulAut.conj g).toMonoidHom := by
  rw [critR, critR, zm_smul, zm_smul, Subgroup.map_commutator]

theorem usup_ne_smul {α α' : Vtx X} (g : X.Universal)
    (h4 : Usup X (geo X α' α 2) (geo X α' α 1) ≠ Usup X (geo X α' α 2) (geo X α' α 3)) :
    Usup X (geo X (g • α') (g • α) 2) (geo X (g • α') (g • α) 1) ≠
      Usup X (geo X (g • α') (g • α) 2) (geo X (g • α') (g • α) 3) := by
  rw [geo_smul, geo_smul, geo_smul, usup_smul, usup_smul]
  intro heq
  exact h4 (Subgroup.map_injective (MulAut.conj g).injective heq)

end Smul

namespace Ctx

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} {h : PUHyp M T L}
  {F : Type} [Field F] [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)}
  {α₀ α₀' : Vtx (puAmalgam h.le)} (c : Ctx h φ α₀ α₀')
include c

local notation "𝔛" => puAmalgam h.le
local notation "𝔘" => GoldAmalgam.Universal (puAmalgam h.le)
local notation "𝔄" => SimpleGraph.Adj (GoldAmalgam.treeGraph (puAmalgam h.le))

theorem exists_good_star {γ ν : Vtx 𝔛} (hγ : IsMVtx 𝔛 γ) (hγν : 𝔄 γ ν) :
    ∃ γ' : Vtx 𝔛, Star 𝔛 γ γ' ∧
      Usup 𝔛 (geo 𝔛 γ' γ 2) (geo 𝔛 γ' γ 1) ≠ Usup 𝔛 (geo 𝔛 γ' γ 2) (geo 𝔛 γ' γ 3) ∧
      ¬ critR 𝔛 γ γ' ≤ Usup 𝔛 γ ν := by
  classical
  have hq : 2 ≤ Nat.card F := Finite.one_lt_card
  obtain ⟨α₁, hs₁, h4₁⟩ := c.exists_star_ne
  obtain ⟨g, hg⟩ := exists_smul_eq_of_isMVtx _ c.star.1.1 hγ
  have hs₂ : Star 𝔛 γ (g • α₁) := by rw [← hg]; exact (star_smul _ g α₀ α₁).mpr hs₁
  have h4₂ := usup_ne_smul _ g h4₁
  rw [hg] at h4₂
  set γ₁ := g • α₁ with hγ₁
  obtain ⟨ψ, hψs, hψ⟩ := exists_natural_Uloc h c.hyp.2.2 hγ
  have hZs : ZM 𝔛 γ₁ ≤ stab 𝔛 γ :=
    zm_le_stab_of_isCritical _ h.hyp20 h.critDist_pos hs₂.1
  have hTs : Qv 𝔛 ν ≤ stab 𝔛 γ := qv_le_stab_of_adj _ hγν.symm
  have hr1 : Module.finrank F ↥(commN (natImage ψ (ZM 𝔛 γ₁))) = 1 := by
    have hcR := (c.s431A G M T L h F inferInstance inferInstance φ c.hyp γ γ₁ hs₂).2.2.1
    rw [critR, commutator_zm_eq_uloc h c.full hγ hZs, card_commutator_eq hψ hZs,
      Module.natCard_eq_pow_finrank (K := F), ← Nat.card_eq_fintype_card] at hcR
    exact Nat.pow_right_injective hq (hcR.trans (pow_one _).symm)
  have hP2 : Module.finrank F ↥(commN (natImage ψ (Qv 𝔛 ν))) = 2 := by
    have := (c.edge hγ hγν).2.1
    rw [usup_eq_commutator_uloc h c.full hγ hγν, card_commutator_eq hψ hTs,
      Module.natCard_eq_pow_finrank (K := F), ← Nat.card_eq_fintype_card] at this
    exact Nat.pow_right_injective hq this
  obtain ⟨w, hw⟩ : ∃ w, w ∉ commN (natImage ψ (Qv 𝔛 ν)) := by
    by_contra hcon
    push Not at hcon
    have htop : commN (natImage ψ (Qv 𝔛 ν)) = ⊤ := eq_top_iff.mpr fun v _ => hcon v
    rw [htop, finrank_top, Module.finrank_fin_fun] at hP2
    omega
  have hw0 : w ≠ 0 := fun h0 => hw (h0 ▸ Submodule.zero_mem _)
  obtain ⟨s, hs⟩ := exists_map_eq_of_finrank_eq (P := commN (natImage ψ (ZM 𝔛 γ₁)))
    (H := Submodule.span F {w}) (by rw [hr1, finrank_span_singleton hw0])
  obtain ⟨k, hk⟩ := toSL3_surjective hψs s
  have hkγ : (k : 𝔘) • γ = γ := (mem_stab _).mp k.2
  have hks : Star 𝔛 γ ((k : 𝔘) • γ₁) := by
    have := (star_smul _ (k : 𝔘) γ γ₁).mpr hs₂
    generalize (k : 𝔘) = k' at this hkγ
    rwa [hkγ] at this
  have hk4 := usup_ne_smul _ (k : 𝔘) h4₂
  have hkR : critR 𝔛 γ ((k : 𝔘) • γ₁) = (critR 𝔛 γ γ₁).map (MulAut.conj (k : 𝔘)).toMonoidHom := by
    have := critR_smul' _ (k : 𝔘) γ γ₁
    generalize (k : 𝔘) = k' at this hkγ
    rwa [hkγ] at this
  refine ⟨(k : 𝔘) • γ₁, hks, ?_, ?_⟩
  · generalize (k : 𝔘) = k' at hk4 hkγ
    rwa [hkγ] at hk4
  · intro hle
    rw [hkR] at hle
    apply hw
    have hwr : w ∈ (commN (natImage ψ (ZM 𝔛 γ₁))).map
        (Matrix.SpecialLinearGroup.toLin' s : (Fin 3 → F) →ₗ[F] (Fin 3 → F)) := by
      rw [hs]; exact Submodule.mem_span_singleton_self w
    obtain ⟨y, hy, rfl⟩ := hwr
    obtain ⟨u, rfl⟩ := natVec_surjective hψ y
    have hu : (u : 𝔘) ∈ critR 𝔛 γ γ₁ := by
      rw [critR, commutator_zm_eq_uloc h c.full hγ hZs]
      exact (mem_commutator_iff_natVec hψ hZs u).mpr hy
    have hku : (k : 𝔘) * u * (k : 𝔘)⁻¹ ∈ Usup 𝔛 γ ν := hle ⟨u, hu, rfl⟩
    have hkuU : (k : 𝔘) * u * (k : 𝔘)⁻¹ ∈ Uloc h.le L γ :=
      (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_puTrans h.le (S4A.Uq_normal h) γ k.2)
        u).mp u.2
    rw [usup_eq_commutator_uloc h c.full hγ hγν] at hku
    have h1 := (mem_commutator_iff_natVec hψ hTs ⟨_, hkuU⟩).mp hku
    rw [natVec_conj hψ k u ⟨_, hkuU⟩ rfl, hk] at h1
    simpa [Matrix.SpecialLinearGroup.toLin'_apply, Matrix.toLin'_apply] using h1

theorem stab_le_normalizer_pv_sup' (hb6 : 6 < critDist 𝔛) {γ ν μ : Vtx 𝔛} (hγ : IsMVtx 𝔛 γ)
    (hγν : 𝔄 γ ν) (hνμ : 𝔄 ν μ) (hμ : μ ∈ nablaSet h.le L γ) :
    stab 𝔛 γ ≤ Subgroup.normalizer ((Pv 𝔛 μ ⊔ Vv 𝔛 γ : Subgroup 𝔘) : Set 𝔘) := by
  obtain ⟨γ', hs, h4, hR⟩ := c.exists_good_star hγ hγν
  exact c.stab_le_normalizer_pv_sup hb6 hs h4 hγν hR ⟨ν, hγν, hνμ, hμ, rfl⟩

theorem commutator_pv_qv_le_zm' (hb6 : 6 < critDist 𝔛) {γ ν μ : Vtx 𝔛} (hγ : IsMVtx 𝔛 γ)
    (hγν : 𝔄 γ ν) (hνμ : 𝔄 ν μ) (hμ : μ ∈ nablaSet h.le L γ) : ⁅Pv 𝔛 μ, Qv 𝔛 γ⁆ ≤ ZM 𝔛 γ := by
  obtain ⟨γ', hs, h4, hR⟩ := c.exists_good_star hγ hγν
  exact c.commutator_pv_qv_le_zm hb6 hs h4 hγν hR ⟨ν, hγν, hνμ, hμ, rfl⟩

theorem zm_le_pv' (hb6 : 6 < critDist 𝔛) {γ ν μ : Vtx 𝔛} (hγ : IsMVtx 𝔛 γ) (hγν : 𝔄 γ ν)
    (hνμ : 𝔄 ν μ) (hμ : μ ∈ nablaSet h.le L γ) : ZM 𝔛 γ ≤ Pv 𝔛 μ := by
  obtain ⟨γ', hs, h4, hR⟩ := c.exists_good_star hγ hγν
  exact c.zm_le_pv_of_mem hb6 hs h4 hγν hR ⟨ν, hγν, hνμ, hμ, rfl⟩

theorem exists_edge_coords {μ ν : Vtx 𝔛} (hμ : IsMVtx 𝔛 μ) (hμν : 𝔄 μ ν) :
    ∃ ψ : ↥(stab 𝔛 μ) →* ↥(StatedSL 3 F), Function.Surjective ψ ∧
      IsSumOfNaturalModulesVia (stab 𝔛 μ) (Uloc h.le L μ) ⊥ ψ false 1 ∧
      IsSumOfNaturalModulesVia (stab 𝔛 μ) (Pv 𝔛 μ) (ZM 𝔛 μ) ψ true 1 ∧
      ∀ t : ↥(stab 𝔛 μ), (t : 𝔘) ∈ Qv 𝔛 ν → ∀ p : Fin 3 → F, p 0 = 0 →
        ((toSL3 ψ t : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ p = p := by
  have hq : 2 ≤ Nat.card F := Finite.one_lt_card
  have hTs : Qv 𝔛 ν ≤ stab 𝔛 μ := qv_le_stab_of_adj _ hμν.symm
  obtain ⟨hUZ, hUq, -, hrel⟩ := c.edge hμ hμν
  obtain ⟨ψ, hψs, hU, hP⟩ := c.exists_dual hμ
  have hfin : Module.finrank F ↥(commN (natImage ψ (Qv 𝔛 ν))) = 2 := by
    have := hUq
    rw [usup_eq_commutator_uloc h c.full hμ hμν, card_commutator_eq hU hTs,
      Module.natCard_eq_pow_finrank (K := F), ← Nat.card_eq_fintype_card] at this
    exact Nat.pow_right_injective hq this
  have hfin0 : Module.finrank F ↥(coordZero 0 : Submodule F (Fin 3 → F)) = 2 := by
    have := card_coordZero_zero (F := F)
    rw [Module.natCard_eq_pow_finrank (K := F)] at this
    exact Nat.pow_right_injective hq this
  obtain ⟨s, hs⟩ := exists_map_plane_eq hfin hfin0
  have hU' := isSumOfNaturalModulesVia_conjSL hU s
  have hcomm : commN (natImage (conjSL s ψ) (Qv 𝔛 ν)) = coordZero 0 := by
    rw [natImage_conjSL', commN_map_conj, hs]
  have hTQ : ¬ Qv 𝔛 ν ≤ Qv 𝔛 μ := by
    intro hle
    have h1 := Subgroup.relIndex_eq_one.mpr hle
    rw [hrel] at h1
    have hq' : 2 ≤ Fintype.card F := Fintype.one_lt_card
    have : 1 < Fintype.card F ^ 2 := Nat.one_lt_pow (by norm_num) (by omega)
    omega
  have hfixN : fixN (natImage (conjSL s ψ) (Qv 𝔛 ν)) = coordZero 0 := by
    rw [fixN_eq_commN_of_le_qv h c.full c.hyp.2.2 hμ hμν hUZ hUq hU' le_rfl hTQ, hcomm]
  refine ⟨conjSL s ψ, conjSL_surjective hψs, hU', isSumOfNaturalModulesVia_conjSL_true hP s,
    fun t ht p hp => ?_⟩
  have hp' : p ∈ fixN (natImage (conjSL s ψ) (Qv 𝔛 ν)) := by rw [hfixN]; exact hp
  exact mem_fixN.mp hp' _ (mem_natImage.mpr ⟨t, ht, rfl⟩)

omit [Fintype F] c in
theorem coord_commutator_mem_pt0 {μ ν : Vtx 𝔛} {ψ : ↥(stab 𝔛 μ) →* ↥(StatedSL 3 F)}
    (N : NatSec (stab 𝔛 μ) (Pv 𝔛 μ) (ZM 𝔛 μ) (dualSL ψ) false)
    (hfix : ∀ t : ↥(stab 𝔛 μ), (t : 𝔘) ∈ Qv 𝔛 ν → ∀ p : Fin 3 → F, p 0 = 0 →
      ((toSL3 ψ t : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ p = p)
    {x : 𝔘} (hx : x ∈ Pv 𝔛 μ) (t : ↥(stab 𝔛 μ)) (ht : (t : 𝔘) ∈ Qv 𝔛 ν) :
    N.coord ⁅x, (t : 𝔘)⁆ ∈ pt0 := by
  have htx : (t : 𝔘) * x⁻¹ * (t : 𝔘)⁻¹ ∈ Pv 𝔛 μ := N.conj_mem t (Subgroup.inv_mem _ hx)
  have e : ⁅x, (t : 𝔘)⁆ = x * ((t : 𝔘) * x⁻¹ * (t : 𝔘)⁻¹) := by
    simp only [commutatorElement_def]; group
  have hDj : ∀ v : Fin 3 → F, ∀ j : Fin 3, j ≠ 0 →
      (dualMat (toSL3 ψ t) *ᵥ v) j = v j := by
    intro v j hj
    have h1 := dualMat_mulVec_dotProduct (toSL3 ψ t) v (Pi.single j 1)
    rw [hfix t ht _ (by simp [hj.symm]), dotProduct_single, dotProduct_single, mul_one,
      mul_one] at h1
    exact h1
  rw [e, N.coord_mul hx htx, N.coord_conj t (Subgroup.inv_mem _ hx), N.coord_inv hx, natAct_false,
    toSL3_dualSL, coe_transposeInv, Matrix.mulVec_neg, mem_pt0]
  refine ⟨?_, ?_⟩
  · simp only [Pi.add_apply, Pi.neg_apply]
    rw [hDj _ 1 (by decide), add_neg_cancel]
  · simp only [Pi.add_apply, Pi.neg_apply]
    rw [hDj _ 2 (by decide), add_neg_cancel]

theorem false_of_ctx (hb6 : 6 < critDist 𝔛) : False := by
  classical
  have hq : 2 ≤ Nat.card F := Finite.one_lt_card
  have hb := hb6
  have h20 := h.hyp20
  have hb0 := h.critDist_pos
  have hs := c.star
  have hα := hs.1.1
  have hα' : IsMVtx 𝔛 α₀' := hs.1.isMVtx_right _ h20
  have hd : (puAmalgam h.le).treeGraph.dist α₀ α₀' = critDist 𝔛 := hs.1.2.1
  have hd' : (puAmalgam h.le).treeGraph.dist α₀' α₀ = critDist 𝔛 := by rw [tdist_comm]; exact hd
  set β := geo 𝔛 α₀ α₀' 1 with hβdef
  set δ₂ := geo 𝔛 α₀ α₀' 2 with hδ₂def
  set δ₃ := geo 𝔛 α₀ α₀' 3 with hδ₃def
  set γ := geo 𝔛 α₀' α₀ 2 with hγdef
  set τ := geo 𝔛 α₀' α₀ 3 with hτdef
  set ρ₀ := geo 𝔛 α₀' α₀ 1 with hρ₀def
  have hαβ : 𝔄 α₀ β := adj_geo_one _ (by omega)
  have hβδ₂ : 𝔄 β δ₂ := adj_geo _ (i := 1) (by omega)
  have hδ₂δ₃ : 𝔄 δ₂ δ₃ := adj_geo _ (i := 2) (by omega)
  have hδ₂M : IsMVtx 𝔛 δ₂ := (isMVtx_geo _ (by omega)).mpr ⟨fun _ => even_two, fun _ => hα⟩
  have hγM : IsMVtx 𝔛 γ := (isMVtx_geo _ (by omega)).mpr ⟨fun _ => even_two, fun _ => hα'⟩
  have hγτ : 𝔄 γ τ := adj_geo _ (i := 2) (by omega)
  have hρ₀γ : 𝔄 ρ₀ γ := adj_geo _ (i := 1) (by omega)
  have hα'ρ₀ : 𝔄 α₀' ρ₀ := adj_geo_one _ (by omega)
  have hτgeo : τ = geo 𝔛 α₀ α₀' (critDist 𝔛 - 3) := by
    rw [hτdef, ← geo_symm _ (show critDist 𝔛 - 3 ≤ (puAmalgam h.le).treeGraph.dist α₀ α₀' by
      omega), hd]
    congr 1
    omega
  have hdδ₃τ : (puAmalgam h.le).treeGraph.dist δ₃ τ = critDist 𝔛 - 6 := by
    rw [hτgeo, hδ₃def, dist_geo_geo _ (by omega) (by omega)]
    omega
  have hdδ₂τ : (puAmalgam h.le).treeGraph.dist δ₂ τ = critDist 𝔛 - 5 := by
    rw [hτgeo, hδ₂def, dist_geo_geo _ (by omega) (by omega)]
    omega
  have hαn : α₀ ∈ nablaSet h.le L δ₂ := mem_nablaSet_geo_two h c.full c.cent c.b2 hs.1
  have hA := c.stab_le_normalizer_pv_sup' hb6 hδ₂M hβδ₂.symm hαβ.symm hαn
  obtain ⟨g, hg, hgβ⟩ := exists_mem_stab_smul _ hβδ₂.symm hδ₂δ₃
  have hgδ₂ : g • δ₂ = δ₂ := (mem_stab _).mp hg
  have hgα : 𝔄 δ₃ (g • α₀) := by
    have := (adj_smul _ g β α₀).mpr hαβ.symm
    rwa [hgβ] at this
  have hgαM : IsMVtx 𝔛 (g • α₀) := (isMVtx_smul _ g α₀).mpr hα
  have hPα : Pv 𝔛 α₀ ≤ Pv 𝔛 (g • α₀) ⊔ Vv 𝔛 δ₂ := by
    intro x hx
    have hx' : g⁻¹ * x * g⁻¹⁻¹ ∈ Pv 𝔛 α₀ ⊔ Vv 𝔛 δ₂ :=
      (Subgroup.mem_normalizer_iff.mp (hA (Subgroup.inv_mem _ hg)) x).mp
        (Subgroup.mem_sup_left hx)
    have hmap : (Pv 𝔛 α₀ ⊔ Vv 𝔛 δ₂).map (MulAut.conj g).toMonoidHom =
        Pv 𝔛 (g • α₀) ⊔ Vv 𝔛 δ₂ := by
      have hV : (Vv 𝔛 δ₂).map (MulAut.conj g).toMonoidHom = Vv 𝔛 (g • δ₂) :=
        (vi_smul _ g δ₂ 2).symm
      rw [Subgroup.map_sup, ← pv_smul, hV, hgδ₂]
    rw [← hmap]
    exact ⟨g⁻¹ * x * g⁻¹⁻¹, hx', by simp [mul_assoc]⟩
  have hdgα : (puAmalgam h.le).treeGraph.dist (g • α₀) τ ≤ critDist 𝔛 - 5 := by
    have h1 := dist_triangle (puAmalgam h.le) (g • α₀) δ₃ τ
    rw [tdist_comm _ (g • α₀) δ₃, dist_eq_one_of_adj _ hgα, hdδ₃τ] at h1
    omega
  have hPαc : Pv 𝔛 α₀ ≤ Subgroup.centralizer (Vv 𝔛 τ : Set 𝔘) := by
    refine hPα.trans (sup_le ((pv_le_vv h hgαM).trans ?_) ?_)
    · exact S45.vi_le_centralizer_vi _ h20 hb0 (by omega)
    · exact S45.vi_le_centralizer_vi _ h20 hb0 (by omega)
  obtain ⟨ε, hτε, hεn⟩ := exists_adj_mem_nablaSet_of_dual h c.full c.hyp c.cent c.s42 c.s431A
    c.s431B c.b4 c.star c.kind c.ch hγM hγτ
  have hεM := (zm_le_vv_of_mem_nablaSet h hγM hεn).1
  have hγnε : γ ∈ nablaSet h.le L ε := c.nabla_symm hγM hγτ hτε hεn
  set A₁ := ⁅Pv 𝔛 γ, Qv 𝔛 ε⁆ with hA₁def
  have hA₁Z : A₁ ≤ ZM 𝔛 ε := c.commutator_pv_qv_le_zm' hb6 hεM hτε.symm hγτ.symm hγnε
  have hA₁P : A₁ ≤ Pv 𝔛 γ := commutator_pv_qv_le_pv (h := h) hεM hτε.symm hγτ.symm
  set X := A₁ ⊔ ZM 𝔛 γ with hXdef
  have hXP : X ≤ Pv 𝔛 γ := sup_le hA₁P (zm_le_pv _ γ)
  have hZετ : ZM 𝔛 ε ≤ Vv 𝔛 τ := by
    have := zv_le_vv h (α := τ) (ρ := ε) (by rw [dist_eq_one_of_adj _ hτε]; norm_num)
    rwa [zv_of_isMVtx _ hεM] at this
  have hPαQγ : Pv 𝔛 α₀ ≤ Qv 𝔛 γ := (pv_le_vv h hα).trans hs.2
  have hXc : Pv 𝔛 α₀ ≤ Subgroup.centralizer (X : Set 𝔘) := by
    rw [Subgroup.le_centralizer_iff]
    refine sup_le ?_ ?_
    · exact Subgroup.le_centralizer_iff.mp
        (hPαc.trans (Subgroup.centralizer_le (hA₁Z.trans hZετ)))
    · exact (zm_le_centralizer_qv _ h20 hγM).trans (Subgroup.centralizer_le hPαQγ)
  obtain ⟨ψ, hψs, hU, hP, hfix⟩ := c.exists_edge_coords hγM hγτ
  set α₁ := dualSL ψ with hα₁
  have hα₁s : Function.Surjective α₁ := dualSL_surjective hψs
  have hZd : IsSumOfNaturalModulesVia (stab 𝔛 γ) (Uloc h.le L γ) ⊥ α₁ true 1 :=
    isSumOfNaturalModulesVia_dualSL hU
  have hPn : IsSumOfNaturalModulesVia (stab 𝔛 γ) (Pv 𝔛 γ) (ZM 𝔛 γ) α₁ false 1 :=
    isSumOfNaturalModulesVia_dualSL hP
  set N₁ := NatSec.ofIsSum hPn with hN₁
  have hTs : Qv 𝔛 τ ≤ stab 𝔛 γ := qv_le_stab_of_adj _ hγτ.symm
  have hQετ : Qv 𝔛 ε ≤ Qv 𝔛 τ := qv_le_qv _ h20 hεM hτε.symm
  have hQεs : Qv 𝔛 ε ≤ stab 𝔛 γ := hQετ.trans hTs
  obtain ⟨a, haQ, haQγ⟩ : ∃ a ∈ Qv 𝔛 ε, a ∉ Qv 𝔛 γ := by
    by_contra hcon
    push Not at hcon
    have h1 : ⁅ZM 𝔛 γ, Qv 𝔛 ε⁆ = ⊥ := by
      rw [eq_bot_iff, ← (Subgroup.commutator_eq_bot_iff_le_centralizer).mpr
        (zm_le_centralizer_qv _ h20 hγM)]
      exact Subgroup.commutator_mono le_rfl hcon
    have h2 := (c.edge hεM hτε.symm).2.1
    rw [← (c.three hεM hτε.symm hγτ.symm hγnε).1, h1, Subgroup.card_bot] at h2
    have hq' : 2 ≤ Fintype.card F := Fintype.one_lt_card
    have : 1 < Fintype.card F ^ 2 := Nat.one_lt_pow (by norm_num) (by omega)
    omega
  have has : a ∈ stab 𝔛 γ := hQεs haQ
  have haT : ((⟨a, has⟩ : ↥(stab 𝔛 γ)) : 𝔘) ∈ Qv 𝔛 τ := hQετ haQ
  have ha1 : toSL3 ψ ⟨a, has⟩ ≠ 1 := fun h1 =>
    haQγ ((S46.toSL3_eq_one_iff_mem_qv h c.hyp.2.2 hγM hU _).mp h1)
  obtain ⟨v₀, hv₀⟩ : ∃ v₀, dualMat (toSL3 ψ ⟨a, has⟩) *ᵥ v₀ ≠ v₀ := by
    by_contra hcon
    push Not at hcon
    apply ha1
    have h1 : transposeInv (toSL3 ψ ⟨a, has⟩) = 1 :=
      eq_one_of_mulVec_eq_self fun v => by rw [coe_transposeInv]; exact hcon v
    rw [← transposeInv_transposeInv (toSL3 ψ ⟨a, has⟩), h1, map_one]
  have hcoa : ∀ x ∈ Pv 𝔛 γ, N₁.coord ⁅x, a⁆ =
      N₁.coord x - dualMat (toSL3 ψ ⟨a, has⟩) *ᵥ N₁.coord x := by
    intro x hx
    have hax : a * x⁻¹ * a⁻¹ ∈ Pv 𝔛 γ := N₁.conj_mem ⟨a, has⟩ (Subgroup.inv_mem _ hx)
    have e : ⁅x, a⁆ = x * (a * x⁻¹ * a⁻¹) := by simp only [commutatorElement_def]; group
    rw [e, N₁.coord_mul hx hax]
    have hc := N₁.coord_conj ⟨a, has⟩ (Subgroup.inv_mem _ hx)
    simp only at hc
    rw [hc, N₁.coord_inv hx, natAct_false, toSL3_dualSL, coe_transposeInv, Matrix.mulVec_neg,
      sub_eq_add_neg]
  set w₁ := v₀ - dualMat (toSL3 ψ ⟨a, has⟩) *ᵥ v₀ with hw₁
  have hw₁0 : w₁ ≠ 0 := fun h0 => hv₀ (sub_eq_zero.mp h0).symm
  have hw₁pt : w₁ ∈ pt0 := by
    obtain ⟨x, hx, hxc⟩ := N₁.exists_coord_eq v₀
    have := coord_commutator_mem_pt0 (h := h) N₁ hfix hx ⟨a, has⟩ haT
    rwa [show ⁅x, ((⟨a, has⟩ : ↥(stab 𝔛 γ)) : 𝔘)⁆ = ⁅x, a⁆ from rfl, hcoa x hx, hxc] at this
  have hw₁00 : w₁ 0 ≠ 0 := by
    intro h0
    apply hw₁0
    rw [eq_smul_e0_of_mem_pt0 hw₁pt, h0, zero_smul]
  have hsurj : ∀ y ∈ pt0, ∃ x ∈ A₁, x ∈ Pv 𝔛 γ ∧ N₁.coord x = y := by
    intro y hy
    obtain ⟨x, hx, hxc⟩ := N₁.exists_coord_eq ((y 0 / w₁ 0) • v₀)
    refine ⟨⁅x, a⁆, Subgroup.commutator_mem_commutator hx haQ,
      hA₁P (Subgroup.commutator_mem_commutator hx haQ), ?_⟩
    have e1 := eq_smul_e0_of_mem_pt0 hw₁pt
    have e2 := eq_smul_e0_of_mem_pt0 hy
    rw [hcoa x hx, hxc, Matrix.mulVec_smul, ← smul_sub, ← hw₁]
    calc (y 0 / w₁ 0) • w₁ = (y 0 / w₁ 0) • (w₁ 0 • ![1, 0, 0]) :=
          congrArg (fun v => (y 0 / w₁ 0) • v) e1
      _ = (y 0 / w₁ 0 * w₁ 0) • ![1, 0, 0] := by rw [smul_smul]
      _ = y 0 • ![1, 0, 0] := by rw [div_mul_cancel₀ _ hw₁00]
      _ = y := e2.symm
  have hXpre : ∀ x, x ∈ X ↔ x ∈ Pv 𝔛 γ ∧ N₁.coord x ∈ pt0 := by
    intro x
    constructor
    · intro hx
      have hle : X ≤ N₁.pre (pt0 : Submodule F (Fin 3 → F)).toAddSubgroup := by
        refine sup_le ?_ ?_
        · rw [hA₁def, Subgroup.commutator_le]
          intro p hp t ht
          refine N₁.mem_pre.mpr ⟨hA₁P (Subgroup.commutator_mem_commutator hp ht), ?_⟩
          exact coord_commutator_mem_pt0 (h := h) N₁ hfix hp ⟨t, hQεs ht⟩ (hQετ ht)
        · intro z hz
          refine N₁.mem_pre.mpr ⟨zm_le_pv _ γ hz, ?_⟩
          rw [(N₁.coord_eq_zero_iff (zm_le_pv _ γ hz)).mpr hz]
          exact Submodule.zero_mem _
      exact N₁.mem_pre.mp (hle hx)
    · rintro ⟨hxP, hxpt⟩
      obtain ⟨y, hyA, hyP, hyc⟩ := hsurj _ hxpt
      have hmem := N₁.inv_mul_mem_of_coord_eq hyP hxP hyc
      have : x = y * (y⁻¹ * x) := by group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hyA) (Subgroup.mem_sup_right hmem)
  obtain ⟨n, hn⟩ := c.hyp.2.2.1
  have hinf := c.pv_inf_centralizer hγM
  have hUn : IsSumOfNaturalModulesVia (stab 𝔛 γ) (Pv 𝔛 γ)
      (Pv 𝔛 γ ⊓ Subgroup.centralizer (Qv 𝔛 γ : Set 𝔘)) α₁ false 1 := by
    rw [hinf]; exact hPn
  have hZU : ⁅Uloc h.le L γ, Pv 𝔛 γ⁆ = ⊥ := by
    rw [eq_bot_iff, ← vv_comm_eq_bot h c.b4 hγM]
    exact Subgroup.commutator_mono ((uloc_le_zm h c.full hγM).trans (zm_le_vv h hγM))
      (pv_le_vv h hγM)
  have hZW : ⁅Uloc h.le L γ, Qv 𝔛 γ⁆ = ⊥ :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer).mpr
      ((uloc_le_zm h c.full hγM).trans (zm_le_centralizer_qv _ h20 hγM))
  have hUW : ⁅Pv 𝔛 γ, Qv 𝔛 γ⁆ ≤ Uloc h.le L γ := c.commutator_pv_qv hγM
  have hcl : Pv 𝔛 γ = Subgroup.closure {u | ∃ l : ↥(stab 𝔛 γ), ∃ x ∈ X,
      (l : 𝔘) * x * (l : 𝔘)⁻¹ = u} := by
    apply le_antisymm
    · set Y := Subgroup.closure {u | ∃ l : ↥(stab 𝔛 γ), ∃ x ∈ X, (l : 𝔘) * x * (l : 𝔘)⁻¹ = u}
      have hXY : X ≤ Y := fun x hx => Subgroup.subset_closure ⟨1, x, hx, by simp⟩
      have hYn : ∀ l : ↥(stab 𝔛 γ), ∀ y ∈ Y, (l : 𝔘) * y * (l : 𝔘)⁻¹ ∈ Y := by
        intro l y hy
        induction hy using Subgroup.closure_induction with
        | mem y hy =>
          obtain ⟨l', x, hx, rfl⟩ := hy
          exact Subgroup.subset_closure ⟨l * l', x, hx, by simp [mul_assoc]⟩
        | one => simp
        | mul a b _ _ ha hb =>
          have : (l : 𝔘) * (a * b) * (l : 𝔘)⁻¹ =
              ((l : 𝔘) * a * (l : 𝔘)⁻¹) * ((l : 𝔘) * b * (l : 𝔘)⁻¹) := by group
          rw [this]
          exact Y.mul_mem ha hb
        | inv a _ ha =>
          have : (l : 𝔘) * a⁻¹ * (l : 𝔘)⁻¹ = ((l : 𝔘) * a * (l : 𝔘)⁻¹)⁻¹ := by group
          rw [this]
          exact Y.inv_mem ha
      obtain ⟨y₁, hy₁A, hy₁P, hy₁c⟩ := hsurj ![1, 0, 0] (by simp [mem_pt0])
      have hy₁Z : y₁ ∉ ZM 𝔛 γ := by
        rw [← N₁.coord_eq_zero_iff hy₁P, hy₁c]
        intro h0
        have := congrFun h0 0
        simp at this
      intro v hv
      obtain ⟨u, huY, -, huv⟩ := N₁.exists_inv_mul_mem_of_invariant hα₁s hYn
        (hXY (Subgroup.mem_sup_left hy₁A)) hy₁P hy₁Z hv
      have : v = u * (u⁻¹ * v) := by group
      rw [this]
      exact Y.mul_mem huY (hXY (Subgroup.mem_sup_right huv))
    · rw [Subgroup.closure_le]
      rintro _ ⟨l, x, hx, rfl⟩
      exact N₁.conj_mem l (hXP hx)
  have hstab : ∀ l : ↥(stab 𝔛 γ), toSL3 α₁ l ∈ (ptStab : Subgroup (SL3 F)) →
      ∀ x ∈ X, (l : 𝔘) * x * (l : 𝔘)⁻¹ ∈ X := by
    intro l hl x hx
    obtain ⟨hxP, hxpt⟩ := (hXpre x).mp hx
    refine (hXpre _).mpr ⟨N₁.conj_mem l hxP, ?_⟩
    rw [N₁.coord_conj l hxP, natAct_false, eq_smul_e0_of_mem_pt0 hxpt, Matrix.mulVec_smul]
    exact Submodule.smul_mem _ _ (mem_ptStab_iff_mulVec_e0.mp hl)
  have hlevi : ∀ l : ↥(stab 𝔛 γ), toSL3 α₁ l ∈ (ptLevi : Subgroup (SL3 F)) →
      ∀ x ∈ X, x⁻¹ * ((l : 𝔘) * x * (l : 𝔘)⁻¹) ∈
        Pv 𝔛 γ ⊓ Subgroup.centralizer (Qv 𝔛 γ : Set 𝔘) := by
    intro l hl x hx
    obtain ⟨hxP, hxpt⟩ := (hXpre x).mp hx
    rw [hinf]
    refine N₁.inv_mul_mem_of_coord_eq hxP (N₁.conj_mem l hxP) ?_
    rw [N₁.coord_conj l hxP, natAct_false, mulVec_of_mem_ptLevi hl hxpt]
  have hXW : ⁅X, Qv 𝔛 γ⁆ ≠ ⊥ := by
    intro hbot
    obtain ⟨y₁, hy₁A, hy₁P, hy₁c⟩ := hsurj ![1, 0, 0] (by simp [mem_pt0])
    have hy₁C : y₁ ∈ Pv 𝔛 γ ⊓ Subgroup.centralizer (Qv 𝔛 γ : Set 𝔘) :=
      ⟨hy₁P, (Subgroup.commutator_eq_bot_iff_le_centralizer).mp hbot
        (Subgroup.mem_sup_left hy₁A)⟩
    rw [hinf, ← N₁.coord_eq_zero_iff hy₁P, hy₁c] at hy₁C
    have := congrFun hy₁C 0
    simp at this
  have hXWc : Nat.card ↥⁅X, Qv 𝔛 γ⁆ ≤ Nat.card F ^ 2 := by
    have hZετ' : ZM 𝔛 ε ≤ Qv 𝔛 τ := zm_le_qv_of_dist_lt _ hεM (by
      rw [tdist_comm, dist_eq_one_of_adj _ hτε]; omega)
    have hZεs : ZM 𝔛 ε ≤ stab 𝔛 γ := hZετ'.trans hTs
    have hZγs : ZM 𝔛 γ ≤ stab 𝔛 γ := (zm_le_qv_self _ hγM hb0).trans (qv_le_stab _ γ)
    have hZγε : ZM 𝔛 γ ≤ stab 𝔛 ε := ((zm_le_qv_self _ hγM hb0).trans
      (qv_le_qv _ h20 hγM hγτ)).trans (qv_le_stab_of_adj _ hτε)
    have hNn₁ : ZM 𝔛 ε ≤ Subgroup.normalizer ((⁅ZM 𝔛 ε, Qv 𝔛 γ⁆ : Subgroup 𝔘) : Set 𝔘) :=
      le_normalizer_commutator Subgroup.le_normalizer (hZεs.trans (stab_le_normalizer_qv _ γ))
    have hNn₂ : ZM 𝔛 γ ≤ Subgroup.normalizer ((⁅ZM 𝔛 ε, Qv 𝔛 γ⁆ : Subgroup 𝔘) : Set 𝔘) :=
      le_normalizer_commutator (hZγε.trans (stab_le_normalizer_zm _ ε))
        (hZγs.trans (stab_le_normalizer_qv _ γ))
    have hle : ⁅X, Qv 𝔛 γ⁆ ≤ ⁅ZM 𝔛 ε, Qv 𝔛 γ⁆ := by
      refine commutator_sup_left_le (hA₁Z.trans hNn₁) hNn₂ (Subgroup.commutator_mono hA₁Z le_rfl) ?_
      rw [(Subgroup.commutator_eq_bot_iff_le_centralizer).mpr (zm_le_centralizer_qv _ h20 hγM)]
      exact bot_le
    rw [(c.three hγM hγτ hτε hεn).1] at hle
    have hfinS := finite_stab h hγM
    have hfinU : Finite ↥(Usup 𝔛 γ τ) := Finite.of_injective _ (Subgroup.inclusion_injective
      ((c.usup_le_uloc hγM hγτ).trans ((uloc_le_zm h c.full hγM).trans hZγs)))
    calc Nat.card ↥⁅X, Qv 𝔛 γ⁆ ≤ Nat.card ↥(Usup 𝔛 γ τ) := Subgroup.card_le_of_le hle
      _ = Nat.card F ^ 2 := by rw [(c.edge hγM hγτ).2.1, Nat.card_eq_fintype_card]
  have h17 := ms17ii_holds 𝔘 F n hn (stab 𝔛 γ) (Uloc h.le L γ) (Qv 𝔛 γ) (Pv 𝔛 γ) X α₁ hα₁s hZd
    hUn (stab_le_normalizer_qv _ γ) hZU hZW hUW hXP hcl hstab hlevi hXW hXWc
  have hα'nγ : α₀' ∈ nablaSet h.le L γ := c.mem_nablaSet_geo_two' hs
  have hγnα' : γ ∈ nablaSet h.le L α₀' := c.nabla_symm hγM hρ₀γ.symm hα'ρ₀.symm hα'nγ
  have hZα'P : ZM 𝔛 α₀' ≤ Pv 𝔛 γ := c.zm_le_pv' hb6 hα' hα'ρ₀ hρ₀γ hγnα'
  have hγgeo : γ = geo 𝔛 α₀ α₀' (critDist 𝔛 - 2) := by
    rw [hγdef, ← geo_symm _ (show critDist 𝔛 - 2 ≤ (puAmalgam h.le).treeGraph.dist α₀ α₀' by
      omega), hd]
    congr 1
    omega
  have hdγβ : (puAmalgam h.le).treeGraph.dist γ β = critDist 𝔛 - 3 := by
    rw [tdist_comm, hγgeo, hβdef, dist_geo_geo _ (by omega) (by omega)]
    omega
  have hPγs : Pv 𝔛 γ ≤ stab 𝔛 α₀ := (pv_le_vv h hγM).trans
    ((S45.vi_le_qv _ (by omega)).trans (qv_le_stab_of_adj _ hαβ.symm))
  obtain ⟨w₀, hw₀U, hw₀C⟩ : ∃ w₀ ∈ Uloc h.le L α₀,
      w₀ ∉ Subgroup.centralizer (Pv 𝔛 γ : Set 𝔘) := by
    by_contra hcon
    push Not at hcon
    apply c.not_zm_le_qv hs
    intro z hz
    refine S46.stab_inf_centralizer_uloc_le_qv h c.hyp.2.2 hα ⟨hPγs (hZα'P hz), ?_⟩
    show z ∈ Subgroup.centralizer (Uloc h.le L α₀ : Set 𝔘)
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    exact (Subgroup.mem_centralizer_iff.mp (hcon u hu) z (hZα'P hz)).symm
  have hUαP : Uloc h.le L α₀ ≤ Pv 𝔛 α₀ := (uloc_le_zm h c.full hα).trans (zm_le_pv _ α₀)
  have hZ₀ := h17 w₀ (hPαQγ (hUαP hw₀U)) (hXc (hUαP hw₀U)) hw₀C
  have hZ₀U : Uloc h.le L γ ⊓ Subgroup.centralizer (qPtPre (stab 𝔛 γ) α₁ : Set 𝔘) ≤
      Uloc h.le L α₀ := by
    rw [← hZ₀, Subgroup.commutator_le]
    intro p hp y hy
    have hyU : y ∈ Uloc h.le L α₀ := (Subgroup.zpowers_le.mpr hw₀U) hy
    have e : ⁅p, y⁆ = (p * y * p⁻¹) * y⁻¹ := by simp only [commutatorElement_def]
    rw [e]
    exact Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_puTrans h.le
      (S4A.Uq_normal h) α₀ (hPγs hp)) y).mp hyU) (Subgroup.inv_mem _ hyU)
  have hall : ∀ z ∈ ZM 𝔛 α₀', ∀ x ∈ Pv 𝔛 α₀, ⁅x, z⁆ ∈ Uloc h.le L α₀ := by
    intro z hz x hx
    by_cases hxc : x ∈ Subgroup.centralizer (Pv 𝔛 γ : Set 𝔘)
    · have h1 : ⁅x, z⁆ = 1 := by
        rw [commutatorElement_eq_one_iff_mul_comm]
        exact (Subgroup.mem_centralizer_iff.mp hxc z (hZα'P hz)).symm
      rw [h1]
      exact Subgroup.one_mem _
    · have hZx := h17 x (hPαQγ hx) (hXc hx) hxc
      have hmem : ⁅z, x⁆ ∈ ⁅Pv 𝔛 γ, Subgroup.zpowers x⁆ :=
        Subgroup.commutator_mem_commutator (hZα'P hz) (Subgroup.mem_zpowers x)
      rw [hZx] at hmem
      rw [← commutatorElement_inv]
      exact Subgroup.inv_mem _ (hZ₀U hmem)
  obtain ⟨z, hzZ, hzQ⟩ := Set.not_subset.mp (c.not_zm_le_qv hs)
  obtain ⟨ψα, -, hUα, hPαd⟩ := c.exists_dual hα
  set Nα := NatSec.ofIsSum hPαd with hNα
  have hzs : z ∈ stab 𝔛 α₀ := zm_le_stab_of_isCritical _ h20 hb0 hs.1 hzZ
  have hz1 : toSL3 ψα ⟨z, hzs⟩ ≠ 1 := fun h1 =>
    hzQ ((S46.toSL3_eq_one_iff_mem_qv h c.hyp.2.2 hα hUα _).mp h1)
  obtain ⟨y, hy⟩ : ∃ y, dualMat (toSL3 ψα ⟨z, hzs⟩) *ᵥ y ≠ y := by
    by_contra hcon
    push Not at hcon
    apply hz1
    have h1 : transposeInv (toSL3 ψα ⟨z, hzs⟩) = 1 :=
      eq_one_of_mulVec_eq_self fun v => by rw [coe_transposeInv]; exact hcon v
    rw [← transposeInv_transposeInv (toSL3 ψα ⟨z, hzs⟩), h1, map_one]
  obtain ⟨x, hx, hxy⟩ := Nα.exists_coord_eq y
  have hZ : ⁅x, z⁆ ∈ ZM 𝔛 α₀ := uloc_le_zm h c.full hα (hall z hzZ x hx)
  have hzx : z * x⁻¹ * z⁻¹ ∈ Pv 𝔛 α₀ := Nα.conj_mem ⟨z, hzs⟩ (Subgroup.inv_mem _ hx)
  have e : ⁅x, z⁆ = x * (z * x⁻¹ * z⁻¹) := by simp only [commutatorElement_def]; group
  have h0 := (Nα.coord_eq_zero_iff (Subgroup.mul_mem _ hx hzx)).mpr (e ▸ hZ)
  rw [Nα.coord_mul hx hzx] at h0
  have hc := Nα.coord_conj ⟨z, hzs⟩ (Subgroup.inv_mem _ hx)
  simp only at hc
  rw [hc, Nα.coord_inv hx, natAct_true, Matrix.mulVec_neg, hxy, add_neg_eq_zero] at h0
  exact hy h0.symm

end Ctx

end CFSG.Quasithin.MS93.S4A.D432
