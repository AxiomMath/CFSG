module

public import CFSG.Quasithin.MS93.S4A432M
public import CFSG.Quasithin.MS93.S4A432
import CFSG.Quasithin.MS93.S45Vtx
import CFSG.Quasithin.MS93.S45Path

public section

namespace CFSG.Quasithin.MS93.S4A.D432

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

section Dual

variable {F : Type} [Field F]

theorem mem_pt0_of_dualMat_fix {A : Subgroup (SL3 F)}
    (hA : coordZero 0 ≤ commN A) {v : Fin 3 → F} (hv : ∀ g ∈ A, dualMat g *ᵥ v = v) :
    v ∈ pt0 := by
  have hperp : commN A ≤ orthN v := commN_le_orthN hv
  have h1 : v ⬝ᵥ Pi.single 1 1 = 0 :=
    hperp (hA (show (Pi.single 1 1 : Fin 3 → F) 0 = 0 by simp))
  have h2 : v ⬝ᵥ Pi.single 2 1 = 0 :=
    hperp (hA (show (Pi.single 2 1 : Fin 3 → F) 0 = 0 by simp))
  rw [dotProduct_single, mul_one] at h1 h2
  exact ⟨h1, h2⟩

theorem dualMat_mulVec_apply_of_fix {g : SL3 F}
    (hg : ∀ p : Fin 3 → F, p 0 = 0 → ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ p = p)
    (v : Fin 3 → F) {j : Fin 3} (hj : j ≠ 0) : (dualMat g *ᵥ v) j = v j := by
  have h1 := dualMat_mulVec_dotProduct g v (Pi.single j 1)
  rw [hg _ (by simp [hj.symm]), dotProduct_single, dotProduct_single, mul_one, mul_one] at h1
  exact h1

end Dual

namespace Ctx

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} {h : PUHyp M T L}
  {F : Type} [Field F] [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)}
  {α₀ α₀' : Vtx (puAmalgam h.le)} (c : Ctx h φ α₀ α₀')
include c

local notation "𝔛" => puAmalgam h.le
local notation "𝔘" => GoldAmalgam.Universal (puAmalgam h.le)
local notation "𝔄" => SimpleGraph.Adj (GoldAmalgam.treeGraph (puAmalgam h.le))

theorem exists_edge_coords' {μ ν : Vtx 𝔛} (hμ : IsMVtx 𝔛 μ) (hμν : 𝔄 μ ν) :
    ∃ ψ : ↥(stab 𝔛 μ) →* ↥(StatedSL 3 F), Function.Surjective ψ ∧
      IsSumOfNaturalModulesVia (stab 𝔛 μ) (Uloc h.le L μ) ⊥ ψ false 1 ∧
      IsSumOfNaturalModulesVia (stab 𝔛 μ) (Pv 𝔛 μ) (ZM 𝔛 μ) ψ true 1 ∧
      IsSumOfNaturalModulesVia (stab 𝔛 μ) (Vv 𝔛 μ) (Bloc h.le L μ) ψ true 1 ∧
      commN (natImage ψ (Qv 𝔛 ν)) = coordZero 0 ∧
      ∀ t : ↥(stab 𝔛 μ), (t : 𝔘) ∈ Qv 𝔛 ν → ∀ p : Fin 3 → F, p 0 = 0 →
        ((toSL3 ψ t : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ p = p := by
  have hq : 2 ≤ Nat.card F := Finite.one_lt_card
  have hTs : Qv 𝔛 ν ≤ stab 𝔛 μ := qv_le_stab_of_adj _ hμν.symm
  obtain ⟨hUZ, hUq, -, hrel⟩ := c.edge hμ hμν
  obtain ⟨ψ, hψs, hU, hP⟩ := c.exists_dual hμ
  obtain ⟨hPiB, hPB, -⟩ := c.decomp hμ
  have hVs : Vv 𝔛 μ ≤ stab 𝔛 μ := (vv_le_qv h c.b2 hμ).trans (qv_le_stab _ μ)
  have hVn := stab_le_normalizer_vv h μ
  have hBn : stab 𝔛 μ ≤ Subgroup.normalizer (Bloc h.le L μ : Set 𝔘) :=
    stab_le_normalizer_of_smul (F := fun δ => Bloc h.le L δ) _ (fun g δ => bloc_smul h g δ) μ
  have hBV : Bloc h.le L μ ≤ Vv 𝔛 μ := bloc_le_vv h μ
  have hVB := isSumOfNaturalModulesVia_transfer hP hPB hPiB le_rfl (sup_eq_left.mpr hBV) hVn hBn
    (((pv_le_vv h hμ).trans hVs).trans hBn)
  rw [inf_eq_right.mpr hBV] at hVB
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
    isSumOfNaturalModulesVia_conjSL_true hVB s, hcomm, fun t ht p hp => ?_⟩
  have hp' : p ∈ fixN (natImage (conjSL s ψ) (Qv 𝔛 ν)) := by rw [hfixN]; exact hp
  exact mem_fixN.mp hp' _ (mem_natImage.mpr ⟨t, ht, rfl⟩)

theorem critR0_le_pv {α α' : Vtx 𝔛} (hs : Star 𝔛 α α') : critR0 𝔛 α α' ≤ Pv 𝔛 α := by
  have hα := hs.1.1
  obtain ⟨-, hPB, hBG⟩ := c.decomp hα
  have hZs : ZM 𝔛 α' ≤ stab 𝔛 α := zm_le_stab_of_isCritical _ h.hyp20 h.critDist_pos hs.1
  have hVc : Vv 𝔛 α ≤ Subgroup.centralizer (Vv 𝔛 α : Set 𝔘) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer).mp (vv_comm_eq_bot h c.b4 hα)
  have hcn : ∀ X : Subgroup 𝔘, X ≤ Vv 𝔛 α → X ≤ Subgroup.normalizer (Pv 𝔛 α : Set 𝔘) :=
    fun X hX => ((hX.trans hVc).trans (Subgroup.centralizer_le (pv_le_vv h hα))).trans
      (Subgroup.centralizer_le_normalizer _)
  rw [critR0, ← hPB]
  exact commutator_sup_left_le (hcn _ (pv_le_vv h hα)) (hcn _ (bloc_le_vv h α))
    (Subgroup.le_normalizer_iff_commutator_le_left.mp (hZs.trans (stab_le_normalizer_pv _ α)))
    (((Subgroup.commutator_mono le_rfl hZs).trans hBG).trans (zm_le_pv _ α))

theorem zm_inf_bloc_le_of_mem {μ ν δ : Vtx 𝔛} (hμ : IsMVtx 𝔛 μ) (hμν : 𝔄 μ ν) (hνδ : 𝔄 ν δ)
    (hδ : δ ∈ nablaSet h.le L μ) : ZM 𝔛 δ ⊓ Bloc h.le L μ ≤ ZM 𝔛 μ := by
  refine c.le_zm_of_commutator_eq_bot hμ (inf_le_right.trans (bloc_le_vv h μ)) ?_
  refine c.eq_bot_of_normal_of_le_usup hμ hμν
    (c.stab_le_normalizer_commutator_qv hμ inf_le_right) ?_
  rw [← (c.three hμ hμν hνδ hδ).1]
  exact Subgroup.commutator_mono inf_le_left le_rfl

theorem zm_le_pv_of_critR0_le {α α' : Vtx 𝔛} (hs : Star 𝔛 α α')
    (hR : critR0 𝔛 α α' ≤ ZM 𝔛 (geo 𝔛 α α' 2)) : ZM 𝔛 (geo 𝔛 α α' 2) ≤ Pv 𝔛 α := by
  classical
  have h20 := h.hyp20
  have hb0 := h.critDist_pos
  have hα := hs.1.1
  have hb := c.b4
  have hd : (puAmalgam h.le).treeGraph.dist α α' = critDist 𝔛 := hs.1.2.1
  set β := geo 𝔛 α α' 1 with hβdef
  set δ := geo 𝔛 α α' 2 with hδdef
  have hαβ : 𝔄 α β := adj_geo_one _ (by omega)
  have hβδ : 𝔄 β δ := adj_geo _ (i := 1) (by omega)
  have hδM : IsMVtx 𝔛 δ := (isMVtx_geo _ (by omega)).mpr ⟨fun _ => even_two, fun _ => hα⟩
  have hαn : α ∈ nablaSet h.le L δ := mem_nablaSet_geo_two h c.full c.cent c.b2 hs.1
  have hδn : δ ∈ nablaSet h.le L α := c.nabla_symm hδM hβδ.symm hαβ.symm hαn
  have hZδV : ZM 𝔛 δ ≤ Vv 𝔛 α := (zm_le_vv_of_mem_nablaSet h hα hδn).2
  have hZB : ZM 𝔛 α ≤ Bloc h.le L α := zm_le_bloc h c.b2 hα
  have hR₀P := c.critR0_le_pv hs
  obtain ⟨ψ, -, hU, -, hVB, hcomm, hfix⟩ := c.exists_edge_coords' hα hαβ
  set N := NatSec.ofIsSum hVB with hNdef
  obtain ⟨a, haZ, haQ⟩ := IsConcreteLE.not_le_iff_exists.mp (c.not_zm_le_qv hs)
  have has : a ∈ stab 𝔛 α := zm_le_stab_of_isCritical _ h20 hb0 hs.1 haZ
  have haT : ((⟨a, has⟩ : ↥(stab 𝔛 α)) : 𝔘) ∈ Qv 𝔛 β := zm_le_qv_geo_one _ h20 hb0 hs.1 haZ
  have ha1 : toSL3 ψ ⟨a, has⟩ ≠ 1 := fun h1 =>
    haQ ((S46.toSL3_eq_one_iff_mem_qv h c.hyp.2.2 hα hU _).mp h1)
  obtain ⟨v₀, hv₀⟩ : ∃ v₀, dualMat (toSL3 ψ ⟨a, has⟩) *ᵥ v₀ ≠ v₀ := by
    by_contra hcon
    push Not at hcon
    apply ha1
    have h1 : transposeInv (toSL3 ψ ⟨a, has⟩) = 1 :=
      eq_one_of_mulVec_eq_self fun v => by rw [coe_transposeInv]; exact hcon v
    rw [← transposeInv_transposeInv (toSL3 ψ ⟨a, has⟩), h1, map_one]
  have hcoa : ∀ x ∈ Vv 𝔛 α, N.coord ⁅x, a⁆ =
      N.coord x - dualMat (toSL3 ψ ⟨a, has⟩) *ᵥ N.coord x := by
    intro x hx
    have hax : a * x⁻¹ * a⁻¹ ∈ Vv 𝔛 α := N.conj_mem ⟨a, has⟩ (Subgroup.inv_mem _ hx)
    have e : ⁅x, a⁆ = x * (a * x⁻¹ * a⁻¹) := by simp only [commutatorElement_def]; group
    rw [e, N.coord_mul hx hax]
    have hc := N.coord_conj ⟨a, has⟩ (Subgroup.inv_mem _ hx)
    simp only at hc
    rw [hc, N.coord_inv hx, natAct_true, Matrix.mulVec_neg, sub_eq_add_neg]
  set w₁ := v₀ - dualMat (toSL3 ψ ⟨a, has⟩) *ᵥ v₀ with hw₁
  have hw₁0 : w₁ ≠ 0 := fun h0 => hv₀ (sub_eq_zero.mp h0).symm
  have hw₁pt : w₁ ∈ pt0 := by
    rw [mem_pt0, hw₁]
    refine ⟨?_, ?_⟩
    · rw [Pi.sub_apply, dualMat_mulVec_apply_of_fix (hfix ⟨a, has⟩ haT) v₀ (by decide),
        sub_self]
    · rw [Pi.sub_apply, dualMat_mulVec_apply_of_fix (hfix ⟨a, has⟩ haT) v₀ (by decide),
        sub_self]
  have hw₁00 : w₁ 0 ≠ 0 := by
    intro h0
    apply hw₁0
    rw [eq_smul_e0_of_mem_pt0 hw₁pt, h0, zero_smul]
  have hsurj : ∀ y ∈ pt0, ∃ r ∈ critR0 𝔛 α α', r ∈ Vv 𝔛 α ∧ N.coord r = y := by
    intro y hy
    obtain ⟨x, hx, hxc⟩ := N.exists_coord_eq ((y 0 / w₁ 0) • v₀)
    have hxa : ⁅x, a⁆ ∈ critR0 𝔛 α α' := Subgroup.commutator_mem_commutator hx haZ
    refine ⟨⁅x, a⁆, hxa, pv_le_vv h hα (hR₀P hxa), ?_⟩
    have e1 := eq_smul_e0_of_mem_pt0 hw₁pt
    have e2 := eq_smul_e0_of_mem_pt0 hy
    rw [hcoa x hx, hxc, Matrix.mulVec_smul, ← smul_sub, ← hw₁]
    calc (y 0 / w₁ 0) • w₁ = (y 0 / w₁ 0) • (w₁ 0 • ![1, 0, 0]) :=
          congrArg (fun v => (y 0 / w₁ 0) • v) e1
      _ = (y 0 / w₁ 0 * w₁ 0) • ![1, 0, 0] := by rw [smul_smul]
      _ = y 0 • ![1, 0, 0] := by rw [div_mul_cancel₀ _ hw₁00]
      _ = y := e2.symm
  intro z hz
  have hzpt : N.coord z ∈ pt0 := by
    refine c.coord_mem_pt0 hα N hcomm.ge (hZδV hz) fun k hk => ?_
    refine hZB (zh_le_zm _ hαβ ((c.edge hδM hβδ.symm).1 ?_))
    rw [Usup, zv_of_isMVtx _ hδM]
    exact Subgroup.commutator_mem_commutator hz hk
  obtain ⟨r, hrR, hrV, hrc⟩ := hsurj _ hzpt
  have hrb := N.inv_mul_mem_of_coord_eq hrV (hZδV hz) hrc
  have hrZ : r ∈ ZM 𝔛 δ := hR hrR
  have hrz : r⁻¹ * z ∈ ZM 𝔛 α :=
    c.zm_inf_bloc_le_of_mem hα hαβ hβδ hδn ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ hrZ) hz, hrb⟩
  have := Subgroup.mul_mem _ (hR₀P hrR) (zm_le_pv _ α hrz)
  rwa [mul_inv_cancel_left] at this

theorem not_zm_le_centralizer_pv {α α' : Vtx 𝔛} (hs : Star 𝔛 α α') :
    ¬ ZM 𝔛 α' ≤ Subgroup.centralizer (Pv 𝔛 (geo 𝔛 α α' 2) : Set 𝔘) := by
  intro hc
  have h20 := h.hyp20
  have hb0 := h.critDist_pos
  have hα := hs.1.1
  have hα' : IsMVtx 𝔛 α' := hs.1.isMVtx_right _ h20
  have hb := c.b4
  have hd : (puAmalgam h.le).treeGraph.dist α α' = critDist 𝔛 := hs.1.2.1
  set β := geo 𝔛 α α' 1 with hβdef
  set δ := geo 𝔛 α α' 2 with hδdef
  set τ := geo 𝔛 α α' 3 with hτdef
  have hαβ : 𝔄 α β := adj_geo_one _ (by omega)
  have hβδ : 𝔄 β δ := adj_geo _ (i := 1) (by omega)
  have hδτ : 𝔄 δ τ := adj_geo _ (i := 2) (by omega)
  obtain ⟨x, hx, w, hw, hxw⟩ : ∃ x ∈ ZM 𝔛 α, ∃ w ∈ ZM 𝔛 α', ⁅x, w⁆ ≠ 1 := by
    by_contra hcon
    push Not at hcon
    apply ms22_ii _ h20 hb0 c.cent hs.1
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro x hx w hw
    rw [Subgroup.mem_bot]
    exact hcon x hx w hw
  have hxV : x ∈ Vv 𝔛 δ := by
    have := zv_le_vv h (α := δ) (ρ := α)
      (by rw [hδdef, tdist_comm, dist_geo _ (by omega)])
    rw [zv_of_isMVtx _ hα] at this
    exact this hx
  obtain ⟨g, hg, hgβ⟩ := exists_mem_stab_smul _ hβδ.symm hδτ
  have hgx : ⁅g * x * g⁻¹, w⁆ = ⁅x, w⁆ := by
    have hp : x⁻¹ * (g * x * g⁻¹) ∈ Pv 𝔛 δ := by
      have e : x⁻¹ * (g * x * g⁻¹) = ⁅x⁻¹, g⁆ := by simp only [commutatorElement_def]; group
      rw [e]
      exact (show ⁅Vv 𝔛 δ, stab 𝔛 δ⁆ ≤ Pv 𝔛 δ from le_sup_left)
        (Subgroup.commutator_mem_commutator (Subgroup.inv_mem _ hxV) hg)
    have hpw := Subgroup.mem_centralizer_iff.mp (hc hw) _ hp
    have e2 : g * x * g⁻¹ = x * (x⁻¹ * (g * x * g⁻¹)) := by group
    rw [e2]
    generalize x⁻¹ * (g * x * g⁻¹) = p at hpw ⊢
    simp only [commutatorElement_def]
    calc x * p * w * (x * p)⁻¹ * w⁻¹ = x * (p * w) * p⁻¹ * x⁻¹ * w⁻¹ := by group
      _ = x * (w * p) * p⁻¹ * x⁻¹ * w⁻¹ := by rw [hpw]
      _ = x * w * x⁻¹ * w⁻¹ := by group
  apply hxw
  rw [← hgx]
  have hgα : 𝔄 τ (g • α) := by
    have := (adj_smul _ g β α).mpr hαβ.symm
    rwa [hgβ] at this
  have hgαM : IsMVtx 𝔛 (g • α) := (isMVtx_smul _ g α).mpr hα
  have hgxZ : g * x * g⁻¹ ∈ ZM 𝔛 (g • α) := by
    rw [zm_smul]
    exact ⟨x, hx, by simp [MulAut.conj_apply]⟩
  have hdist : (puAmalgam h.le).treeGraph.dist α' (g • α) < critDist 𝔛 := by
    have h1 := dist_triangle (puAmalgam h.le) α' τ (g • α)
    have h2 : (puAmalgam h.le).treeGraph.dist α' τ = critDist 𝔛 - 3 := by
      rw [tdist_comm, hτdef, dist_geo_right _ (by omega), hd]
    rw [h2, dist_eq_one_of_adj _ hgα] at h1
    omega
  have hwQ : w ∈ Qv 𝔛 (g • α) := zm_le_qv_of_dist_lt _ hα' hdist hw
  rw [commutatorElement_eq_one_iff_mul_comm]
  exact (Subgroup.mem_centralizer_iff.mp (zm_le_centralizer_qv _ h20 hgαM hgxZ) w hwQ).symm

theorem exists_star_ne_through {μ ν : Vtx 𝔛} (hμ : IsMVtx 𝔛 μ) (hμν : 𝔄 μ ν) :
    ∃ x : Vtx 𝔛, Star 𝔛 μ x ∧ geo 𝔛 μ x 1 = ν ∧
      Usup 𝔛 (geo 𝔛 x μ 2) (geo 𝔛 x μ 1) ≠ Usup 𝔛 (geo 𝔛 x μ 2) (geo 𝔛 x μ 3) := by
  have hb := c.b4
  obtain ⟨α₁, hs₁, h4₁⟩ := c.exists_star_ne
  obtain ⟨g, hg⟩ := exists_smul_eq_of_isMVtx _ c.star.1.1 hμ
  have hs₂ : Star 𝔛 μ (g • α₁) := by rw [← hg]; exact (star_smul _ g α₀ α₁).mpr hs₁
  have h4₂ := usup_ne_smul _ g h4₁
  rw [hg] at h4₂
  have hd₂ : (puAmalgam h.le).treeGraph.dist μ (g • α₁) = critDist 𝔛 := hs₂.1.2.1
  have hμν₁ : 𝔄 μ (geo 𝔛 μ (g • α₁) 1) := adj_geo_one _ (by omega)
  obtain ⟨k, hk, hkν⟩ := exists_mem_stab_smul _ hμν₁ hμν
  have hkμ : k • μ = μ := (mem_stab _).mp hk
  refine ⟨k • g • α₁, ?_, ?_, ?_⟩
  · have := (star_smul _ k μ (g • α₁)).mpr hs₂
    rwa [hkμ] at this
  · have := geo_smul _ k μ (g • α₁) 1
    rw [hkμ] at this
    rw [this, hkν]
  · have := usup_ne_smul _ k h4₂
    rwa [hkμ] at this

theorem false_of_six' (hb6 : critDist 𝔛 = 6) : False := by
  classical
  have h20 := h.hyp20
  have hb0 := h.critDist_pos
  have hq : 2 ≤ Nat.card F := Finite.one_lt_card
  have hq' : 2 ≤ Fintype.card F := Fintype.one_lt_card
  obtain ⟨α', hs, h4⟩ := c.exists_star_ne
  have hα := hs.1.1
  have hα' : IsMVtx 𝔛 α' := hs.1.isMVtx_right _ h20
  have hd : (puAmalgam h.le).treeGraph.dist α₀ α' = 6 := hs.1.2.1.trans hb6
  have hd' : (puAmalgam h.le).treeGraph.dist α' α₀ = 6 := by rw [tdist_comm]; exact hd
  set δ := geo 𝔛 α₀ α' 2 with hδdef
  set γ := geo 𝔛 α' α₀ 2 with hγdef
  set τ := geo 𝔛 α' α₀ 3 with hτdef
  set ρ := geo 𝔛 α' α₀ 1 with hρdef
  have hτgeo : geo 𝔛 α₀ α' 3 = τ := by
    rw [hτdef, ← geo_symm _ (show 3 ≤ (puAmalgam h.le).treeGraph.dist α₀ α' by omega), hd]
  have hδM : IsMVtx 𝔛 δ := (isMVtx_geo _ (by omega)).mpr ⟨fun _ => even_two, fun _ => hα⟩
  have hγM : IsMVtx 𝔛 γ := (isMVtx_geo _ (by omega)).mpr ⟨fun _ => even_two, fun _ => hα'⟩
  have hδτ : 𝔄 δ τ := by rw [← hτgeo]; exact adj_geo _ (i := 2) (by omega)
  have hγτ : 𝔄 γ τ := adj_geo _ (i := 2) (by omega)
  have hργ : 𝔄 ρ γ := adj_geo _ (i := 1) (by omega)
  have hQ : Qv 𝔛 δ = Qv 𝔛 γ := c.qv_eq_of_six hb6 hs h4
  have hZ : ZM 𝔛 δ = ZM 𝔛 γ := by
    rw [← xm_eq_zm h c.full hδM, ← xm_eq_zm h c.full hγM, XM, XM, hQ]
  have hW : Usup 𝔛 δ τ = Usup 𝔛 γ τ := by
    rw [Usup, Usup, zv_of_isMVtx _ hδM, zv_of_isMVtx _ hγM, hZ]
  obtain ⟨x, hsx, hx1, h4x⟩ := c.exists_star_ne_through hδM hδτ
  have hdx : (puAmalgam h.le).treeGraph.dist δ x = 6 := hsx.1.2.1.trans hb6
  set e := geo 𝔛 δ x 2 with hedef
  have hτe : 𝔄 τ e := by rw [← hx1]; exact adj_geo _ (i := 1) (by omega)
  have heM : IsMVtx 𝔛 e := (isMVtx_geo _ (by omega)).mpr ⟨fun _ => even_two, fun _ => hδM⟩
  have hen : e ∈ nablaSet h.le L δ :=
    c.nabla_symm heM hτe.symm hδτ.symm (mem_nablaSet_geo_two h c.full c.cent c.b2 hsx.1)
  have hZeP : ZM 𝔛 e ≤ Pv 𝔛 δ :=
    c.zm_le_pv_of_critR0_le hsx (c.critR0_le_zm_of_six hb6 hsx h4x)
  have hUeZ : Uloc h.le L e ≤ ZM 𝔛 e := uloc_le_zm h c.full heM
  obtain ⟨ψ, hψs, hU, hP, -, hcomm, hfix⟩ := c.exists_edge_coords' hδM hδτ
  set α₁ := dualSL ψ with hα₁
  have hα₁s : Function.Surjective α₁ := dualSL_surjective hψs
  have hZd : IsSumOfNaturalModulesVia (stab 𝔛 δ) (Uloc h.le L δ) ⊥ α₁ true 1 :=
    isSumOfNaturalModulesVia_dualSL hU
  have hPn : IsSumOfNaturalModulesVia (stab 𝔛 δ) (Pv 𝔛 δ) (ZM 𝔛 δ) α₁ false 1 :=
    isSumOfNaturalModulesVia_dualSL hP
  set N₁ := NatSec.ofIsSum hPn with hN₁
  have hTs : Qv 𝔛 τ ≤ stab 𝔛 δ := qv_le_stab_of_adj _ hδτ.symm
  have hfinS := finite_stab h hδM
  set X := Uloc h.le L e ⊔ ZM 𝔛 δ with hXdef
  have hXP : X ≤ Pv 𝔛 δ := sup_le (hUeZ.trans hZeP) (zm_le_pv _ δ)
  have hptU : ∀ u ∈ Uloc h.le L e, N₁.coord u ∈ pt0 := by
    intro u hu
    have huP : u ∈ Pv 𝔛 δ := hZeP (hUeZ hu)
    refine mem_pt0_of_dualMat_fix hcomm.ge fun g hg => ?_
    obtain ⟨t, htT, rfl⟩ := mem_natImage.mp hg
    have htu : (t : 𝔘) * u * (t : 𝔘)⁻¹ ∈ Pv 𝔛 δ := N₁.conj_mem t huP
    have hmem : u⁻¹ * ((t : 𝔘) * u * (t : 𝔘)⁻¹) ∈ ZM 𝔛 δ := by
      have e1 : u⁻¹ * ((t : 𝔘) * u * (t : 𝔘)⁻¹) = ⁅u⁻¹, (t : 𝔘)⁆ := by
        simp only [commutatorElement_def]; group
      rw [e1]
      have : ⁅u⁻¹, (t : 𝔘)⁆ ∈ Usup 𝔛 e τ := by
        rw [Usup, zv_of_isMVtx _ heM]
        exact Subgroup.commutator_mem_commutator (Subgroup.inv_mem _ (hUeZ hu)) htT
      exact zh_le_zm _ hδτ ((c.edge heM hτe.symm).1 this)
    have h0 := (N₁.coord_eq_zero_iff (Subgroup.mul_mem _ (Subgroup.inv_mem _ huP) htu)).mpr hmem
    rw [N₁.coord_mul (Subgroup.inv_mem _ huP) htu, N₁.coord_inv huP, N₁.coord_conj t huP,
      natAct_false, toSL3_dualSL, coe_transposeInv, neg_add_eq_zero] at h0
    exact h0.symm
  have hfinU : Finite ↥(Uloc h.le L e) := by
    have := finite_stab h heM
    exact Finite.of_injective _ (Subgroup.inclusion_injective
      (hUeZ.trans ((zm_le_qv_self _ heM hb0).trans (qv_le_stab _ e))))
  have hfinW : Finite ↥(Usup 𝔛 δ τ) := Finite.of_injective _ (Subgroup.inclusion_injective
    ((c.usup_le_uloc hδM hδτ).trans ((uloc_le_zm h c.full hδM).trans
      ((zm_le_qv_self _ hδM hb0).trans (qv_le_stab _ δ)))))
  have himg : Fintype.card F ≤ Nat.card ↥(N₁.img (Uloc h.le L e)) := by
    have hcard := card_le_card_inf_mul_card_img N₁ (hUeZ.trans hZeP)
    have hle : Uloc h.le L e ⊓ ZM 𝔛 δ ≤ Usup 𝔛 δ τ := by
      rw [← c.uloc_inf_bloc hδM hδτ hτe hen]
      exact inf_le_inf_left _ (zm_le_bloc h c.b2 hδM)
    have h1 := Subgroup.card_le_of_le hle
    obtain ⟨ψ₀, -, hψ₀⟩ := exists_natural_Uloc h c.hyp.2.2 heM
    rw [card_eq_of_natural hψ₀, Nat.card_eq_fintype_card (α := F)] at hcard
    rw [(c.edge hδM hδτ).2.1] at h1
    by_contra hlt
    have h2 : Nat.card ↥(Uloc h.le L e ⊓ ZM 𝔛 δ) * Nat.card ↥(N₁.img (Uloc h.le L e)) <
        Fintype.card F ^ 2 * Fintype.card F :=
      Nat.mul_lt_mul_of_le_of_lt h1 (not_le.mp hlt) (by positivity)
    have e3 : Fintype.card F ^ 2 * Fintype.card F = Fintype.card F ^ 3 := by ring
    omega
  have himg_eq : N₁.img (Uloc h.le L e) = (pt0 : Submodule F (Fin 3 → F)).toAddSubgroup := by
    refine AddSubgroup.eq_of_le_of_card_ge (fun y hy => ?_) ?_
    · obtain ⟨u, hu, -, rfl⟩ := N₁.mem_img.mp hy
      exact hptU u hu
    · have := ML3.card_pt0 (F := F)
      rw [Nat.card_eq_fintype_card (α := F)] at this
      exact this.le.trans himg
  have hXpre : ∀ y, y ∈ X ↔ y ∈ Pv 𝔛 δ ∧ N₁.coord y ∈ pt0 := by
    intro y
    constructor
    · intro hy
      have hle : X ≤ N₁.pre (pt0 : Submodule F (Fin 3 → F)).toAddSubgroup := by
        refine sup_le (fun u hu => N₁.mem_pre.mpr ⟨hZeP (hUeZ hu), hptU u hu⟩) ?_
        intro z hz
        refine N₁.mem_pre.mpr ⟨zm_le_pv _ δ hz, ?_⟩
        rw [(N₁.coord_eq_zero_iff (zm_le_pv _ δ hz)).mpr hz]
        exact Submodule.zero_mem _
      exact N₁.mem_pre.mp (hle hy)
    · rintro ⟨hyP, hypt⟩
      have hy' : N₁.coord y ∈ N₁.img (Uloc h.le L e) := by rw [himg_eq]; exact hypt
      obtain ⟨u, hu, huP, huc⟩ := N₁.mem_img.mp hy'
      have hmem := N₁.inv_mul_mem_of_coord_eq huP hyP huc
      have : y = u * (u⁻¹ * y) := by group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hu) (Subgroup.mem_sup_right hmem)
  obtain ⟨y₁, hy₁X, hy₁c⟩ : ∃ y₁ ∈ X, N₁.coord y₁ = ![1, 0, 0] := by
    have h1 : (![1, 0, 0] : Fin 3 → F) ∈ N₁.img (Uloc h.le L e) := by
      rw [himg_eq]; simp [mem_pt0]
    obtain ⟨u, hu, -, huc⟩ := N₁.mem_img.mp h1
    exact ⟨u, Subgroup.mem_sup_left hu, huc⟩
  have hy₁P : y₁ ∈ Pv 𝔛 δ := hXP hy₁X
  have hy₁Z : y₁ ∉ ZM 𝔛 δ := by
    rw [← N₁.coord_eq_zero_iff hy₁P, hy₁c]
    intro h0
    have := congrFun h0 0
    simp at this
  obtain ⟨n, hn⟩ := c.hyp.2.2.1
  have hinf := c.pv_inf_centralizer hδM
  have hUn : IsSumOfNaturalModulesVia (stab 𝔛 δ) (Pv 𝔛 δ)
      (Pv 𝔛 δ ⊓ Subgroup.centralizer (Qv 𝔛 δ : Set 𝔘)) α₁ false 1 := by
    rw [hinf]; exact hPn
  have hZU : ⁅Uloc h.le L δ, Pv 𝔛 δ⁆ = ⊥ := by
    rw [eq_bot_iff, ← vv_comm_eq_bot h c.b4 hδM]
    exact Subgroup.commutator_mono ((uloc_le_zm h c.full hδM).trans (zm_le_vv h hδM))
      (pv_le_vv h hδM)
  have hZW : ⁅Uloc h.le L δ, Qv 𝔛 δ⁆ = ⊥ :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer).mpr
      ((uloc_le_zm h c.full hδM).trans (zm_le_centralizer_qv _ h20 hδM))
  have hUW : ⁅Pv 𝔛 δ, Qv 𝔛 δ⁆ ≤ Uloc h.le L δ := c.commutator_pv_qv hδM
  have hcl : Pv 𝔛 δ = Subgroup.closure {u | ∃ l : ↥(stab 𝔛 δ), ∃ x ∈ X,
      (l : 𝔘) * x * (l : 𝔘)⁻¹ = u} := by
    apply le_antisymm
    · set Y := Subgroup.closure {u | ∃ l : ↥(stab 𝔛 δ), ∃ x ∈ X, (l : 𝔘) * x * (l : 𝔘)⁻¹ = u}
      have hXY : X ≤ Y := fun x hx => Subgroup.subset_closure ⟨1, x, hx, by simp⟩
      have hYn : ∀ l : ↥(stab 𝔛 δ), ∀ y ∈ Y, (l : 𝔘) * y * (l : 𝔘)⁻¹ ∈ Y := by
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
      intro v hv
      obtain ⟨u, huY, -, huv⟩ := N₁.exists_inv_mul_mem_of_invariant hα₁s hYn
        (hXY hy₁X) hy₁P hy₁Z hv
      have : v = u * (u⁻¹ * v) := by group
      rw [this]
      exact Y.mul_mem huY (hXY (Subgroup.mem_sup_right huv))
    · rw [Subgroup.closure_le]
      rintro _ ⟨l, x, hx, rfl⟩
      exact N₁.conj_mem l (hXP hx)
  have hstab : ∀ l : ↥(stab 𝔛 δ), toSL3 α₁ l ∈ (ptStab : Subgroup (SL3 F)) →
      ∀ x ∈ X, (l : 𝔘) * x * (l : 𝔘)⁻¹ ∈ X := by
    intro l hl x hx
    obtain ⟨hxP, hxpt⟩ := (hXpre x).mp hx
    refine (hXpre _).mpr ⟨N₁.conj_mem l hxP, ?_⟩
    rw [N₁.coord_conj l hxP, natAct_false, eq_smul_e0_of_mem_pt0 hxpt, Matrix.mulVec_smul]
    exact Submodule.smul_mem _ _ (mem_ptStab_iff_mulVec_e0.mp hl)
  have hlevi : ∀ l : ↥(stab 𝔛 δ), toSL3 α₁ l ∈ (ptLevi : Subgroup (SL3 F)) →
      ∀ x ∈ X, x⁻¹ * ((l : 𝔘) * x * (l : 𝔘)⁻¹) ∈
        Pv 𝔛 δ ⊓ Subgroup.centralizer (Qv 𝔛 δ : Set 𝔘) := by
    intro l hl x hx
    obtain ⟨hxP, hxpt⟩ := (hXpre x).mp hx
    rw [hinf]
    refine N₁.inv_mul_mem_of_coord_eq hxP (N₁.conj_mem l hxP) ?_
    rw [N₁.coord_conj l hxP, natAct_false, mulVec_of_mem_ptLevi hl hxpt]
  have hXW : ⁅X, Qv 𝔛 δ⁆ ≠ ⊥ := by
    intro hbot
    have hy₁C : y₁ ∈ Pv 𝔛 δ ⊓ Subgroup.centralizer (Qv 𝔛 δ : Set 𝔘) :=
      ⟨hy₁P, (Subgroup.commutator_eq_bot_iff_le_centralizer).mp hbot hy₁X⟩
    rw [hinf] at hy₁C
    exact hy₁Z hy₁C
  have hXWc : Nat.card ↥⁅X, Qv 𝔛 δ⁆ ≤ Nat.card F ^ 2 := by
    have hZes : ZM 𝔛 e ≤ stab 𝔛 δ := (zm_le_qv_of_dist_lt _ heM (by
      rw [dist_eq_two_of_adj_adj _ hτe.symm hδτ.symm (by
        intro hed; exact (hen.2) (by rw [hed, zv_of_isMVtx _ hδM]; exact zm_le_bloc h c.b2 hδM))]
      omega)).trans (qv_le_stab _ δ)
    have hZδs : ZM 𝔛 δ ≤ stab 𝔛 δ := (zm_le_qv_self _ hδM hb0).trans (qv_le_stab _ δ)
    have hZδe : ZM 𝔛 δ ≤ stab 𝔛 e := ((zm_le_qv_self _ hδM hb0).trans
      (qv_le_qv _ h20 hδM hδτ)).trans (qv_le_stab_of_adj _ hτe)
    have hNn₁ : ZM 𝔛 e ≤ Subgroup.normalizer ((⁅ZM 𝔛 e, Qv 𝔛 δ⁆ : Subgroup 𝔘) : Set 𝔘) :=
      le_normalizer_commutator Subgroup.le_normalizer (hZes.trans (stab_le_normalizer_qv _ δ))
    have hNn₂ : ZM 𝔛 δ ≤ Subgroup.normalizer ((⁅ZM 𝔛 e, Qv 𝔛 δ⁆ : Subgroup 𝔘) : Set 𝔘) :=
      le_normalizer_commutator (hZδe.trans (stab_le_normalizer_zm _ e))
        (hZδs.trans (stab_le_normalizer_qv _ δ))
    have hle : ⁅X, Qv 𝔛 δ⁆ ≤ ⁅ZM 𝔛 e, Qv 𝔛 δ⁆ := by
      refine commutator_sup_left_le (hUeZ.trans hNn₁) hNn₂
        (Subgroup.commutator_mono hUeZ le_rfl) ?_
      rw [(Subgroup.commutator_eq_bot_iff_le_centralizer).mpr (zm_le_centralizer_qv _ h20 hδM)]
      exact bot_le
    rw [(c.three hδM hδτ hτe hen).1] at hle
    calc Nat.card ↥⁅X, Qv 𝔛 δ⁆ ≤ Nat.card ↥(Usup 𝔛 δ τ) := Subgroup.card_le_of_le hle
      _ = Nat.card F ^ 2 := by rw [(c.edge hδM hδτ).2.1, Nat.card_eq_fintype_card]
  have h17 := ms17ii_holds 𝔘 F n hn (stab 𝔛 δ) (Uloc h.le L δ) (Qv 𝔛 δ) (Pv 𝔛 δ) X α₁ hα₁s hZd
    hUn (stab_le_normalizer_qv _ δ) hZU hZW hUW hXP hcl hstab hlevi hXW hXWc
  obtain ⟨w, hwZ, hwC⟩ := IsConcreteLE.not_le_iff_exists.mp (c.not_zm_le_centralizer_pv hs)
  have hdα'δ : (puAmalgam h.le).treeGraph.dist α' δ < critDist 𝔛 := by
    rw [tdist_comm, hδdef, dist_geo_right _ (by omega), hd]; omega
  have hdα'e : (puAmalgam h.le).treeGraph.dist α' e < critDist 𝔛 := by
    have h1 := dist_triangle (puAmalgam h.le) α' τ e
    rw [hτdef, dist_geo _ (by omega), dist_eq_one_of_adj _ hτe] at h1
    omega
  have hZα'δ : ZM 𝔛 α' ≤ Qv 𝔛 δ := zm_le_qv_of_dist_lt _ hα' hdα'δ
  have hZα'e : ZM 𝔛 α' ≤ Qv 𝔛 e := zm_le_qv_of_dist_lt _ hα' hdα'e
  have hXc : ZM 𝔛 α' ≤ Subgroup.centralizer (X : Set 𝔘) := by
    rw [Subgroup.le_centralizer_iff]
    refine sup_le ?_ ?_
    · exact hUeZ.trans (Subgroup.le_centralizer_iff.mp
        (hZα'e.trans (Subgroup.le_centralizer_iff.mp (zm_le_centralizer_qv _ h20 heM))))
    · exact Subgroup.le_centralizer_iff.mp
        (hZα'δ.trans (Subgroup.le_centralizer_iff.mp (zm_le_centralizer_qv _ h20 hδM)))
  have hZ₀ := h17 w (hZα'δ hwZ) (hXc hwZ) hwC
  have hWle : Usup 𝔛 δ τ ≤
      Uloc h.le L δ ⊓ Subgroup.centralizer (qPtPre (stab 𝔛 δ) α₁ : Set 𝔘) := by
    intro u hu
    have huU : u ∈ Uloc h.le L δ := c.usup_le_uloc hδM hδτ hu
    refine ⟨huU, ?_⟩
    show u ∈ Subgroup.centralizer (qPtPre (stab 𝔛 δ) α₁ : Set 𝔘)
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨l, hl, rfl⟩
    have hvec : natVec hU ⟨u, huU⟩ ∈ coordZero 0 := by
      rw [← hcomm]
      have hu' : ((⟨u, huU⟩ : ↥(Uloc h.le L δ)) : 𝔘) ∈ ⁅Uloc h.le L δ, Qv 𝔛 τ⁆ := by
        rw [← usup_eq_commutator_uloc h c.full hδM hδτ]; exact hu
      exact (mem_commutator_iff_natVec hU hTs ⟨u, huU⟩).mp hu'
    refine (commute_iff_natVec hU l ⟨u, huU⟩).mpr ?_
    have hl' : toSL3 α₁ l ∈ (qPt : Subgroup (SL3 F)) := hl
    have e1 : toSL3 ψ l = transposeInv (toSL3 α₁ l) := by
      rw [hα₁, toSL3_dualSL, transposeInv_transposeInv]
    rw [e1, coe_transposeInv]
    exact ML3.dualMat_mulVec_of_mem_qPt hl' hvec
  have hPR : ⁅Pv 𝔛 δ, Subgroup.zpowers w⁆ ≤ critR0 𝔛 α₀ α' := by
    rw [← (c.critR0_eq hs).2, Subgroup.commutator_comm]
    refine Subgroup.commutator_mono (Subgroup.zpowers_le.mpr hwZ) ?_
    rw [← hQ]
    exact (pv_le_vv h hδM).trans (vv_le_qv h c.b2 hδM)
  have hWR : Usup 𝔛 δ τ ≤ Usup 𝔛 γ ρ := by
    rw [← (c.critR0_eq hs).1]
    exact (hWle.trans hZ₀.ge).trans hPR
  have hfinSγ := finite_stab h hγM
  have hfinR : Finite ↥(Usup 𝔛 γ ρ) := Finite.of_injective _ (Subgroup.inclusion_injective
    ((c.usup_le_uloc hγM hργ.symm).trans ((uloc_le_zm h c.full hγM).trans
      ((zm_le_qv_self _ hγM hb0).trans (qv_le_stab _ γ)))))
  have heq : Usup 𝔛 δ τ = Usup 𝔛 γ ρ := Subgroup.eq_of_le_of_card_ge hWR (by
    rw [(c.edge hγM hργ.symm).2.1, (c.edge hδM hδτ).2.1])
  exact h4 (heq.symm.trans hW)

end Ctx

end CFSG.Quasithin.MS93.S4A.D432

namespace CFSG.Quasithin.MS93.S4A

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible

theorem s432Dual5R_holds (h32 : S32) (h431A : S431A) (h431B : S431B) : S432Dual5R := by
  intro G _ _ M T L h F _ _ φ hH hb6 α α' hs _ hkall hCHall _
  have hfull : IsSL3Full M T L :=
    isSL3Full_iff_exists_via.mpr ⟨F, inferInstance, inferInstance, φ, hH.2.2⟩
  exact D432.Ctx.false_of_six' ⟨hfull, hH, centHyp_of_S32 h32 h, s42_of h32, h431A, h431B,
    by omega, hs, hkall, hCHall⟩ hb6

theorem s432Dual5_holds (h32 : S32) (h431A : S431A) (h431B : S431B) : S432Dual5 :=
  s432Dual5_of h32 h431A h431B (s432Dual5R_holds h32 h431A h431B)

theorem s432_holds (h32 : S32) (h431A : S431A) (h431B : S431B) : S432 :=
  s432_of h32 h431A h431B (s432Dual5_holds h32 h431A h431B)

end CFSG.Quasithin.MS93.S4A
