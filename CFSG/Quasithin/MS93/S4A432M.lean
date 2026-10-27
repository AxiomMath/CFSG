module

public import CFSG.Quasithin.MS93.S4A432L
import CFSG.Quasithin.MS93.S45Vtx
import CFSG.Quasithin.MS93.S45Path

public section

namespace CFSG.Quasithin.MS93.S4A.D432

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

section Count

variable {𝔾 : Type} [Group 𝔾] {L V K₀ : Subgroup 𝔾} {F : Type} [Field F] [Finite F]
  {ψ : ↥L →* ↥(StatedSL 3 F)} {dual : Bool}

theorem card_le_card_inf_mul_card_img (N : NatSec L V K₀ ψ dual) {B : Subgroup 𝔾} [Finite ↥B]
    (hBV : B ≤ V) : Nat.card ↥B ≤ Nat.card ↥(B ⊓ K₀) * Nat.card ↥(N.img B) := by
  set f : ↥B →* Multiplicative (Fin 3 → F) := N.β.comp (Subgroup.inclusion hBV) with hf
  have h1 := Subgroup.card_ker_mul_card_range f
  have hfinK : Finite ↥(B ⊓ K₀) := Finite.of_injective _ (Subgroup.inclusion_injective inf_le_left)
  have hrange : Nat.card ↥f.range ≤ Nat.card ↥(N.img B) := by
    refine Nat.card_le_card_of_injective
      (fun m => ⟨Multiplicative.toAdd (m : Multiplicative (Fin 3 → F)), ?_⟩) ?_
    · obtain ⟨b, hb⟩ := m.2
      refine N.mem_img.mpr ⟨b, b.2, hBV b.2, ?_⟩
      rw [N.coord_of_mem (hBV b.2), ← hb]
      rfl
    · intro a b hab
      have := congrArg (fun x : ↥(N.img B) => (x : Fin 3 → F)) hab
      exact Subtype.ext this
  have hker : Nat.card ↥f.ker ≤ Nat.card ↥(B ⊓ K₀) := by
    refine Nat.card_le_card_of_injective (fun k => ⟨k.1, k.1.2, (N.ker _).mp k.2⟩) ?_
    intro a b hab
    have := congrArg (fun x : ↥(B ⊓ K₀) => (x : 𝔾)) hab
    exact Subtype.ext (Subtype.ext this)
  rw [← h1]
  exact Nat.mul_le_mul hker hrange

end Count

namespace Ctx

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} {h : PUHyp M T L}
  {F : Type} [Field F] [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)}
  {α₀ α₀' : Vtx (puAmalgam h.le)} (c : Ctx h φ α₀ α₀')
include c

local notation "𝔛" => puAmalgam h.le
local notation "𝔘" => GoldAmalgam.Universal (puAmalgam h.le)
local notation "𝔄" => SimpleGraph.Adj (GoldAmalgam.treeGraph (puAmalgam h.le))

theorem stab_le_normalizer_commutator_qv {μ : Vtx 𝔛} (hμ : IsMVtx 𝔛 μ) {X : Subgroup 𝔘}
    (hX : X ≤ Bloc h.le L μ) :
    stab 𝔛 μ ≤ Subgroup.normalizer ((⁅X, Qv 𝔛 μ⁆ : Subgroup 𝔘) : Set 𝔘) := by
  obtain ⟨-, -, hBG⟩ := c.decomp hμ
  have hZcQ := zm_le_centralizer_qv _ h.hyp20 hμ
  refine le_normalizer_of_map_conj_le fun g hg => ?_
  rw [Subgroup.map_commutator, Subgroup.commutator_le]
  rintro _ ⟨z, hz, rfl⟩ _ ⟨y, hy, rfl⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  have hc : ⁅z⁻¹, g⁆ ∈ ZM 𝔛 μ :=
    hBG (Subgroup.commutator_mem_commutator (Subgroup.inv_mem _ (hX hz)) hg)
  have hy' : g * y * g⁻¹ ∈ Qv 𝔛 μ :=
    (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_qv _ μ hg) y).mp hy
  have hcy : ⁅z⁻¹, g⁆ * (g * y * g⁻¹) = (g * y * g⁻¹) * ⁅z⁻¹, g⁆ :=
    (Subgroup.mem_centralizer_iff.mp (hZcQ hc) _ hy').symm
  have e : ⁅g * z * g⁻¹, g * y * g⁻¹⁆ = ⁅z, g * y * g⁻¹⁆ := by
    have e1 : g * z * g⁻¹ = z * ⁅z⁻¹, g⁆ := by simp only [commutatorElement_def]; group
    rw [e1]
    simp only [commutatorElement_def] at hcy ⊢
    calc z * (z⁻¹ * g * z⁻¹⁻¹ * g⁻¹) * (g * y * g⁻¹) *
          (z * (z⁻¹ * g * z⁻¹⁻¹ * g⁻¹))⁻¹ * (g * y * g⁻¹)⁻¹
        = z * ((z⁻¹ * g * z⁻¹⁻¹ * g⁻¹) * (g * y * g⁻¹)) *
          (z⁻¹ * g * z⁻¹⁻¹ * g⁻¹)⁻¹ * z⁻¹ * (g * y * g⁻¹)⁻¹ := by group
      _ = z * ((g * y * g⁻¹) * (z⁻¹ * g * z⁻¹⁻¹ * g⁻¹)) *
          (z⁻¹ * g * z⁻¹⁻¹ * g⁻¹)⁻¹ * z⁻¹ * (g * y * g⁻¹)⁻¹ := by rw [hcy]
      _ = z * (g * y * g⁻¹) * z⁻¹ * (g * y * g⁻¹)⁻¹ := by group
  rw [e]
  exact Subgroup.commutator_mem_commutator hz hy'

theorem eq_bot_of_normal_of_le_usup {μ ν : Vtx 𝔛} (hμ : IsMVtx 𝔛 μ) (hμν : 𝔄 μ ν)
    {Y : Subgroup 𝔘} (hYn : stab 𝔛 μ ≤ Subgroup.normalizer (Y : Set 𝔘))
    (hYU : Y ≤ Usup 𝔛 μ ν) : Y = ⊥ := by
  have hq : 2 ≤ Fintype.card F := Fintype.one_lt_card
  have hUU := c.usup_le_uloc hμ hμν
  by_cases hYZ : Y ≤ Zloc h.le L μ
  · rw [eq_bot_iff, ← uloc_inf_zloc h c.full μ]
    exact le_inf (hYU.trans hUU) hYZ
  · exfalso
    have hle := uloc_le_of_normal h c.full c.hyp.2.2 hμ
      ((hYU.trans hUU).trans (uloc_le_zm h c.full hμ)) hYn hYZ
    have hfinS := finite_stab h hμ
    have hfinH : Finite ↥(Usup 𝔛 μ ν) := Finite.of_injective _ (Subgroup.inclusion_injective
      (hUU.trans ((uloc_le_zm h c.full hμ).trans
        ((zm_le_qv_self _ hμ h.critDist_pos).trans (qv_le_stab _ μ)))))
    have h1 := Subgroup.card_le_of_le (hle.trans hYU)
    obtain ⟨ψ₀, -, hψ₀⟩ := exists_natural_Uloc h c.hyp.2.2 hμ
    rw [card_eq_of_natural hψ₀, (c.edge hμ hμν).2.1, Nat.card_eq_fintype_card (α := F)] at h1
    have : Fintype.card F ^ 2 < Fintype.card F ^ 3 :=
      Nat.pow_lt_pow_right (by omega) (by norm_num)
    omega

theorem le_zm_of_commutator_eq_bot {μ : Vtx 𝔛} (hμ : IsMVtx 𝔛 μ) {X : Subgroup 𝔘}
    (hXV : X ≤ Vv 𝔛 μ) (hX : ⁅X, Qv 𝔛 μ⁆ = ⊥) : X ≤ ZM 𝔛 μ := by
  have hXc : X ≤ Subgroup.centralizer (Qv 𝔛 μ : Set 𝔘) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer).mp hX
  have hE := S45.isElemAbelian_vi _ h.hyp20 h.critDist_pos (δ := μ) (i := 2)
    (by have := c.b4; omega)
  intro x hx
  rw [← xm_eq_zm h c.full hμ, XM]
  exact mem_omegaOneCenterOf (vv_le_qv h c.b2 hμ (hXV hx))
    (fun y hy => Subgroup.mem_centralizer_iff.mp (hXc hx) y hy) (hE.2 x (hXV hx))

theorem exists_edge_coords_vv {μ ν : Vtx 𝔛} (hμ : IsMVtx 𝔛 μ) (hμν : 𝔄 μ ν) :
    ∃ ψ : ↥(stab 𝔛 μ) →* ↥(StatedSL 3 F), Function.Surjective ψ ∧
      IsSumOfNaturalModulesVia (stab 𝔛 μ) (Uloc h.le L μ) ⊥ ψ false 1 ∧
      IsSumOfNaturalModulesVia (stab 𝔛 μ) (Vv 𝔛 μ) (Bloc h.le L μ) ψ true 1 ∧
      commN (natImage ψ (Qv 𝔛 ν)) = coordZero 0 := by
  have hq : 2 ≤ Nat.card F := Finite.one_lt_card
  have hTs : Qv 𝔛 ν ≤ stab 𝔛 μ := qv_le_stab_of_adj _ hμν.symm
  obtain ⟨-, hUq, -, -⟩ := c.edge hμ hμν
  obtain ⟨ψ, hψs, hU, hV⟩ := c.exists_dual_vv hμ
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
  refine ⟨conjSL s ψ, conjSL_surjective hψs, isSumOfNaturalModulesVia_conjSL hU s,
    isSumOfNaturalModulesVia_conjSL_true hV s, ?_⟩
  rw [natImage_conjSL', commN_map_conj, hs]

theorem commN_eq_of_usup_eq {μ ν ν' : Vtx 𝔛} (hμ : IsMVtx 𝔛 μ) (hμν : 𝔄 μ ν) (hμν' : 𝔄 μ ν')
    {ψ : ↥(stab 𝔛 μ) →* ↥(StatedSL 3 F)}
    (hU : IsSumOfNaturalModulesVia (stab 𝔛 μ) (Uloc h.le L μ) ⊥ ψ false 1)
    (he : Usup 𝔛 μ ν = Usup 𝔛 μ ν') :
    commN (natImage ψ (Qv 𝔛 ν)) = commN (natImage ψ (Qv 𝔛 ν')) := by
  ext y
  obtain ⟨w, rfl⟩ := natVec_surjective hU y
  rw [← mem_commutator_iff_natVec hU (qv_le_stab_of_adj _ hμν.symm),
    ← mem_commutator_iff_natVec hU (qv_le_stab_of_adj _ hμν'.symm),
    ← usup_eq_commutator_uloc h c.full hμ hμν, ← usup_eq_commutator_uloc h c.full hμ hμν', he]

theorem coord_mem_pt0 {μ : Vtx 𝔛} (hμ : IsMVtx 𝔛 μ) {ψ : ↥(stab 𝔛 μ) →* ↥(StatedSL 3 F)}
    (N : NatSec (stab 𝔛 μ) (Vv 𝔛 μ) (Bloc h.le L μ) ψ true) {X : Subgroup 𝔘}
    (hX : coordZero 0 ≤ commN (natImage ψ X)) {v : 𝔘} (hv : v ∈ Vv 𝔛 μ)
    (hvX : ∀ k : ↥(stab 𝔛 μ), (k : 𝔘) ∈ X → ⁅v, (k : 𝔘)⁆ ∈ Bloc h.le L μ) :
    N.coord v ∈ pt0 := by
  have hBn : stab 𝔛 μ ≤ Subgroup.normalizer (Bloc h.le L μ : Set 𝔘) :=
    stab_le_normalizer_of_smul (F := fun δ => Bloc h.le L δ) _ (fun g δ => bloc_smul h g δ) μ
  have hvs : v ∈ stab 𝔛 μ := ((vv_le_qv h c.b2 hμ).trans (qv_le_stab _ μ)) hv
  have hfix : ∀ k : ↥(stab 𝔛 μ), (k : 𝔘) ∈ X →
      dualMat (toSL3 ψ k) *ᵥ N.coord v = N.coord v := by
    intro k hk
    have hkv : (k : 𝔘) * v * (k : 𝔘)⁻¹ ∈ Vv 𝔛 μ := N.conj_mem k hv
    have hmem : v⁻¹ * ((k : 𝔘) * v * (k : 𝔘)⁻¹) ∈ Bloc h.le L μ := by
      have e : v⁻¹ * ((k : 𝔘) * v * (k : 𝔘)⁻¹) = v⁻¹ * ⁅v, (k : 𝔘)⁆⁻¹ * v := by
        simp only [commutatorElement_def]
        group
      rw [e]
      have := (Subgroup.mem_normalizer_iff.mp (hBn (Subgroup.inv_mem _ hvs)) _).mp
        (Subgroup.inv_mem _ (hvX k hk))
      simpa [mul_assoc] using this
    have h0 := (N.coord_eq_zero_iff (Subgroup.mul_mem _ (Subgroup.inv_mem _ hv) hkv)).mpr hmem
    rw [N.coord_mul (Subgroup.inv_mem _ hv) hkv, N.coord_inv hv, N.coord_conj k hv,
      natAct_true, neg_add_eq_zero] at h0
    exact h0.symm
  have hperp : commN (natImage ψ X) ≤ orthN (N.coord v) := by
    refine commN_le_orthN fun g hg => ?_
    obtain ⟨k, hkX, rfl⟩ := mem_natImage.mp hg
    exact hfix k hkX
  have h1 : N.coord v ⬝ᵥ Pi.single 1 1 = 0 :=
    hperp (hX (show (Pi.single 1 1 : Fin 3 → F) 0 = 0 by simp))
  have h2 : N.coord v ⬝ᵥ Pi.single 2 1 = 0 :=
    hperp (hX (show (Pi.single 2 1 : Fin 3 → F) 0 = 0 by simp))
  rw [dotProduct_single, mul_one] at h1 h2
  exact ⟨h1, h2⟩

theorem commutator_critR0_qv_one_le {α α' : Vtx 𝔛} (hs : Star 𝔛 α α') :
    ⁅critR0 𝔛 α α', Qv 𝔛 (geo 𝔛 α α' 1)⁆ ≤ Uloc h.le L α := by
  have hα := hs.1.1
  have hαβ : 𝔄 α (geo 𝔛 α α' 1) := adj_geo_one_of_isCritical _ h.critDist_pos hs.1
  have hZβ : ZM 𝔛 α' ≤ Qv 𝔛 (geo 𝔛 α α' 1) := zm_le_qv_geo_one _ h.hyp20 h.critDist_pos hs.1
  have hTs : Qv 𝔛 (geo 𝔛 α α' 1) ≤ stab 𝔛 α := qv_le_stab_of_adj _ hαβ.symm
  obtain ⟨-, hPB, hBG⟩ := c.decomp hα
  have hVc : Vv 𝔛 α ≤ Subgroup.centralizer (Vv 𝔛 α : Set 𝔘) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer).mp (vv_comm_eq_bot h c.b4 hα)
  have hcn : ∀ X Y : Subgroup 𝔘, X ≤ Vv 𝔛 α → Y ≤ Vv 𝔛 α →
      X ≤ Subgroup.normalizer (Y : Set 𝔘) := fun X Y hX hY =>
    ((hX.trans hVc).trans (Subgroup.centralizer_le hY)).trans
      (Subgroup.centralizer_le_normalizer _)
  have hPT : ⁅Pv 𝔛 α, Qv 𝔛 (geo 𝔛 α α' 1)⁆ ≤ Pv 𝔛 α :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp (hTs.trans (stab_le_normalizer_pv _ α))
  have hN : ⁅Pv 𝔛 α, Qv 𝔛 (geo 𝔛 α α' 1)⁆ ⊔ ZM 𝔛 α ≤ Vv 𝔛 α :=
    sup_le (hPT.trans (pv_le_vv h hα)) (zm_le_vv h hα)
  have h1 : ⁅Vv 𝔛 α, Qv 𝔛 (geo 𝔛 α α' 1)⁆ ≤ ⁅Pv 𝔛 α, Qv 𝔛 (geo 𝔛 α α' 1)⁆ ⊔ ZM 𝔛 α := by
    rw [← hPB]
    exact commutator_sup_left_le (hcn _ _ (pv_le_vv h hα) hN) (hcn _ _ (bloc_le_vv h α) hN)
      le_sup_left ((Subgroup.commutator_mono le_rfl hTs).trans (hBG.trans le_sup_right))
  have hUn := stab_le_normalizer_puTrans h.le (S4A.Uq_normal h) α
  have hPTs : ⁅Pv 𝔛 α, Qv 𝔛 (geo 𝔛 α α' 1)⁆ ≤ stab 𝔛 α :=
    hPT.trans ((pv_le_vv h hα).trans ((vv_le_qv h c.b2 hα).trans (qv_le_stab _ α)))
  have hZs : ZM 𝔛 α ≤ stab 𝔛 α := (zm_le_qv_self _ hα h.critDist_pos).trans (qv_le_stab _ α)
  have h2 : ⁅⁅Pv 𝔛 α, Qv 𝔛 (geo 𝔛 α α' 1)⁆ ⊔ ZM 𝔛 α, Qv 𝔛 (geo 𝔛 α α' 1)⁆ ≤
      Uloc h.le L α :=
    commutator_sup_left_le (hPTs.trans hUn) (hZs.trans hUn)
      (c.commutator_commutator_pv_le hα hαβ)
      ((Subgroup.commutator_mono le_rfl hTs).trans (c.commutator_zm_stab_le hα))
  exact (Subgroup.commutator_mono ((Subgroup.commutator_mono le_rfl hZβ).trans h1) le_rfl).trans
    h2

theorem commutator_critR0_qv_two_le (hb6 : critDist 𝔛 = 6) {α α' : Vtx 𝔛} (hs : Star 𝔛 α α') :
    ⁅critR0 𝔛 α α', Qv 𝔛 (geo 𝔛 α α' 2)⁆ ≤ Usup 𝔛 (geo 𝔛 α α' 2) (geo 𝔛 α α' 1) := by
  have h20 := h.hyp20
  have hα := hs.1.1
  have hα' : IsMVtx 𝔛 α' := hs.1.isMVtx_right _ h20
  have hd : (puAmalgam h.le).treeGraph.dist α α' = 6 := hs.1.2.1.trans hb6
  have hd' : (puAmalgam h.le).treeGraph.dist α' α = 6 := by rw [tdist_comm]; exact hd
  have hαβ : 𝔄 α (geo 𝔛 α α' 1) := adj_geo_one _ (by omega)
  have hβδ : 𝔄 (geo 𝔛 α α' 1) (geo 𝔛 α α' 2) := adj_geo _ (i := 1) (by omega)
  have hδM : IsMVtx 𝔛 (geo 𝔛 α α' 2) :=
    (isMVtx_geo _ (by omega)).mpr ⟨fun _ => even_two, fun _ => hα⟩
  have hγM : IsMVtx 𝔛 (geo 𝔛 α' α 2) :=
    (isMVtx_geo _ (by omega)).mpr ⟨fun _ => even_two, fun _ => hα'⟩
  have hργ : 𝔄 (geo 𝔛 α' α 1) (geo 𝔛 α' α 2) := adj_geo _ (i := 1) (by omega)
  have hαn : α ∈ nablaSet h.le L (geo 𝔛 α α' 2) := mem_nablaSet_geo_two h c.full c.cent c.b2 hs.1
  have hγgeo : geo 𝔛 α' α 2 = geo 𝔛 α α' 4 := by
    rw [← geo_symm _ (show 4 ≤ (puAmalgam h.le).treeGraph.dist α α' by omega), hd]
  have hdδγ : (puAmalgam h.le).treeGraph.dist (geo 𝔛 α α' 2) (geo 𝔛 α' α 2) = 2 := by
    rw [hγgeo, dist_geo_geo _ (by omega) (by omega)]
  have hR₀U : critR0 𝔛 α α' ≤ Uloc h.le L (geo 𝔛 α' α 2) := by
    rw [(c.critR0_eq hs).1]
    exact c.usup_le_uloc hγM hργ.symm
  have hR₀V : critR0 𝔛 α α' ≤ Vv 𝔛 (geo 𝔛 α α' 2) := by
    refine hR₀U.trans ((uloc_le_zm h c.full hγM).trans ?_)
    have := zv_le_vv h (α := geo 𝔛 α α' 2) (ρ := geo 𝔛 α' α 2) (by rw [hdδγ])
    rwa [zv_of_isMVtx _ hγM] at this
  have hB : ⁅critR0 𝔛 α α', Qv 𝔛 (geo 𝔛 α α' 2)⁆ ≤ Bloc h.le L (geo 𝔛 α α' 2) :=
    ((Subgroup.commutator_mono hR₀V le_rfl).trans (c.commutator_vv_qv hδM)).trans
      (zm_le_bloc h c.b2 hδM)
  have hU : ⁅critR0 𝔛 α α', Qv 𝔛 (geo 𝔛 α α' 2)⁆ ≤ Uloc h.le L α :=
    (Subgroup.commutator_mono le_rfl (qv_le_qv _ h20 hδM hβδ.symm)).trans
      (c.commutator_critR0_qv_one_le hs)
  rw [← c.uloc_inf_bloc hδM hβδ.symm hαβ.symm hαn]
  exact le_inf hU hB

theorem qv_eq_of_not_mem_nablaSet (hb6 : critDist 𝔛 = 6) {α α' : Vtx 𝔛} (hs : Star 𝔛 α α')
    (h4 : Usup 𝔛 (geo 𝔛 α' α 2) (geo 𝔛 α' α 1) ≠ Usup 𝔛 (geo 𝔛 α' α 2) (geo 𝔛 α' α 3))
    (hγ : geo 𝔛 α' α 2 ∉ nablaSet h.le L (geo 𝔛 α α' 2)) :
    Qv 𝔛 (geo 𝔛 α α' 2) = Qv 𝔛 (geo 𝔛 α' α 2) := by
  have h20 := h.hyp20
  have hq : 2 ≤ Fintype.card F := Fintype.one_lt_card
  have hα := hs.1.1
  have hα' : IsMVtx 𝔛 α' := hs.1.isMVtx_right _ h20
  have hd : (puAmalgam h.le).treeGraph.dist α α' = 6 := hs.1.2.1.trans hb6
  have hd' : (puAmalgam h.le).treeGraph.dist α' α = 6 := by rw [tdist_comm]; exact hd
  set δ := geo 𝔛 α α' 2 with hδdef
  set γ := geo 𝔛 α' α 2 with hγdef
  set τ := geo 𝔛 α' α 3 with hτdef
  have hτgeo : geo 𝔛 α α' 3 = τ := by
    rw [hτdef, ← geo_symm _ (show 3 ≤ (puAmalgam h.le).treeGraph.dist α α' by omega), hd]
  have hδM : IsMVtx 𝔛 δ := (isMVtx_geo _ (by omega)).mpr ⟨fun _ => even_two, fun _ => hα⟩
  have hγM : IsMVtx 𝔛 γ := (isMVtx_geo _ (by omega)).mpr ⟨fun _ => even_two, fun _ => hα'⟩
  have hδτ : 𝔄 δ τ := by rw [← hτgeo]; exact adj_geo _ (i := 2) (by omega)
  have hγτ : 𝔄 γ τ := adj_geo _ (i := 2) (by omega)
  have hργ : 𝔄 (geo 𝔛 α' α 1) γ := adj_geo _ (i := 1) (by omega)
  have hγgeo : γ = geo 𝔛 α α' 4 := by
    rw [hγdef, ← geo_symm _ (show 4 ≤ (puAmalgam h.le).treeGraph.dist α α' by omega), hd]
  have hdδγ : (puAmalgam h.le).treeGraph.dist δ γ = 2 := by
    rw [hγgeo, hδdef, dist_geo_geo _ (by omega) (by omega)]
  have hZγB : ZM 𝔛 γ ≤ Bloc h.le L δ := by
    by_contra hcon
    exact hγ ⟨hdδγ, by rwa [zv_of_isMVtx _ hγM]⟩
  have hQδτ : Qv 𝔛 δ ≤ Qv 𝔛 τ := qv_le_qv _ h20 hδM hδτ
  set N := ⁅ZM 𝔛 γ, Qv 𝔛 δ⁆ with hNdef
  have hNn : stab 𝔛 δ ≤ Subgroup.normalizer (N : Set 𝔘) :=
    c.stab_le_normalizer_commutator_qv hδM hZγB
  have hNτ : N ≤ ZH 𝔛 τ := by
    refine (Subgroup.commutator_mono le_rfl hQδτ).trans ?_
    have := (c.edge hγM hγτ).1
    rwa [Usup, zv_of_isMVtx _ hγM] at this
  have hNZl : N ≤ Zloc h.le L δ := by
    by_contra hNZ
    have hle := uloc_le_of_normal h c.full c.hyp.2.2 hδM (hNτ.trans (zh_le_zm _ hδτ)) hNn hNZ
    have hUc : Uloc h.le L δ ≤ Subgroup.centralizer (Qv 𝔛 τ : Set 𝔘) :=
      (hle.trans hNτ).trans (zh_le_centralizer _ τ)
    have hTU : Qv 𝔛 τ ≤ Qv 𝔛 δ := fun y hy =>
      S46.stab_inf_centralizer_uloc_le_qv h c.hyp.2.2 hδM
        ⟨qv_le_stab_of_adj _ hδτ.symm hy, Subgroup.le_centralizer_iff.mp hUc hy⟩
    have h1 := (c.edge hδM hδτ).2.2.2
    rw [Subgroup.relIndex_eq_one.mpr hTU] at h1
    have : 1 < Fintype.card F ^ 2 := Nat.one_lt_pow (by norm_num) (by omega)
    omega
  have hR₀U : critR0 𝔛 α α' ≤ Uloc h.le L γ := by
    rw [(c.critR0_eq hs).1]
    exact c.usup_le_uloc hγM hργ.symm
  have hR₀Q : ⁅critR0 𝔛 α α', Qv 𝔛 δ⁆ = ⊥ := by
    have h1 := c.commutator_critR0_qv_two_le hb6 hs
    have h2 : ⁅critR0 𝔛 α α', Qv 𝔛 δ⁆ ≤ Zloc h.le L δ :=
      (Subgroup.commutator_mono (hR₀U.trans (uloc_le_zm h c.full hγM)) le_rfl).trans hNZl
    rw [eq_bot_iff, ← uloc_inf_zloc h c.full δ]
    exact le_inf (h1.trans (c.usup_le_uloc hδM (adj_geo _ (i := 1) (by omega)).symm)) h2
  have hQle : Qv 𝔛 δ ≤ Qv 𝔛 γ :=
    c.le_qv_of_le_qv_three hs h4 hQδτ
      (Subgroup.le_centralizer_iff.mp ((Subgroup.commutator_eq_bot_iff_le_centralizer).mp hR₀Q))
  have hfinγ : Finite ↥(Qv 𝔛 γ) := by
    have := finite_stab h hγM
    exact Finite.of_injective _ (Subgroup.inclusion_injective (qv_le_stab _ γ))
  have hcard : Nat.card ↥(Qv 𝔛 γ) ≤ Nat.card ↥(Qv 𝔛 δ) := by
    obtain ⟨g, hg⟩ := exists_smul_eq_of_isMVtx _ hγM hδM
    rw [← hg, qv_smul, Subgroup.card_map_of_injective (MulAut.conj g).injective]
  exact Subgroup.eq_of_le_of_card_ge hQle hcard

theorem false_of_mem_nablaSet (hb6 : critDist 𝔛 = 6) {α α' : Vtx 𝔛} (hs : Star 𝔛 α α')
    (h4 : Usup 𝔛 (geo 𝔛 α' α 2) (geo 𝔛 α' α 1) ≠ Usup 𝔛 (geo 𝔛 α' α 2) (geo 𝔛 α' α 3))
    (hγ : geo 𝔛 α' α 2 ∈ nablaSet h.le L (geo 𝔛 α α' 2)) : False := by
  classical
  have h20 := h.hyp20
  have hq : 2 ≤ Fintype.card F := Fintype.one_lt_card
  have hα := hs.1.1
  have hα' : IsMVtx 𝔛 α' := hs.1.isMVtx_right _ h20
  have hd : (puAmalgam h.le).treeGraph.dist α α' = 6 := hs.1.2.1.trans hb6
  have hd' : (puAmalgam h.le).treeGraph.dist α' α = 6 := by rw [tdist_comm]; exact hd
  set β := geo 𝔛 α α' 1 with hβdef
  set δ := geo 𝔛 α α' 2 with hδdef
  set γ := geo 𝔛 α' α 2 with hγdef
  set τ := geo 𝔛 α' α 3 with hτdef
  set ρ := geo 𝔛 α' α 1 with hρdef
  have hτgeo : geo 𝔛 α α' 3 = τ := by
    rw [hτdef, ← geo_symm _ (show 3 ≤ (puAmalgam h.le).treeGraph.dist α α' by omega), hd]
  have hδM : IsMVtx 𝔛 δ := (isMVtx_geo _ (by omega)).mpr ⟨fun _ => even_two, fun _ => hα⟩
  have hγM : IsMVtx 𝔛 γ := (isMVtx_geo _ (by omega)).mpr ⟨fun _ => even_two, fun _ => hα'⟩
  have hαβ : 𝔄 α β := adj_geo_one _ (by omega)
  have hβδ : 𝔄 β δ := adj_geo _ (i := 1) (by omega)
  have hδτ : 𝔄 δ τ := by rw [← hτgeo]; exact adj_geo _ (i := 2) (by omega)
  have hγτ : 𝔄 γ τ := adj_geo _ (i := 2) (by omega)
  have hργ : 𝔄 ρ γ := adj_geo _ (i := 1) (by omega)
  have hαn : α ∈ nablaSet h.le L δ := mem_nablaSet_geo_two h c.full c.cent c.b2 hs.1
  obtain ⟨hZγQ, -⟩ := c.three hδM hδτ hγτ.symm hγ
  obtain ⟨hZαQ, -⟩ := c.three hδM hβδ.symm hαβ.symm hαn
  have hZαV : ZM 𝔛 α ≤ Vv 𝔛 δ := (zm_le_vv_of_mem_nablaSet h hδM hαn).2
  have hZγV : ZM 𝔛 γ ≤ Vv 𝔛 δ := (zm_le_vv_of_mem_nablaSet h hδM hγ).2
  have hUγZ : Uloc h.le L γ ≤ ZM 𝔛 γ := uloc_le_zm h c.full hγM
  have hVc : Vv 𝔛 δ ≤ Subgroup.centralizer (Vv 𝔛 δ : Set 𝔘) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer).mp (vv_comm_eq_bot h c.b4 hδM)
  have hcn : ∀ X Y : Subgroup 𝔘, X ≤ Vv 𝔛 δ → Y ≤ Vv 𝔛 δ →
      X ≤ Subgroup.normalizer (Y : Set 𝔘) := fun X Y hX hY =>
    ((hX.trans hVc).trans (Subgroup.centralizer_le hY)).trans
      (Subgroup.centralizer_le_normalizer _)
  have hcommV : ∀ X : Subgroup 𝔘, X ≤ Vv 𝔛 δ → ⁅X, Qv 𝔛 δ⁆ ≤ Vv 𝔛 δ := fun X hX =>
    ((Subgroup.commutator_mono hX le_rfl).trans (c.commutator_vv_qv hδM)).trans (zm_le_vv h hδM)
  have hQδτ : Qv 𝔛 δ ≤ Qv 𝔛 τ := qv_le_qv _ h20 hδM hδτ
  have hQδγ : Qv 𝔛 δ ≤ stab 𝔛 γ := hQδτ.trans (qv_le_stab_of_adj _ hγτ.symm)
  have hR₀U : critR0 𝔛 α α' ≤ Uloc h.le L γ := by
    rw [(c.critR0_eq hs).1]
    exact c.usup_le_uloc hγM hργ.symm
  have hUγ : Uloc h.le L γ ≤ critR0 𝔛 α α' ⊔ Usup 𝔛 γ τ := by
    have := c.uloc_le_usup_sup hγM hργ.symm hγτ h4
    rwa [← (c.critR0_eq hs).1] at this
  have hR₀V : critR0 𝔛 α α' ≤ Vv 𝔛 δ := (hR₀U.trans hUγZ).trans hZγV
  have hUγτV : Usup 𝔛 γ τ ≤ Vv 𝔛 δ := ((c.usup_le_uloc hγM hγτ).trans hUγZ).trans hZγV
  have hZlV : Zloc h.le L γ ≤ Vv 𝔛 δ := (zloc_le_zm h c.full hγM).trans hZγV
  have hN₀V := hcommV _ hR₀V
  have hUγτc : ⁅Usup 𝔛 γ τ, Qv 𝔛 δ⁆ = ⊥ :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer).mpr
      (((c.edge hγM hγτ).1.trans (zh_le_centralizer _ τ)).trans (Subgroup.centralizer_le hQδτ))
  have hZlc : ⁅Zloc h.le L γ, Qv 𝔛 δ⁆ = ⊥ :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer).mpr
      ((zloc_le_centralizer_stab h c.full hγM).trans (Subgroup.centralizer_le hQδγ))
  have hZγle : ⁅ZM 𝔛 γ, Qv 𝔛 δ⁆ ≤ ⁅critR0 𝔛 α α', Qv 𝔛 δ⁆ := by
    rw [zm_eq_uloc_sup_zloc h c.full hγM]
    refine commutator_sup_left_le (hcn _ _ (hUγZ.trans hZγV) hN₀V) (hcn _ _ hZlV hN₀V) ?_
      (by rw [hZlc]; exact bot_le)
    refine (Subgroup.commutator_mono hUγ le_rfl).trans ?_
    exact commutator_sup_left_le (hcn _ _ hR₀V hN₀V) (hcn _ _ hUγτV hN₀V) le_rfl
      (by rw [hUγτc]; exact bot_le)
  have hfinS := finite_stab h hδM
  have hUe : Usup 𝔛 δ τ = Usup 𝔛 δ β := by
    have hle : Usup 𝔛 δ τ ≤ Usup 𝔛 δ β := by
      rw [← hZγQ]
      exact hZγle.trans (c.commutator_critR0_qv_two_le hb6 hs)
    have hfin : Finite ↥(Usup 𝔛 δ β) := Finite.of_injective _ (Subgroup.inclusion_injective
      ((c.usup_le_uloc hδM hβδ.symm).trans ((uloc_le_zm h c.full hδM).trans
        ((zm_le_qv_self _ hδM h.critDist_pos).trans (qv_le_stab _ δ)))))
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [(c.edge hδM hδτ).2.1, (c.edge hδM hβδ.symm).2.1]
  have hUδβV : Usup 𝔛 δ β ≤ Vv 𝔛 δ :=
    (c.usup_le_uloc hδM hβδ.symm).trans ((uloc_le_zm h c.full hδM).trans (zm_le_vv h hδM))
  set X := (ZM 𝔛 α ⊔ Uloc h.le L γ) ⊓ Bloc h.le L δ with hXdef
  have hXZ : X ≤ ZM 𝔛 δ := by
    have hY : ⁅X, Qv 𝔛 δ⁆ = ⊥ := by
      refine c.eq_bot_of_normal_of_le_usup hδM hβδ.symm
        (c.stab_le_normalizer_commutator_qv hδM inf_le_right) ?_
      refine (Subgroup.commutator_mono inf_le_left le_rfl).trans ?_
      refine commutator_sup_left_le (hcn _ _ hZαV hUδβV) (hcn _ _ (hUγZ.trans hZγV) hUδβV)
        hZαQ.le ?_
      rw [← hUe, ← hZγQ]
      exact Subgroup.commutator_mono hUγZ le_rfl
    exact c.le_zm_of_commutator_eq_bot hδM (inf_le_right.trans (bloc_le_vv h δ)) hY
  obtain ⟨ψ, -, hU, hVB, hcomm⟩ := c.exists_edge_coords_vv hδM hβδ.symm
  set N := NatSec.ofIsSum hVB with hNdef
  have hcommτ : commN (natImage ψ (Qv 𝔛 τ)) = coordZero 0 := by
    rw [c.commN_eq_of_usup_eq hδM hδτ hβδ.symm hU hUe, hcomm]
  have hZB : ZM 𝔛 δ ≤ Bloc h.le L δ := zm_le_bloc h c.b2 hδM
  have hptα : ∀ x ∈ ZM 𝔛 α, N.coord x ∈ pt0 := by
    intro x hx
    refine c.coord_mem_pt0 hδM N hcomm.ge (hZαV hx) fun k hk => ?_
    refine hZB (zh_le_zm _ hβδ.symm ((c.edge hα hαβ).1 ?_))
    rw [Usup, zv_of_isMVtx _ hα]
    exact Subgroup.commutator_mem_commutator hx hk
  have hptγ : ∀ u ∈ Uloc h.le L γ, N.coord u ∈ pt0 := by
    intro u hu
    refine c.coord_mem_pt0 hδM N hcommτ.ge (hZγV (hUγZ hu)) fun k hk => ?_
    refine hZB (zh_le_zm _ hδτ ((c.edge hγM hγτ).1 ?_))
    rw [Usup, zv_of_isMVtx _ hγM]
    exact Subgroup.commutator_mem_commutator (hUγZ hu) hk
  have hfinU : Finite ↥(Uloc h.le L γ) := by
    have := finite_stab h hγM
    exact Finite.of_injective _ (Subgroup.inclusion_injective
      (hUγZ.trans ((zm_le_qv_self _ hγM h.critDist_pos).trans (qv_le_stab _ γ))))
  have hcard := card_le_card_inf_mul_card_img N (hUγZ.trans hZγV)
  rw [c.uloc_inf_bloc hδM hδτ hγτ.symm hγ, (c.edge hδM hδτ).2.1] at hcard
  obtain ⟨ψ₀, -, hψ₀⟩ := exists_natural_Uloc h c.hyp.2.2 hγM
  rw [card_eq_of_natural hψ₀, Nat.card_eq_fintype_card (α := F)] at hcard
  have himg : Fintype.card F ≤ Nat.card ↥(N.img (Uloc h.le L γ)) := by
    by_contra hlt
    have : Fintype.card F ^ 2 * Nat.card ↥(N.img (Uloc h.le L γ)) <
        Fintype.card F ^ 2 * Fintype.card F :=
      Nat.mul_lt_mul_of_pos_left (not_le.mp hlt) (by positivity)
    have e : Fintype.card F ^ 2 * Fintype.card F = Fintype.card F ^ 3 := by ring
    omega
  have himg_le : N.img (Uloc h.le L γ) ≤ (pt0 : Submodule F (Fin 3 → F)).toAddSubgroup := by
    intro y hy
    obtain ⟨u, hu, -, rfl⟩ := N.mem_img.mp hy
    exact hptγ u hu
  have himg_eq : N.img (Uloc h.le L γ) = (pt0 : Submodule F (Fin 3 → F)).toAddSubgroup := by
    refine AddSubgroup.eq_of_le_of_card_ge himg_le ?_
    have := ML3.card_pt0 (F := F)
    rw [Nat.card_eq_fintype_card (α := F)] at this
    exact this.le.trans himg
  obtain ⟨x, hxZ, hxQ⟩ := IsConcreteLE.not_le_iff_exists.mp hs.1.2.2
  have hxpt : N.coord x ∈ N.img (Uloc h.le L γ) := by
    rw [himg_eq]
    exact hptα x hxZ
  obtain ⟨u, huU, huV, hux⟩ := N.mem_img.mp hxpt
  have hb := N.inv_mul_mem_of_coord_eq huV (hZαV hxZ) hux
  have hbX : u⁻¹ * x ∈ X :=
    ⟨Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.inv_mem _ huU))
      (Subgroup.mem_sup_left hxZ), hb⟩
  have hγQ : ZM 𝔛 γ ≤ Qv 𝔛 α' := zm_le_qv_of_dist_lt _ hγM (by
    rw [hγdef, tdist_comm, dist_geo _ (by omega)]; omega)
  have hδQ : ZM 𝔛 δ ≤ Qv 𝔛 α' := zm_le_qv_of_dist_lt _ hδM (by
    rw [hδdef, dist_geo_right _ (by omega)]; omega)
  apply hxQ
  have := Subgroup.mul_mem _ (hγQ (hUγZ huU)) (hδQ (hXZ hbX))
  rwa [mul_inv_cancel_left] at this

theorem qv_eq_of_six (hb6 : critDist 𝔛 = 6) {α α' : Vtx 𝔛} (hs : Star 𝔛 α α')
    (h4 : Usup 𝔛 (geo 𝔛 α' α 2) (geo 𝔛 α' α 1) ≠ Usup 𝔛 (geo 𝔛 α' α 2) (geo 𝔛 α' α 3)) :
    Qv 𝔛 (geo 𝔛 α α' 2) = Qv 𝔛 (geo 𝔛 α' α 2) := by
  by_cases hγ : geo 𝔛 α' α 2 ∈ nablaSet h.le L (geo 𝔛 α α' 2)
  · exact (c.false_of_mem_nablaSet hb6 hs h4 hγ).elim
  · exact c.qv_eq_of_not_mem_nablaSet hb6 hs h4 hγ

theorem critR0_le_zm_of_six (hb6 : critDist 𝔛 = 6) {α α' : Vtx 𝔛} (hs : Star 𝔛 α α')
    (h4 : Usup 𝔛 (geo 𝔛 α' α 2) (geo 𝔛 α' α 1) ≠ Usup 𝔛 (geo 𝔛 α' α 2) (geo 𝔛 α' α 3)) :
    critR0 𝔛 α α' ≤ ZM 𝔛 (geo 𝔛 α α' 2) := by
  have hα := hs.1.1
  have hα' : IsMVtx 𝔛 α' := hs.1.isMVtx_right _ h.hyp20
  have hd : (puAmalgam h.le).treeGraph.dist α α' = 6 := hs.1.2.1.trans hb6
  have hd' : (puAmalgam h.le).treeGraph.dist α' α = 6 := by rw [tdist_comm]; exact hd
  have hδM : IsMVtx 𝔛 (geo 𝔛 α α' 2) :=
    (isMVtx_geo _ (by omega)).mpr ⟨fun _ => even_two, fun _ => hα⟩
  have hγM : IsMVtx 𝔛 (geo 𝔛 α' α 2) :=
    (isMVtx_geo _ (by omega)).mpr ⟨fun _ => even_two, fun _ => hα'⟩
  have hργ : 𝔄 (geo 𝔛 α' α 1) (geo 𝔛 α' α 2) := adj_geo _ (i := 1) (by omega)
  have hZ : ZM 𝔛 (geo 𝔛 α' α 2) = ZM 𝔛 (geo 𝔛 α α' 2) := by
    rw [← xm_eq_zm h c.full hγM, ← xm_eq_zm h c.full hδM, XM, XM, c.qv_eq_of_six hb6 hs h4]
  rw [← hZ, (c.critR0_eq hs).1]
  exact (c.usup_le_uloc hγM hργ.symm).trans (uloc_le_zm h c.full hγM)

theorem false_of_six (hb6 : critDist 𝔛 = 6)
    (hR : ∀ α α' : Vtx 𝔛, Star 𝔛 α α' →
      Usup 𝔛 (geo 𝔛 α' α 2) (geo 𝔛 α' α 1) ≠ Usup 𝔛 (geo 𝔛 α' α 2) (geo 𝔛 α' α 3) →
      ¬ critR0 𝔛 α α' ≤ ZM 𝔛 (geo 𝔛 α α' 2)) : False := by
  obtain ⟨α', hs, h4⟩ := c.exists_star_ne
  exact hR α₀ α' hs h4 (c.critR0_le_zm_of_six hb6 hs h4)

end Ctx

end CFSG.Quasithin.MS93.S4A.D432
