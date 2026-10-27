module

public import CFSG.Quasithin.MS93.S4A432H

public section

namespace CFSG.Quasithin.MS93.S4A.D432

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

section Yne

universe u v

variable {A B : Type u} {C : Type v} [Group A] [Group C] [Group B] (X : GoldAmalgam A C B)

@[expose] def Yne (γ τ : Vtx X) : Subgroup X.Universal :=
  ZM X γ ⊔ ⨆ ρ ∈ {ρ : Vtx X | X.treeGraph.Adj γ ρ ∧ Usup X γ ρ ≠ Usup X γ τ}, Vv X ρ

theorem zm_le_yne (γ τ : Vtx X) : ZM X γ ≤ Yne X γ τ := le_sup_left

theorem vv_le_yne_of_ne {γ τ ρ : Vtx X} (hγρ : X.treeGraph.Adj γ ρ)
    (hne : Usup X γ ρ ≠ Usup X γ τ) : Vv X ρ ≤ Yne X γ τ :=
  le_sup_of_le_right (le_iSup₂_of_le (f := fun ρ (_ : ρ ∈ {ρ : Vtx X | X.treeGraph.Adj γ ρ ∧
    Usup X γ ρ ≠ Usup X γ τ}) => Vv X ρ) ρ ⟨hγρ, hne⟩ le_rfl)

theorem map_yne_le {γ τ : Vtx X} {g : X.Universal} (hg : g • γ = γ)
    (hgH : ∀ ρ, X.treeGraph.Adj γ ρ → Usup X γ ρ ≠ Usup X γ τ →
      Usup X γ (g • ρ) ≠ Usup X γ τ) :
    (Yne X γ τ).map (MulAut.conj g).toMonoidHom ≤ Yne X γ τ := by
  rw [Yne, Subgroup.map_sup, ← zm_smul, hg, Subgroup.map_iSup]
  refine sup_le le_sup_left (iSup_le fun ρ => ?_)
  rw [Subgroup.map_iSup]
  refine iSup_le fun hρ => ?_
  have hV : (Vv X ρ).map (MulAut.conj g).toMonoidHom = Vv X (g • ρ) := (vi_smul X g ρ 2).symm
  rw [hV]
  have hadj : X.treeGraph.Adj γ (g • ρ) := by
    have := (adj_smul X g γ ρ).mpr hρ.1
    rwa [hg] at this
  exact vv_le_yne_of_ne X hadj (hgH ρ hρ.1 hρ.2)

end Yne

section Adj

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
include h

theorem vv_le_vv_of_adj {γ ρ : Vtx (puAmalgam h.le)} (hγ : IsMVtx _ γ)
    (hγρ : (puAmalgam h.le).treeGraph.Adj γ ρ) : Vv (puAmalgam h.le) ρ ≤ Vv _ γ := by
  refine iSup₂_le fun x hx => ?_
  simp only [Set.mem_ofPred_eq] at hx
  have htri := dist_triangle (puAmalgam h.le) γ ρ x
  rw [dist_eq_one_of_adj _ hγρ] at htri
  by_cases hd : (puAmalgam h.le).treeGraph.dist γ x ≤ 2
  · exact zv_le_vv h hd
  have h3 : (puAmalgam h.le).treeGraph.dist x γ = 3 := by
    rw [tdist_comm]; omega
  have hx : ¬ IsMVtx (puAmalgam h.le) x := by
    intro hxM
    have := (even_dist_iff (puAmalgam h.le) x γ).mpr ⟨fun _ => hγ, fun _ => hxM⟩
    rw [h3] at this
    exact absurd this (by decide)
  have hadj := adj_geo_one (puAmalgam h.le) (u := x) (w := γ) (by omega)
  have hd2 : (puAmalgam h.le).treeGraph.dist γ (geo (puAmalgam h.le) x γ 1) ≤ 2 := by
    rw [tdist_comm, dist_geo_right _ (by omega), h3]
  have hx' : IsMVtx (puAmalgam h.le) (geo (puAmalgam h.le) x γ 1) := by
    by_contra hx'
    exact hx ((isMVtx_iff_of_adj _ hadj).mpr hx')
  rw [zv_of_not_isMVtx _ hx]
  refine (zh_le_zm _ hadj.symm).trans ?_
  have := zv_le_vv h hd2
  rwa [zv_of_isMVtx _ hx'] at this

theorem isCritical_of_not_le {F : Type} [Field F] [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)}
    (hφ : IsSL3FullVia M T L φ) {α δ : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α)
    (hδ : IsMVtx _ δ) (hd : (puAmalgam h.le).treeGraph.dist α δ = critDist (puAmalgam h.le))
    (hZ : ¬ ZM (puAmalgam h.le) δ ≤ Qv _ α) : IsCritical (puAmalgam h.le) α δ := by
  have hb := h.critDist_pos
  refine ⟨hα, hd, fun hle => hZ ?_⟩
  have hβ := adj_geo_one (puAmalgam h.le) (u := α) (w := δ) (by omega)
  have hZs : ZM (puAmalgam h.le) δ ≤ stab _ α := by
    refine (zm_le_qv_of_dist_lt _ hδ ?_).trans (qv_le_stab_of_adj _ hβ.symm)
    rw [tdist_comm, dist_geo_right _ (by omega), hd]
    omega
  intro z hz
  refine S46.stab_inf_centralizer_uloc_le_qv h hφ hα ⟨hZs hz, ?_⟩
  show z ∈ Subgroup.centralizer (Uloc h.le L α : Set (puAmalgam h.le).Universal)
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  have hu' := hle (uloc_le_zm h (isSL3Full_iff_exists_via.mpr ⟨F, inferInstance, inferInstance,
    φ, hφ⟩) hα hu)
  exact Subgroup.mem_centralizer_iff.mp (zm_le_centralizer_qv _ h.hyp20 hδ hz) u hu'

end Adj

namespace Ctx

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} {h : PUHyp M T L}
  {F : Type} [Field F] [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)}
  {α₀ α₀' : Vtx (puAmalgam h.le)} (c : Ctx h φ α₀ α₀')
include c

local notation "𝔛" => puAmalgam h.le
local notation "𝔘" => GoldAmalgam.Universal (puAmalgam h.le)
local notation "𝔄" => SimpleGraph.Adj (GoldAmalgam.treeGraph (puAmalgam h.le))

theorem exists_usup_ne {γ τ : Vtx 𝔛} (hγ : IsMVtx 𝔛 γ) (hγτ : 𝔄 γ τ) :
    ∃ ρ, 𝔄 γ ρ ∧ Usup 𝔛 γ ρ ≠ Usup 𝔛 γ τ := by
  by_contra hall
  push Not at hall
  have hHn : stab 𝔛 γ ≤ Subgroup.normalizer (Usup 𝔛 γ τ : Set 𝔘) := by
    intro g hg
    have hgγ : g • γ = γ := (mem_stab _).mp hg
    have hadj : 𝔄 γ (g • τ) := by
      have := (adj_smul _ g γ τ).mpr hγτ
      rwa [hgγ] at this
    have hmap : (Usup 𝔛 γ τ).map (MulAut.conj g).toMonoidHom = Usup 𝔛 γ τ := by
      rw [← usup_smul, hgγ]
      exact hall _ hadj
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rw [← hmap]
      exact ⟨x, hx, rfl⟩
    · intro hx
      rw [← hmap] at hx
      obtain ⟨y, hy, hyx⟩ := hx
      have : y = x := by
        have := congrArg (fun w => g⁻¹ * w * g) hyx
        simpa [mul_assoc] using this
      rwa [← this]
  obtain ⟨hUZ, hUq, -, -⟩ := c.edge hγ hγτ
  have hHU := c.usup_le_uloc hγ hγτ
  have hHZ : ¬ Usup 𝔛 γ τ ≤ Zloc h.le L γ := by
    intro hle
    have hbot : Usup 𝔛 γ τ = ⊥ := by
      rw [eq_bot_iff, ← uloc_inf_zloc h c.full γ]
      exact le_inf hHU hle
    rw [hbot, Subgroup.card_bot] at hUq
    have hq : 2 ≤ Fintype.card F := Fintype.one_lt_card
    have : 1 < Fintype.card F ^ 2 := Nat.one_lt_pow (by norm_num) (by omega)
    omega
  have hle := uloc_le_of_normal h c.full c.hyp.2.2 hγ
    (hUZ.trans (zh_le_zm _ hγτ)) hHn hHZ
  have hfinS := finite_stab h hγ
  have hfinH : Finite ↥(Usup 𝔛 γ τ) := Finite.of_injective _ (Subgroup.inclusion_injective
    (hHU.trans ((uloc_le_zm h c.full hγ).trans
      ((zm_le_qv_self _ hγ h.critDist_pos).trans (qv_le_stab _ γ)))))
  have h1 := Subgroup.card_le_of_le hle
  obtain ⟨ψ, -, hψ⟩ := exists_natural_Uloc h c.hyp.2.2 hγ
  rw [card_eq_of_natural hψ, hUq, Nat.card_eq_fintype_card (α := F)] at h1
  have hq : 2 ≤ Fintype.card F := Fintype.one_lt_card
  have : Fintype.card F ^ 2 < Fintype.card F ^ 3 := Nat.pow_lt_pow_right (by omega) (by norm_num)
  omega

theorem pv_le_yne {γ τ : Vtx 𝔛} (hγ : IsMVtx 𝔛 γ) (hγτ : 𝔄 γ τ) : Pv 𝔛 γ ≤ Yne 𝔛 γ τ := by
  classical
  have hq : 2 ≤ Nat.card F := Finite.one_lt_card
  have hb2 := c.b2
  set H := Usup 𝔛 γ τ with hHdef
  set Y := Yne 𝔛 γ τ with hYdef
  have hTs : Qv 𝔛 τ ≤ stab 𝔛 γ := qv_le_stab_of_adj _ hγτ.symm
  obtain ⟨-, hHq, -, -⟩ := c.edge hγ hγτ
  obtain ⟨ψ, hψs, hU, hP⟩ := c.exists_dual hγ
  obtain ⟨hPiB, hPB, -⟩ := c.decomp hγ
  have hVs : Vv 𝔛 γ ≤ stab 𝔛 γ := (vv_le_qv h hb2 hγ).trans (qv_le_stab _ γ)
  have hVn := stab_le_normalizer_vv h γ
  have hBn : stab 𝔛 γ ≤ Subgroup.normalizer (Bloc h.le L γ : Set 𝔘) :=
    stab_le_normalizer_of_smul (F := fun δ => Bloc h.le L δ) _ (fun g δ => bloc_smul h g δ) γ
  have hBV : Bloc h.le L γ ≤ Vv 𝔛 γ := bloc_le_vv h γ
  have hZB : ZM 𝔛 γ ≤ Bloc h.le L γ := zm_le_bloc h hb2 hγ
  have hfin : Module.finrank F ↥(commN (natImage ψ (Qv 𝔛 τ))) = 2 := by
    have := hHq
    rw [usup_eq_commutator_uloc h c.full hγ hγτ, card_commutator_eq hU hTs,
      Module.natCard_eq_pow_finrank (K := F), ← Nat.card_eq_fintype_card] at this
    exact Nat.pow_right_injective hq this
  have hfin0 : Module.finrank F ↥(coordZero 0 : Submodule F (Fin 3 → F)) = 2 := by
    have := card_coordZero_zero (F := F)
    rw [Module.natCard_eq_pow_finrank (K := F)] at this
    exact Nat.pow_right_injective hq this
  obtain ⟨s, hs⟩ := exists_map_plane_eq hfin hfin0
  set ψ' := conjSL s ψ with hψ'
  have hψ's : Function.Surjective ψ' := conjSL_surjective hψs
  have hU' := isSumOfNaturalModulesVia_conjSL hU s
  have hP' := isSumOfNaturalModulesVia_conjSL_true hP s
  have hcomm : commN (natImage ψ' (Qv 𝔛 τ)) = coordZero 0 := by
    rw [hψ', natImage_conjSL', commN_map_conj, hs]
  have hVB := isSumOfNaturalModulesVia_transfer hP' hPB hPiB le_rfl (sup_eq_left.mpr hBV) hVn hBn
    (((pv_le_vv h hγ).trans hVs).trans hBn)
  rw [inf_eq_right.mpr hBV] at hVB
  set N := NatSec.ofIsSum hVB with hN
  have hKH : ∀ k : ↥(stab 𝔛 γ), toSL3 ψ' k ∈ (rowLevi : Subgroup (SL3 F)) →
      ∀ u ∈ H, (k : 𝔘) * u * (k : 𝔘)⁻¹ ∈ H := by
    intro k hk u hu
    have hHU : H ≤ Uloc h.le L γ := c.usup_le_uloc hγ hγτ
    have hku : (k : 𝔘) * u * (k : 𝔘)⁻¹ ∈ Uloc h.le L γ :=
      (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_puTrans h.le (S4A.Uq_normal h) γ k.2)
        u).mp (hHU hu)
    have hu' := hHU hu
    rw [hHdef, usup_eq_commutator_uloc h c.full hγ hγτ] at hu ⊢
    have h1 := (mem_commutator_iff_natVec hU' hTs ⟨u, hu'⟩).mp hu
    rw [hcomm] at h1
    refine (mem_commutator_iff_natVec hU' hTs ⟨_, hku⟩).mpr ?_
    rw [hcomm, natVec_conj hU' k ⟨u, hu'⟩ ⟨_, hku⟩ rfl]
    show (((toSL3 ψ' k : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ natVec hU' ⟨u, hu'⟩) 0 = 0
    rw [rowLevi_mulVec_zero hk]
    exact h1
  have hKY : ∀ k : ↥(stab 𝔛 γ), toSL3 ψ' k ∈ (rowLevi : Subgroup (SL3 F)) →
      ∀ y ∈ Y, (k : 𝔘) * y * (k : 𝔘)⁻¹ ∈ Y := by
    intro k hk y hy
    have hki : toSL3 ψ' k⁻¹ ∈ (rowLevi : Subgroup (SL3 F)) := by
      rw [map_inv]; exact Subgroup.inv_mem _ hk
    have hkγ : (k : 𝔘) • γ = γ := (mem_stab _).mp k.2
    have hmap := map_yne_le 𝔛 (g := (k : 𝔘)) (τ := τ) hkγ (fun ρ hρ hne heq => hne ?_)
    · exact hmap ⟨y, hy, rfl⟩
    have e1 : Usup 𝔛 γ ((k : 𝔘) • ρ) = (Usup 𝔛 γ ρ).map (MulAut.conj (k : 𝔘)).toMonoidHom := by
      rw [← usup_smul, hkγ]
    rw [e1] at heq
    apply le_antisymm
    · intro u hu
      have hku : (k : 𝔘) * u * (k : 𝔘)⁻¹ ∈ H := by
        show (k : 𝔘) * u * (k : 𝔘)⁻¹ ∈ Usup 𝔛 γ τ
        rw [← heq]
        exact ⟨u, hu, rfl⟩
      have := hKH k⁻¹ hki _ hku
      simpa [mul_assoc] using this
    · intro u hu
      have hku : (k : 𝔘) * u * (k : 𝔘)⁻¹ ∈
          (Usup 𝔛 γ ρ).map (MulAut.conj (k : 𝔘)).toMonoidHom := by
        rw [heq]
        exact hKH k hk u hu
      obtain ⟨w, hw, hwe⟩ := hku
      have : w = u := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hwe
        exact mul_left_cancel (mul_right_cancel hwe)
      rwa [← this]
  set S := N.img (Pv 𝔛 γ ⊓ Y) with hSdef
  have hSinv : ∀ g ∈ (ptLevi : Subgroup (SL3 F)), ∀ x ∈ S,
      ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x ∈ S := by
    intro g hg x hx
    obtain ⟨y, ⟨hyP, hyY⟩, hyV, rfl⟩ := N.mem_img.mp hx
    obtain ⟨k, hk⟩ := toSL3_surjective hψ's (transposeInv g)
    have hkrow : toSL3 ψ' k ∈ (rowLevi : Subgroup (SL3 F)) := by
      rw [rowLevi, Subgroup.mem_comap, hk, transposeInv_transposeInv]
      exact hg
    refine N.mem_img.mpr ⟨(k : 𝔘) * y * (k : 𝔘)⁻¹,
      ⟨(Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_pv _ γ k.2) y).mp hyP,
        hKY k hkrow y hyY⟩, N.conj_mem k hyV, ?_⟩
    rw [N.coord_conj k hyV, natAct_true, hk, ← coe_transposeInv, transposeInv_transposeInv]
  rcases ptLevi_invariant_cases S hSinv with hpt | htop
  swap
  ·
    intro p hp
    have hpV := pv_le_vv h hγ hp
    obtain ⟨y, ⟨hyP, hyY⟩, hyV, hyc⟩ := N.mem_img.mp (htop (N.coord p))
    have hmem : y⁻¹ * p ∈ Bloc h.le L γ := N.inv_mul_mem_of_coord_eq hyV hpV hyc
    have hmem' : y⁻¹ * p ∈ ZM 𝔛 γ := by
      rw [← hPiB]
      exact ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ hyP) hp, hmem⟩
    have : p = y * (y⁻¹ * p) := by group
    rw [this]
    exact Subgroup.mul_mem _ hyY (zm_le_yne _ γ τ hmem')
  exfalso
  obtain ⟨ρ₁, hγρ₁, hne₁⟩ := c.exists_usup_ne hγ hγτ
  obtain ⟨δ₁, hρδ₁, hδ₁⟩ := exists_adj_mem_nablaSet_of_dual h c.full c.hyp c.cent c.s42 c.s431A
    c.s431B c.b4 c.star c.kind c.ch hγ hγρ₁
  have hδ₁M := (zm_le_vv_of_mem_nablaSet h hγ hδ₁).1
  obtain ⟨z, hz, hzB⟩ := Set.not_subset.mp (show ¬ ZM 𝔛 δ₁ ≤ Bloc h.le L γ by
    have := hδ₁.2; rwa [zv_of_isMVtx _ hδ₁M] at this)
  have hzV : z ∈ Vv 𝔛 γ := (zm_le_vv_of_mem_nablaSet h hγ hδ₁).2 hz
  have hzY : z ∈ Y := by
    refine vv_le_yne_of_ne 𝔛 hγρ₁ hne₁ ?_
    have := zv_le_vv h (α := ρ₁) (ρ := δ₁) (by rw [dist_eq_one_of_adj _ hρδ₁]; norm_num)
    rw [zv_of_isMVtx _ hδ₁M] at this
    exact this hz
  set v := N.coord z with hv
  have hv0 : v ≠ 0 := by
    rw [hv, Ne, N.coord_eq_zero_iff hzV]
    exact hzB
  have hTρ₁s : Qv 𝔛 ρ₁ ≤ stab 𝔛 γ := qv_le_stab_of_adj _ hγρ₁.symm
  have hfix : ∀ g ∈ natImage ψ' (Qv 𝔛 ρ₁), dualMat g *ᵥ v = v := by
    intro g hg
    obtain ⟨t, htT, rfl⟩ := mem_natImage.mp hg
    have htz : (t : 𝔘) * z * (t : 𝔘)⁻¹ ∈ Vv 𝔛 γ := N.conj_mem t hzV
    have hmem : z⁻¹ * ((t : 𝔘) * z * (t : 𝔘)⁻¹) ∈ Bloc h.le L γ := by
      have e : z⁻¹ * ((t : 𝔘) * z * (t : 𝔘)⁻¹) = ⁅z⁻¹, (t : 𝔘)⁆ := by
        simp only [commutatorElement_def]; group
      rw [e]
      have hc : ⁅z⁻¹, (t : 𝔘)⁆ ∈ Usup 𝔛 δ₁ ρ₁ := by
        rw [Usup, zv_of_isMVtx _ hδ₁M]
        exact Subgroup.commutator_mem_commutator (Subgroup.inv_mem _ hz) htT
      exact hZB (zh_le_zm _ hγρ₁ ((c.edge hδ₁M hρδ₁.symm).1 hc))
    have h0 := (N.coord_eq_zero_iff (Subgroup.mul_mem _ (Subgroup.inv_mem _ hzV) htz)).mpr hmem
    rw [N.coord_mul (Subgroup.inv_mem _ hzV) htz, N.coord_inv hzV, N.coord_conj t hzV,
      natAct_true, neg_add_eq_zero] at h0
    exact h0.symm
  have hvpt : v ∉ pt0 := by
    intro hvp
    have hperp := commN_le_orthN hfix
    have hv00 : v 0 ≠ 0 := by
      intro h0
      apply hv0
      funext i
      fin_cases i
      · exact h0
      · exact hvp.1
      · exact hvp.2
    have horth : orthN v = coordZero 0 := by
      ext x
      show v ⬝ᵥ x = 0 ↔ x 0 = 0
      simp only [dotProduct, Fin.sum_univ_three, hvp.1, hvp.2, zero_mul, add_zero]
      constructor
      · intro hx
        exact (mul_eq_zero.mp hx).resolve_left hv00
      · intro hx
        rw [hx, mul_zero]
    have hfin1 : Module.finrank F ↥(commN (natImage ψ' (Qv 𝔛 ρ₁))) = 2 := by
      have := (c.edge hγ hγρ₁).2.1
      rw [usup_eq_commutator_uloc h c.full hγ hγρ₁, card_commutator_eq hU' hTρ₁s,
        Module.natCard_eq_pow_finrank (K := F), ← Nat.card_eq_fintype_card] at this
      exact Nat.pow_right_injective hq this
    have heq : commN (natImage ψ' (Qv 𝔛 ρ₁)) = commN (natImage ψ' (Qv 𝔛 τ)) := by
      rw [hcomm]
      rw [horth] at hperp
      exact Submodule.eq_of_le_of_finrank_eq hperp (by rw [hfin1, hfin0])
    apply hne₁
    rw [usup_eq_commutator_uloc h c.full hγ hγρ₁, usup_eq_commutator_uloc h c.full hγ hγτ]
    ext u
    constructor
    · intro hu
      have huU : u ∈ Uloc h.le L γ := (c.usup_le_uloc hγ hγρ₁) (by
        rwa [usup_eq_commutator_uloc h c.full hγ hγρ₁])
      have h1 := (mem_commutator_iff_natVec hU' hTρ₁s ⟨u, huU⟩).mp hu
      rw [heq] at h1
      exact (mem_commutator_iff_natVec hU' hTs ⟨u, huU⟩).mpr h1
    · intro hu
      have huU : u ∈ Uloc h.le L γ := (c.usup_le_uloc hγ hγτ) (by
        rwa [usup_eq_commutator_uloc h c.full hγ hγτ])
      have h1 := (mem_commutator_iff_natVec hU' hTs ⟨u, huU⟩).mp hu
      rw [← heq] at h1
      exact (mem_commutator_iff_natVec hU' hTρ₁s ⟨u, huU⟩).mpr h1
  obtain ⟨g, hg, hgv⟩ : ∃ g ∈ (ptLevi : Subgroup (SL3 F)),
      ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v - v ∉ pt0 := by
    rw [mem_pt0, not_and_or] at hvpt
    rcases hvpt with h1 | h2
    · refine ⟨rootElt 2 1 1, rootGroup_le_ptLevi (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))
        (rootElt_mem_rootGroup 2 1 1), ?_⟩
      rw [rootElt_mulVec (by decide), add_sub_cancel_left, mem_pt0, not_and_or]
      right
      simpa using h1
    · refine ⟨rootElt 1 2 1, rootGroup_le_ptLevi (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
        (rootElt_mem_rootGroup 1 2 1), ?_⟩
      rw [rootElt_mulVec (by decide), add_sub_cancel_left, mem_pt0, not_and_or]
      left
      simpa using h2
  obtain ⟨k, hk⟩ := toSL3_surjective hψ's (transposeInv g)
  have hkrow : toSL3 ψ' k ∈ (rowLevi : Subgroup (SL3 F)) := by
    rw [rowLevi, Subgroup.mem_comap, hk, transposeInv_transposeInv]
    exact hg
  have hkz : (k : 𝔘) * z * (k : 𝔘)⁻¹ ∈ Vv 𝔛 γ := N.conj_mem k hzV
  set y := (k : 𝔘) * z * (k : 𝔘)⁻¹ * z⁻¹ with hy
  have hyV : y ∈ Vv 𝔛 γ := Subgroup.mul_mem _ hkz (Subgroup.inv_mem _ hzV)
  have hyP : y ∈ Pv 𝔛 γ := by
    refine Subgroup.mem_sup_left ?_
    have e : y = ⁅z, (k : 𝔘)⁆⁻¹ := by
      rw [hy]; simp only [commutatorElement_def]; group
    rw [e]
    exact Subgroup.inv_mem _ (Subgroup.commutator_mem_commutator hzV k.2)
  have hyY : y ∈ Y := Subgroup.mul_mem _ (hKY k hkrow z hzY) (Subgroup.inv_mem _ hzY)
  have hyS : N.coord y ∈ S := N.mem_img.mpr ⟨y, ⟨hyP, hyY⟩, hyV, rfl⟩
  have hyc : N.coord y = ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v - v := by
    rw [hy, N.coord_mul hkz (Subgroup.inv_mem _ hzV), N.coord_inv hzV, N.coord_conj k hzV,
      natAct_true, hk, ← coe_transposeInv, transposeInv_transposeInv, sub_eq_add_neg]
  exact hgv (hyc ▸ hpt _ hyS)

theorem vv_le_yne {γ τ ρ : Vtx 𝔛} (hγ : IsMVtx 𝔛 γ) (hγτ : 𝔄 γ τ) (hγρ : 𝔄 γ ρ) :
    Vv 𝔛 ρ ≤ Yne 𝔛 γ τ := by
  obtain ⟨ρ₁, hγρ₁, hne₁⟩ := c.exists_usup_ne hγ hγτ
  obtain ⟨g, hg, hgρ⟩ := exists_mem_stab_smul _ hγρ₁ hγρ
  have hV : Vv 𝔛 ρ = (Vv 𝔛 ρ₁).map (MulAut.conj g).toMonoidHom := by
    rw [← hgρ]; exact vi_smul _ g ρ₁ 2
  rw [hV]
  rintro _ ⟨x, hx, rfl⟩
  have hxV : x ∈ Vv 𝔛 γ := vv_le_vv_of_adj h hγ hγρ₁ hx
  have e : (MulAut.conj g).toMonoidHom x = (g * x * g⁻¹ * x⁻¹) * x := by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group
  rw [e]
  refine Subgroup.mul_mem _ (c.pv_le_yne hγ hγτ ?_) (vv_le_yne_of_ne _ hγρ₁ hne₁ hx)
  refine Subgroup.mem_sup_left ?_
  have e' : g * x * g⁻¹ * x⁻¹ = ⁅x, g⁆⁻¹ := by
    simp only [commutatorElement_def]; group
  rw [e']
  exact Subgroup.inv_mem _ (Subgroup.commutator_mem_commutator hxV hg)

theorem exists_star_ne : ∃ α' : Vtx 𝔛, Star 𝔛 α₀ α' ∧
    Usup 𝔛 (geo 𝔛 α' α₀ 2) (geo 𝔛 α' α₀ 1) ≠ Usup 𝔛 (geo 𝔛 α' α₀ 2) (geo 𝔛 α' α₀ 3) := by
  classical
  have hs := c.star
  have hb := c.b4
  have h20 := h.hyp20
  have hα := hs.1.1
  have hα' : IsMVtx 𝔛 α₀' := hs.1.isMVtx_right _ h20
  have hd' : (puAmalgam h.le).treeGraph.dist α₀' α₀ = critDist 𝔛 := by
    rw [tdist_comm]; exact hs.1.2.1
  set γ := geo 𝔛 α₀' α₀ 2 with hγdef
  set τ := geo 𝔛 α₀' α₀ 3 with hτdef
  set ρ₀ := geo 𝔛 α₀' α₀ 1 with hρ₀def
  by_cases h4 : Usup 𝔛 γ ρ₀ = Usup 𝔛 γ τ
  swap
  · exact ⟨α₀', hs, h4⟩
  have hγ : IsMVtx 𝔛 γ := (isMVtx_geo _ (by omega)).mpr ⟨fun _ => even_two, fun _ => hα'⟩
  have hγτ : 𝔄 γ τ := adj_geo _ (i := 2) (by omega)
  have hρ₀γ : 𝔄 ρ₀ γ := adj_geo _ (i := 1) (by omega)
  have hα'ρ₀ : 𝔄 α₀' ρ₀ := adj_geo_one _ (by omega)
  have hdγ : (puAmalgam h.le).treeGraph.dist γ α₀ = critDist 𝔛 - 2 := by
    rw [hγdef, dist_geo_right _ (by omega), hd']
  have hdτ : (puAmalgam h.le).treeGraph.dist τ α₀ = critDist 𝔛 - 3 := by
    rw [hτdef, dist_geo_right _ (by omega), hd']
  have hZY : ZM 𝔛 α₀' ≤ Yne 𝔛 γ τ := by
    have hd1 : (puAmalgam h.le).treeGraph.dist ρ₀ α₀' ≤ 2 := by
      rw [tdist_comm, dist_eq_one_of_adj _ hα'ρ₀]
      norm_num
    have h1 := zv_le_vv h hd1
    rw [zv_of_isMVtx _ hα'] at h1
    exact h1.trans (c.vv_le_yne hγ hγτ hρ₀γ.symm)
  have hnot : ¬ ZM 𝔛 α₀' ≤ Qv 𝔛 α₀ :=
    (isCritical_of_not_le h c.hyp.2.2 hα' hα hd' hs.1.2.2).2.2
  have hZγ : ZM 𝔛 γ ≤ Qv 𝔛 α₀ := zm_le_qv_of_dist_lt _ hγ (by omega)
  obtain ⟨ρ, ⟨hγρ, hne⟩, hρQ⟩ : ∃ ρ ∈ {ρ : Vtx 𝔛 | 𝔄 γ ρ ∧ Usup 𝔛 γ ρ ≠ Usup 𝔛 γ τ},
      ¬ Vv 𝔛 ρ ≤ Qv 𝔛 α₀ := by
    by_contra hall
    push Not at hall
    exact hnot (hZY.trans (sup_le hZγ (iSup₂_le fun ρ hρ => hall ρ hρ)))
  obtain ⟨x, hx, hxQ⟩ : ∃ x ∈ {x : Vtx 𝔛 | (puAmalgam h.le).treeGraph.dist ρ x ≤ 2},
      ¬ Zv 𝔛 x ≤ Qv 𝔛 α₀ := by
    by_contra hall
    push Not at hall
    exact hρQ (iSup₂_le fun x hx => hall x hx)
  simp only [Set.mem_ofPred_eq] at hx
  have hρ : ¬ IsMVtx 𝔛 ρ := (isMVtx_iff_of_adj _ hγρ).mp hγ
  obtain ⟨δ, hρδ, hδM, hδQ⟩ : ∃ δ, 𝔄 ρ δ ∧ IsMVtx 𝔛 δ ∧ ¬ ZM 𝔛 δ ≤ Qv 𝔛 α₀ := by
    rcases Nat.lt_or_ge ((puAmalgam h.le).treeGraph.dist ρ x) 1 with h0 | h1
    · have : ρ = x := (dist_eq_zero_iff _).mp (by omega)
      subst this
      refine ⟨γ, hγρ.symm, hγ, fun hle => hxQ ?_⟩
      rw [zv_of_not_isMVtx _ hρ]
      exact (zh_le_zm _ hγρ).trans hle
    rcases Nat.lt_or_ge ((puAmalgam h.le).treeGraph.dist ρ x) 2 with h1' | h2
    · have hadj : 𝔄 ρ x := SimpleGraph.dist_eq_one_iff_adj.mp (by omega)
      have hxM : IsMVtx 𝔛 x := by
        by_contra hxM
        exact hρ ((isMVtx_iff_of_adj _ hadj).mpr hxM)
      refine ⟨x, hadj, hxM, fun hle => hxQ ?_⟩
      rwa [zv_of_isMVtx _ hxM]
    · have hd2 : (puAmalgam h.le).treeGraph.dist ρ x = 2 := by omega
      have hxH : ¬ IsMVtx 𝔛 x := by
        intro hxM
        have := (even_dist_iff (puAmalgam h.le) ρ x).mp (by rw [hd2]; decide)
        exact hρ (this.mpr hxM)
      have hadj := adj_geo_one (puAmalgam h.le) (u := ρ) (w := x) (by omega)
      have hadj2 : 𝔄 (geo 𝔛 ρ x 1) x := by
        have := adj_geo (puAmalgam h.le) (u := ρ) (w := x) (i := 1) (by omega)
        rwa [show 1 + 1 = (puAmalgam h.le).treeGraph.dist ρ x by omega, geo_dist] at this
      have hδM : IsMVtx 𝔛 (geo 𝔛 ρ x 1) := by
        by_contra hδM
        exact hρ ((isMVtx_iff_of_adj _ hadj).mpr hδM)
      refine ⟨geo 𝔛 ρ x 1, hadj, hδM, fun hle => hxQ ?_⟩
      rw [zv_of_not_isMVtx _ hxH]
      exact (zh_le_zm _ hadj2).trans hle
  have hδγ : δ ≠ γ := by
    rintro rfl
    exact hδQ hZγ
  have hρτ : ρ ≠ τ := by
    rintro rfl
    exact hne rfl
  have hτ1 : τ = geo 𝔛 γ α₀ 1 := eq_geo_one _ hγτ (by omega)
  have hγα : γ ≠ α₀ := by
    intro he
    rw [he, SimpleGraph.dist_self] at hdγ
    omega
  have hdρ : (puAmalgam h.le).treeGraph.dist ρ α₀ = critDist 𝔛 - 1 := by
    rw [dist_eq_add_one_of_adj_of_ne _ hγρ (hτ1 ▸ hρτ) hγα, hdγ]
    omega
  have hγ1 : γ = geo 𝔛 ρ α₀ 1 := eq_geo_one _ hγρ.symm (by omega)
  have hρα : ρ ≠ α₀ := by
    intro he
    rw [he, SimpleGraph.dist_self] at hdρ
    omega
  have hdδ : (puAmalgam h.le).treeGraph.dist δ α₀ = critDist 𝔛 := by
    rw [dist_eq_add_one_of_adj_of_ne _ hρδ (hγ1 ▸ hδγ) hρα, hdρ]
    omega
  have hδ1 : ρ = geo 𝔛 δ α₀ 1 := eq_geo_one _ hρδ.symm (by omega)
  have hdδγ : (puAmalgam h.le).treeGraph.dist δ γ = 2 := by
    have h1 := dist_triangle (puAmalgam h.le) δ ρ γ
    have h2 := dist_triangle (puAmalgam h.le) δ γ α₀
    rw [dist_eq_one_of_adj _ hρδ.symm, dist_eq_one_of_adj _ hγρ.symm] at h1
    omega
  have hδ2 : γ = geo 𝔛 δ α₀ 2 := eq_geo_of_dist _ hdδγ (by omega)
  have hdδτ : (puAmalgam h.le).treeGraph.dist δ τ = 3 := by
    have h1 := dist_triangle (puAmalgam h.le) δ γ τ
    have h2 := dist_triangle (puAmalgam h.le) δ τ α₀
    rw [dist_eq_one_of_adj _ hγτ] at h1
    omega
  have hδ3 : τ = geo 𝔛 δ α₀ 3 := eq_geo_of_dist _ hdδτ (by omega)
  refine ⟨δ, ⟨isCritical_of_not_le h c.hyp.2.2 hα hδM (by rw [tdist_comm]; exact hdδ) hδQ, ?_⟩,
    ?_⟩
  · rw [← hδ2]
    exact hs.2
  · rw [← hδ1, ← hδ2, ← hδ3]
    exact hne

end Ctx

end CFSG.Quasithin.MS93.S4A.D432
