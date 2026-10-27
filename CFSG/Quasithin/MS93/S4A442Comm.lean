module

public import CFSG.Quasithin.MS93.S4A442
public import CFSG.Quasithin.MS93.S4A442FFD

public section

namespace CFSG.Quasithin.MS93.S4A.P442

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

section Grp

variable {G : Type*} [Group G]

private def commSub'' (H Y N : Subgroup G) (hHN : H ≤ Subgroup.normalizer (N : Set G)) :
    Subgroup G where
  carrier := {v | v ∈ H ∧ ∀ y ∈ Y, ⁅v, y⁆ ∈ N}
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨H.mul_mem ha hb, fun y hy => ?_⟩
    have e : ⁅a * b, y⁆ = a * ⁅b, y⁆ * a⁻¹ * ⁅a, y⁆ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact N.mul_mem ((Subgroup.mem_normalizer_iff.mp (hHN ha) _).mp (hb' y hy)) (ha' y hy)
  one_mem' := ⟨H.one_mem, fun y _ => by simp⟩
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨H.inv_mem ha, fun y hy => ?_⟩
    have e : ⁅a⁻¹, y⁆ = a⁻¹ * ⁅a, y⁆⁻¹ * a⁻¹⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hHN (H.inv_mem ha)) _).mp (N.inv_mem (ha' y hy))

private theorem commutator_sup_le_of'' {A B Y N : Subgroup G}
    (hAN : A ≤ Subgroup.normalizer (N : Set G)) (hBN : B ≤ Subgroup.normalizer (N : Set G))
    (hA : ⁅A, Y⁆ ≤ N) (hB : ⁅B, Y⁆ ≤ N) : ⁅A ⊔ B, Y⁆ ≤ N := by
  have hK : A ⊔ B ≤ commSub'' (A ⊔ B) Y N (sup_le hAN hBN) := by
    refine sup_le (fun v hv => ⟨Subgroup.mem_sup_left hv, fun y hy =>
      hA (Subgroup.commutator_mem_commutator hv hy)⟩) (fun v hv => ⟨Subgroup.mem_sup_right hv,
      fun y hy => hB (Subgroup.commutator_mem_commutator hv hy)⟩)
  rw [Subgroup.commutator_le]
  intro v hv y hy
  exact (hK hv).2 y hy

end Grp

section Vertex

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
  {F : Type} [Field F] [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)} (hφ : IsSL3FullVia M T L φ)
include h hφ

local notation "𝔛" => puAmalgam h.le
local notation "𝔘" => GoldAmalgam.Universal (puAmalgam h.le)

theorem commutator_zm_vv_ne_bot (hC : CentHyp 𝔛) (hb : 4 < critDist 𝔛)
    (hV : ∀ δ δ' : Vtx 𝔛, IsCritical 𝔛 δ δ' → ¬ Vv 𝔛 δ ≤ Qv 𝔛 (geo 𝔛 δ' δ 2))
    (h441 : ∀ δ δ' : Vtx 𝔛, IsCritical 𝔛 δ δ' → Concl441 h.le L δ (geo 𝔛 δ δ' 2))
    {α α' δ : Vtx 𝔛} (hconf : Conf442 𝔛 α α' δ) {g : 𝔘} (hg : g ∈ stab 𝔛 α)
    (hgβ : g • geo 𝔛 α α' 1 = geo 𝔛 α δ 1) :
    ⁅ZM 𝔛 (g • geo 𝔛 α α' 2), Vv 𝔛 δ⁆ ≠ ⊥ := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  have h20 := h.hyp20
  have hb0 := h.critDist_pos
  obtain ⟨n, hn⟩ := ms21_v _ h20
  obtain ⟨hc, hA, hB, hdδ, hpath⟩ := hconf
  have hd : (puAmalgam h.le).treeGraph.dist α α' = critDist 𝔛 := hc.2.1
  have hα : IsMVtx 𝔛 α := hc.1
  have hgα : g • α = α := (mem_stab _).mp hg
  set β := geo 𝔛 α α' 1 with hβdef
  set γ := geo 𝔛 α α' 2 with hγdef
  have hβγ : (puAmalgam h.le).treeGraph.Adj β γ := adj_geo _ (i := 1) (by omega)
  have hγ : IsMVtx 𝔛 γ := isMVtx_geo_two _ h20 hb0 hc
  have hdγ : (puAmalgam h.le).treeGraph.dist α γ = 2 := dist_geo _ (by omega)
  have hδ2 : geo 𝔛 α δ (2 * (n - 1)) = δ := by
    rw [show 2 * (n - 1) = (puAmalgam h.le).treeGraph.dist α δ by omega, geo_dist]
  have hcδ : IsCritical 𝔛 δ γ := by
    have := hpath (n - 1) (by omega) (by omega)
    rwa [hδ2, show critDist 𝔛 - 2 * (n - 1) = 2 by omega] at this
  have hδ : IsMVtx 𝔛 δ := hcδ.1
  have hcγ : IsCritical 𝔛 γ δ := ms22_iii _ h20 hb0 hC hcδ
  have hdγδ : (puAmalgam h.le).treeGraph.dist γ δ = critDist 𝔛 := hcγ.2.1
  have hgeoγδ : geo 𝔛 γ δ 2 = α := by
    symm
    refine eq_geo_of_dist _ (by rw [tdist_comm]; exact hdγ) ?_
    rw [tdist_comm, hdγ, hdγδ]
    omega
  have hN := stab_le_normalizer h hφ hC hb hV h441 hc hA hB
  set V := conjCl (stab 𝔛 α) (ZM 𝔛 γ) with hVdef
  set V₁ := conjCl (stab 𝔛 γ) (ZM 𝔛 α) with hV₁def
  set ν := g • γ with hνdef
  have hVn : stab 𝔛 α ≤ Subgroup.normalizer (V : Set 𝔘) := le_normalizer_conjCl _ _
  have hV₁g : V₁.map (MulAut.conj g).toMonoidHom = conjCl (stab 𝔛 ν) (ZM 𝔛 α) := by
    rw [hV₁def, map_conj_conjCl_zm h, hgα]
  have hV₁le : V₁ ≤ conjCl (stab 𝔛 ν) (ZM 𝔛 α) ⊔ V := by
    have e : (V₁ ⊔ V).map (MulAut.conj g).toMonoidHom = V₁ ⊔ V :=
      map_conj_eq_of_mem_normalizer (hN hg)
    rw [Subgroup.map_sup, hV₁g, map_conj_eq_of_mem_normalizer (hVn hg)] at e
    rw [e]
    exact le_sup_left
  have hZδV : ZM 𝔛 δ ≤ Vv 𝔛 δ := zm_le_vv h hδ
  have hZδα : ZM 𝔛 δ ≤ Qv 𝔛 α := zm_le_qv_of_dist_lt _ hδ (by
    rw [tdist_comm]; omega)
  have hVZ : ⁅V, ZM 𝔛 δ⁆ ≤ ZM 𝔛 γ := by
    have hX := commutator_conjCl_le_dloc_of_le h hφ hC hb hV hcδ (h441 γ δ hcγ) hZδV
      (by rw [hgeoγδ]; exact hZδα)
    rw [hgeoγδ] at hX
    have hQ := commutator_conjCl_le_of_le_dloc h hfull hb hα hdγ hZδα hX
    refine hQ.trans (inf_le_left.trans ?_)
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp
      ((qv_le_qv _ h20 hα (adj_geo_one_of_isCritical _ hb0 hc)).trans
        ((qv_le_stab_of_adj _ hβγ).trans (stab_le_normalizer_zm _ γ)))
  have hV₁Z : ¬ ⁅V₁, ZM 𝔛 δ⁆ ≤ ZM 𝔛 γ := by
    have := not_commutator_conjCl_le_zm h hφ hC hV hcγ
    rwa [hgeoγδ] at this
  have hZn : stab 𝔛 γ ≤ Subgroup.normalizer (ZM 𝔛 γ : Set 𝔘) := stab_le_normalizer_zm _ γ
  have hdν : (puAmalgam h.le).treeGraph.dist α ν = 2 := by
    rw [hνdef, ← hgα, dist_smul, hdγ]
  have hV₁gs : conjCl (stab 𝔛 ν) (ZM 𝔛 α) ≤ stab 𝔛 γ := by
    refine iSup₂_le fun k hk => ?_
    rw [← zm_smul]
    refine zm_le_stab_of_dist_le _ ((isMVtx_smul _ k α).mpr hα) hb0 ?_
    have hkν : k • ν = ν := (mem_stab _).mp hk
    have h1 : (puAmalgam h.le).treeGraph.dist (k • α) ν = 2 := by
      have e := dist_smul _ k α ν
      rw [hkν] at e
      rw [e, hdν]
    have := dist_triangle 𝔛 (k • α) ν γ
    have h2 := dist_triangle 𝔛 ν α γ
    rw [tdist_comm _ ν α, hdν, hdγ] at h2
    omega
  have hVs : V ≤ stab 𝔛 γ := by
    refine iSup₂_le fun k hk => ?_
    rw [← zm_smul]
    refine zm_le_stab_of_dist_le _ ((isMVtx_smul _ k γ).mpr hγ) hb0 ?_
    have hkα : k • α = α := (mem_stab _).mp hk
    have h1 : (puAmalgam h.le).treeGraph.dist (k • γ) α = 2 := by
      have e := dist_smul _ k γ α
      rw [hkα] at e
      rw [e, tdist_comm, hdγ]
    have := dist_triangle 𝔛 (k • γ) α γ
    omega
  have hR₁ : ⁅conjCl (stab 𝔛 ν) (ZM 𝔛 α), ZM 𝔛 δ⁆ ≠ ⊥ := by
    intro hbot
    apply hV₁Z
    refine (Subgroup.commutator_mono hV₁le le_rfl).trans ?_
    exact commutator_sup_le_of'' (hV₁gs.trans hZn) (hVs.trans hZn)
      (by rw [hbot]; exact bot_le) hVZ
  obtain ⟨k, hk, hkZ⟩ : ∃ k ∈ stab 𝔛 ν, ⁅ZM 𝔛 (k • α), ZM 𝔛 δ⁆ ≠ ⊥ := by
    by_contra hall
    push Not at hall
    apply hR₁
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    refine iSup₂_le fun k hk => ?_
    rw [← zm_smul, ← Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact hall k hk
  have hkν : k • ν = ν := (mem_stab _).mp hk
  have hkαM : IsMVtx 𝔛 (k • α) := (isMVtx_smul _ k α).mpr hα
  have hdkα : (puAmalgam h.le).treeGraph.dist (k • α) ν = 2 := by
    have e := dist_smul _ k α ν
    rw [hkν] at e
    rw [e, hdν]
  have hδ₁ν : (puAmalgam h.le).treeGraph.Adj (geo 𝔛 α δ 1) ν := by
    rw [← hgβ, hνdef]
    exact (adj_smul _ g β γ).mpr hβγ
  have hdδ₁δ : (puAmalgam h.le).treeGraph.dist (geo 𝔛 α δ 1) δ = critDist 𝔛 - 3 := by
    rw [dist_geo_right _ (by omega)]
    omega
  have hdνδ : (puAmalgam h.le).treeGraph.dist ν δ ≤ critDist 𝔛 - 2 := by
    have := dist_triangle 𝔛 ν (geo 𝔛 α δ 1) δ
    rw [dist_eq_one_of_adj _ hδ₁ν.symm, hdδ₁δ] at this
    omega
  have hlow : critDist 𝔛 ≤ (puAmalgam h.le).treeGraph.dist (k • α) δ := by
    by_contra hlt
    apply hkZ
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact (zm_le_centralizer_qv _ h20 hkαM).trans (Subgroup.centralizer_le
      (zm_le_qv_of_dist_lt _ hδ (by rw [tdist_comm]; omega)))
  have hup := dist_triangle 𝔛 (k • α) ν δ
  rw [hdkα] at hup
  have hdkδ : (puAmalgam h.le).treeGraph.dist (k • α) δ = critDist 𝔛 := by omega
  have hgeo : ν = geo 𝔛 (k • α) δ 2 := eq_geo_of_dist _ hdkα (by omega)
  have hcδk : IsCritical 𝔛 δ (k • α) := by
    refine ⟨hδ, by rw [tdist_comm]; exact hdkδ, fun hle => hkZ ?_⟩
    rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact hle.trans (Subgroup.le_centralizer_iff.mp (zm_le_centralizer_qv _ h20 hkαM))
  have h43 := hV δ (k • α) hcδk
  rw [← hgeo] at h43
  intro hbot
  apply h43
  have hνM : IsMVtx 𝔛 ν := (isMVtx_smul _ g γ).mpr hγ
  have hVδ₁ : Vv 𝔛 δ ≤ Qv 𝔛 (geo 𝔛 α δ 1) := vv_le_qv_of_dist h hδ (by
    rw [tdist_comm, hdδ₁δ]; omega)
  refine le_qv_of_le_centralizer _ hC hνM hδ₁ν.symm hVδ₁ ?_
  rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
  exact hbot

end Vertex

theorem _root_.CFSG.Quasithin.MS93.S4A.s442Comm_of (h32 : S32) (h43 : S43) (h441 : S441) :
    S442Comm := by
  intro G _ _ M T L h F _ _ φ hH hb α α' δ hconf g hg hgβ
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hH.2.2⟩
  exact commutator_zm_vv_ne_bot h hH.2.2 (centHyp_of_S32 h32 h) hb
    (h43 G M T L h hH.1 hH.2.1 hfull) (h441 G M T L h F inferInstance inferInstance φ hH hb)
    hconf hg hgβ

theorem _root_.CFSG.Quasithin.MS93.S4A.s442_of_s441 (h14 : MS14AS) (hSQ : SQTKQuot) (h32 : S32)
    (h43 : S43) (h441 : S441) : S442 :=
  s442_of h32 h43 h441 (s442Comm_of h32 h43 h441) (s442FFD_of h14 hSQ h32 h43)

end CFSG.Quasithin.MS93.S4A.P442
