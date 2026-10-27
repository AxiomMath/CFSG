module

public import CFSG.Quasithin.MS93.S4A443
public import CFSG.Quasithin.MS93.S4A444
public import CFSG.Quasithin.MS93.S4A44Good

public section

namespace CFSG.Quasithin.MS93.S4A

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

section Tools

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
  {F : Type} [Field F] [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)} (hφ : IsSL3FullVia M T L φ)
include h hφ

theorem commutator_zm_vv_le_dloc_geo (hC : CentHyp (puAmalgam h.le))
    (hb : 4 < critDist (puAmalgam h.le))
    (hV : ∀ δ δ' : Vtx (puAmalgam h.le), IsCritical (puAmalgam h.le) δ δ' →
      ¬ Vv (puAmalgam h.le) δ ≤ Qv _ (geo _ δ' δ 2))
    (h441 : ∀ δ δ' : Vtx (puAmalgam h.le), IsCritical (puAmalgam h.le) δ δ' →
      Concl441 h.le L δ (geo (puAmalgam h.le) δ δ' 2))
    {γ x : Vtx (puAmalgam h.le)} (hγ : IsMVtx _ γ) (hx : IsMVtx _ x)
    (hd : (puAmalgam h.le).treeGraph.dist γ x + 2 = critDist (puAmalgam h.le)) :
    ⁅ZM (puAmalgam h.le) γ, Vv (puAmalgam h.le) x⁆ ≤ Dloc h.le L (geo _ γ x 2) := by
  have hb0 := h.critDist_pos
  have hDn := stab_le_normalizer_dloc h (geo (puAmalgam h.le) γ x 2)
  have hdy : (puAmalgam h.le).treeGraph.dist x (geo _ γ x 2) =
      critDist (puAmalgam h.le) - 4 := by
    rw [tdist_comm, dist_geo_right _ (by omega)]
    omega
  have hVs : Vv (puAmalgam h.le) x ≤ stab _ (geo _ γ x 2) :=
    (vv_le_qv_of_dist h hx (by omega)).trans (qv_le_stab _ _)
  have hVeq : Vv (puAmalgam h.le) x = ⨆ ρ : {ρ : Vtx (puAmalgam h.le) //
      (puAmalgam h.le).treeGraph.dist x ρ ≤ 2}, Zv (puAmalgam h.le) (ρ : Vtx (puAmalgam h.le)) :=
    iSup_subtype'
  rw [Subgroup.commutator_comm, hVeq]
  refine commutator_iSup_le_of (fun ρ => ?_) (hVeq ▸ hVs.trans hDn)
  obtain ⟨ρ, hρ⟩ := ρ
  obtain ⟨μ, hμ, hdμ, hρμ⟩ := exists_zv_le_zm h hx hρ
  refine (Subgroup.commutator_mono hρμ le_rfl).trans ?_
  by_cases hZ : ZM (puAmalgam h.le) γ ≤ Qv _ μ
  · rw [(Subgroup.commutator_eq_bot_iff_le_centralizer).mpr
      ((zm_le_centralizer_qv _ h.hyp20 hμ).trans (Subgroup.centralizer_le hZ))]
    exact bot_le
  · have t1 := dist_triangle _ γ x μ
    have hge : critDist (puAmalgam h.le) ≤ (puAmalgam h.le).treeGraph.dist γ μ := by
      by_contra hlt
      exact hZ (zm_le_qv_of_dist_lt _ hγ (by omega))
    have hcγμ : IsCritical (puAmalgam h.le) γ μ := ⟨hγ, by omega, hZ⟩
    have hxμ : x = geo (puAmalgam h.le) γ μ (critDist (puAmalgam h.le) - 2) :=
      eq_geo_of_dist _ (by omega) (by omega)
    have hgeo : geo (puAmalgam h.le) γ x 2 = geo _ γ μ 2 := by
      rw [hxμ, geo_geo _ (by omega) (by omega)]
    rw [hgeo]
    exact critR_le_dloc h hφ hC hb hV (ms22_iii _ h.hyp20 hb0 hC hcγμ) (h441 γ μ hcγμ)

end Tools

section Mirror

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
include h

theorem IsGoodPathB.exists_ltil_mirror (hfull : IsSL3Full M T L) {p : ℕ → Vtx (puAmalgam h.le)}
    {N : ℕ} (hp : IsGoodPathB _ p N) {i : ℕ} (hie : Even i) (hi2 : 2 ≤ i) (hiN : i + 2 ≤ N) :
    ∃ s ∈ Ltil h.le L (p i), s • p (i + 2) = p (i - 2) ∧ s • p (i + 1) = p (i - 1) := by
  have hnb := hp.toIsNBPath
  obtain ⟨g, hg, hge⟩ := hp.straight i hie hi2 hiN
  have hM : IsMVtx (puAmalgam h.le) (p i) :=
    (hnb.isMVtx_iff (by omega)).mpr ⟨fun _ => hie, fun _ => hp.mvtx⟩
  have hadj1 : (puAmalgam h.le).treeGraph.Adj (p i) (p (i + 1)) := hp.adj i (by omega)
  have hadj2 : (puAmalgam h.le).treeGraph.Adj (p (i + 1)) (p (i + 2)) := hp.adj (i + 1) (by omega)
  obtain ⟨l, hl, hle⟩ := exists_ltil_smul_eq h hfull hM hadj1 hadj2 hg
  refine ⟨l, hl, hle.trans hge, ?_⟩
  have hls : l • p i = p i := (mem_stab _).mp (ltil_le_stab h _ hl)
  have hadj3 : (puAmalgam h.le).treeGraph.Adj (p (i - 2)) (p (i - 1)) := by
    have := hp.adj (i - 2) (by omega)
    rwa [show i - 2 + 1 = i - 1 by omega] at this
  have hadj4 : (puAmalgam h.le).treeGraph.Adj (p (i - 1)) (p i) := by
    have := hp.adj (i - 1) (by omega)
    rwa [show i - 1 + 1 = i by omega] at this
  apply eq_of_adj_adj_of_dist_eq_two h (u := p i) (w := p (i - 2))
  · rw [← hls]
    exact (adj_smul _ l _ _).mpr hadj1
  · rw [← hle.trans hge]
    exact (adj_smul _ l _ _).mpr hadj2
  · exact hadj4.symm
  · exact hadj3.symm
  · rw [tdist_comm, hnb.dist_eq' (by omega) (by omega)]
    omega

theorem IsGoodPathB.usup_eq_of_le_dloc (hfull : IsSL3Full M T L) {p : ℕ → Vtx (puAmalgam h.le)}
    {N : ℕ} (hp : IsGoodPathB _ p N) {i : ℕ} (hie : Even i) (hi2 : 2 ≤ i) (hiN : i + 2 ≤ N)
    {W : Subgroup (puAmalgam h.le).Universal} (hW : W ≤ Dloc h.le L (p i))
    (hWe : W = Usup (puAmalgam h.le) (p (i + 2)) (p (i + 1)) ∨
      W = Usup (puAmalgam h.le) (p (i - 2)) (p (i - 1))) :
    Usup (puAmalgam h.le) (p (i + 2)) (p (i + 1)) =
      Usup (puAmalgam h.le) (p (i - 2)) (p (i - 1)) := by
  obtain ⟨s, hsL, hsa, hsb⟩ := hp.exists_ltil_mirror h hfull hie hi2 hiN
  have hM : IsMVtx (puAmalgam h.le) (p i) :=
    (hp.toIsNBPath.isMVtx_iff (by omega)).mpr ⟨fun _ => hie, fun _ => hp.mvtx⟩
  have hcen := dloc_le_centralizer_ltil h hM
  have hfix : W.map (MulAut.conj s).toMonoidHom = W := by
    refine le_antisymm ?_ fun x hx => ⟨x, hx, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩
      have hxs : s * x = x * s := Subgroup.mem_centralizer_iff.mp (hcen (hW hx)) s hsL
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hxs, mul_inv_cancel_right]
      exact hx
    · have hxs : s * x = x * s := Subgroup.mem_centralizer_iff.mp (hcen (hW hx)) s hsL
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hxs, mul_inv_cancel_right]
  have himg : (Usup (puAmalgam h.le) (p (i + 2)) (p (i + 1))).map (MulAut.conj s).toMonoidHom =
      Usup (puAmalgam h.le) (p (i - 2)) (p (i - 1)) := by
    rw [← usup_smul, hsa, hsb]
  rcases hWe with rfl | rfl
  · rw [← himg, hfix]
  · have hinj : Function.Injective (MulAut.conj s).toMonoidHom := (MulAut.conj s).injective
    apply Subgroup.map_injective hinj
    rw [himg, hfix]

end Mirror

section Step1

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
  {F : Type} [Field F] [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)} (hφ : IsSL3FullVia M T L φ)
include h hφ

theorem IsGoodPathB.commutator_uloc_vv_ne_usup (hC : CentHyp (puAmalgam h.le))
    (hb6 : 6 < critDist (puAmalgam h.le))
    (hV : ∀ δ δ' : Vtx (puAmalgam h.le), IsCritical (puAmalgam h.le) δ δ' →
      ¬ Vv (puAmalgam h.le) δ ≤ Qv _ (geo _ δ' δ 2))
    (h441 : ∀ δ δ' : Vtx (puAmalgam h.le), IsCritical (puAmalgam h.le) δ δ' →
      Concl441 h.le L δ (geo (puAmalgam h.le) δ δ' 2))
    {p : ℕ → Vtx (puAmalgam h.le)} (hp : IsGoodPathB _ p (critDist (puAmalgam h.le) + 8)) :
    ⁅Uloc h.le L (p (critDist (puAmalgam h.le) + 4)), Vv (puAmalgam h.le) (p 6)⁆ ≠
      Usup (puAmalgam h.le) (p (critDist (puAmalgam h.le) + 4))
        (p (critDist (puAmalgam h.le) + 3)) := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  have hb : 4 < critDist (puAmalgam h.le) := by omega
  have hb0 := h.critDist_pos
  have hnb := hp.toIsNBPath
  obtain ⟨k, hk⟩ := ms21_v _ h.hyp20
  have hM : ∀ i, Even i → i ≤ critDist (puAmalgam h.le) + 8 → IsMVtx (puAmalgam h.le) (p i) :=
    fun i hi hiN => (hnb.isMVtx_iff hiN).mpr ⟨fun _ => hi, fun _ => hp.mvtx⟩
  have hd : ∀ i j, i ≤ j → j ≤ critDist (puAmalgam h.le) + 8 →
      (puAmalgam h.le).treeGraph.dist (p i) (p j) = j - i := fun i j hij hj => hnb.dist_eq' hij hj
  have hd' : ∀ i j, i ≤ j → j ≤ critDist (puAmalgam h.le) + 8 →
      (puAmalgam h.le).treeGraph.dist (p j) (p i) = j - i := fun i j hij hj => by
    rw [tdist_comm]; exact hd i j hij hj
  have hadj : ∀ i j, j = i + 1 → j ≤ critDist (puAmalgam h.le) + 8 →
      (puAmalgam h.le).treeGraph.Adj (p i) (p j) := fun i j hij hj => by
    subst hij; exact hp.adj i (by omega)
  have hα := hM (critDist (puAmalgam h.le) + 4) ⟨k + 2, by omega⟩ (by omega)
  have hα' := hM 4 ⟨2, rfl⟩ (by omega)
  have hp6 := hM 6 ⟨3, rfl⟩ (by omega)
  have hβα := hadj (critDist (puAmalgam h.le) + 3) (critDist (puAmalgam h.le) + 4) rfl (by omega)
  have hVβ : Vv (puAmalgam h.le) (p 6) ≤ Qv _ (p (critDist (puAmalgam h.le) + 3)) :=
    vv_le_qv_of_dist h hp6 (by rw [hd 6 _ (by omega) (by omega)]; omega)
  have hVs : Vv (puAmalgam h.le) (p 6) ≤ stab _ (p (critDist (puAmalgam h.le) + 4)) :=
    hVβ.trans (qv_le_stab_of_adj _ hβα)
  have hp8 := hM 8 ⟨4, rfl⟩ (by omega)
  have hp0 := hM 0 ⟨0, rfl⟩ (by omega)
  have hpe0 : ¬ ZM (puAmalgam h.le) (p 0) ≤ Subgroup.normalizer
      (Usup (puAmalgam h.le) (p (critDist (puAmalgam h.le))) (p (critDist (puAmalgam h.le) + 1)) :
        Set (puAmalgam h.le).Universal) := by
    have := hp.pe (critDist (puAmalgam h.le)) ⟨k, hk⟩ le_rfl (by omega)
    rwa [Nat.sub_self] at this
  intro heq
  have hY := commutator_zm_vv_le_dloc_geo h hφ hC hb hV h441 hα hp6
    (by rw [hd' 6 _ (by omega) (by omega)]; omega)
  have hg2 : geo (puAmalgam h.le) (p (critDist (puAmalgam h.le) + 4)) (p 6) 2 =
      p (critDist (puAmalgam h.le) + 2) := by
    rw [hnb.eq_geo_rev (i := 6) (j := critDist (puAmalgam h.le) + 4)
      (k := critDist (puAmalgam h.le) + 2) (by omega) (by omega) (by omega)]
    congr 1
    omega
  rw [hg2, commutator_zm_eq_uloc h hfull hα hVs, heq] at hY
  have hmir := hp.usup_eq_of_le_dloc h hfull (i := critDist (puAmalgam h.le) + 2)
    ⟨k + 1, by omega⟩ (by omega) (by omega) hY (Or.inl (by
      rw [show critDist (puAmalgam h.le) + 2 + 2 = critDist (puAmalgam h.le) + 4 by omega,
        show critDist (puAmalgam h.le) + 2 + 1 = critDist (puAmalgam h.le) + 3 by omega]))
  rw [show critDist (puAmalgam h.le) + 2 + 2 = critDist (puAmalgam h.le) + 4 by omega,
    show critDist (puAmalgam h.le) + 2 + 1 = critDist (puAmalgam h.le) + 3 by omega,
    show critDist (puAmalgam h.le) + 2 - 2 = critDist (puAmalgam h.le) by omega,
    show critDist (puAmalgam h.le) + 2 - 1 = critDist (puAmalgam h.le) + 1 by omega] at hmir
  have hcen : Usup (puAmalgam h.le) (p (critDist (puAmalgam h.le) + 4))
      (p (critDist (puAmalgam h.le) + 3)) ≤
        Subgroup.centralizer (ZM (puAmalgam h.le) (p 0) : Set (puAmalgam h.le).Universal) := by
    rcases (show 10 ≤ critDist (puAmalgam h.le) ∨ critDist (puAmalgam h.le) = 8 by omega)
      with h10 | h8
    · have hUV : ⁅Uloc h.le L (p (critDist (puAmalgam h.le) + 4)),
          Vv (puAmalgam h.le) (p 6)⁆ ≤ Vv (puAmalgam h.le) (p 6) := by
        rw [Subgroup.commutator_comm]
        refine Subgroup.le_normalizer_iff_commutator_le_left.mp ?_
        refine (uloc_le_zm h hfull hα).trans ((zm_le_qv_of_dist_lt _ hα ?_).trans
          ((qv_le_stab _ _).trans (stab_le_normalizer_vv h _)))
        rw [hd' 6 _ (by omega) (by omega)]
        omega
      rw [← heq]
      exact hUV.trans (vv_le_centralizer_zm _ h.hyp20 hp0
        (by rw [hd 0 6 (by omega) (by omega)]; omega))
    ·
      have hD6 : Usup (puAmalgam h.le) (p (critDist (puAmalgam h.le) + 4))
          (p (critDist (puAmalgam h.le) + 3)) ≤ Dloc h.le L (p 6) := by
        rw [← heq, ← commutator_zm_eq_uloc h hfull hα hVs]
        exact commutator_zm_vv_le_dloc h hφ hC hb hV h441 hα hp6
          (by rw [hd' 6 _ (by omega) (by omega)]; omega)
      obtain ⟨s, hsL, hsa, -⟩ := hp.exists_ltil_mirror h hfull (i := 6) ⟨3, rfl⟩ (by omega)
        (by omega)
      have hcs := dloc_le_centralizer_ltil h hp6
      have hZ8 : Usup (puAmalgam h.le) (p (critDist (puAmalgam h.le) + 4))
          (p (critDist (puAmalgam h.le) + 3)) ≤ ZM (puAmalgam h.le) (p 8) := by
        rw [hmir, h8, Usup, zv_of_isMVtx _ hp8]
        exact Subgroup.le_normalizer_iff_commutator_le_left.mp
          ((qv_le_stab_of_adj _ (hadj 8 9 rfl (by omega)).symm).trans
            (stab_le_normalizer_zm _ _))
      have hZ4 : Usup (puAmalgam h.le) (p (critDist (puAmalgam h.le) + 4))
          (p (critDist (puAmalgam h.le) + 3)) ≤ ZM (puAmalgam h.le) (p 4) := by
        intro x hx
        have hxs : s * x = x * s := Subgroup.mem_centralizer_iff.mp (hcs (hD6 hx)) s hsL
        have hx' : s * x * s⁻¹ ∈ ZM (puAmalgam h.le) (s • p 8) := by
          rw [zm_smul]
          exact ⟨x, hZ8 hx, rfl⟩
        rw [hsa, show 6 - 2 = 4 from rfl, hxs, mul_inv_cancel_right] at hx'
        exact hx'
      exact hZ4.trans ((zm_le_centralizer_qv _ h.hyp20 hα').trans (Subgroup.centralizer_le
        (zm_le_qv_of_dist_lt _ hp0 (by rw [hd 0 4 (by omega) (by omega)]; omega))))
  apply hpe0
  rw [← hmir]
  exact le_normalizer_of_le_centralizer (Subgroup.le_centralizer_iff.mp hcen)

theorem IsGoodPathB.card_commutator_uloc_vv (hC : CentHyp (puAmalgam h.le))
    (hb6 : 6 < critDist (puAmalgam h.le))
    (hV : ∀ δ δ' : Vtx (puAmalgam h.le), IsCritical (puAmalgam h.le) δ δ' →
      ¬ Vv (puAmalgam h.le) δ ≤ Qv _ (geo _ δ' δ 2))
    (h441 : ∀ δ δ' : Vtx (puAmalgam h.le), IsCritical (puAmalgam h.le) δ δ' →
      Concl441 h.le L δ (geo (puAmalgam h.le) δ δ' 2))
    {p : ℕ → Vtx (puAmalgam h.le)} (hp : IsGoodPathB _ p (critDist (puAmalgam h.le) + 8)) :
    ⁅Uloc h.le L (p (critDist (puAmalgam h.le) + 4)), ZM (puAmalgam h.le) (p 4)⁆ =
      ⁅Uloc h.le L (p (critDist (puAmalgam h.le) + 4)), Vv (puAmalgam h.le) (p 6)⁆ ∧
    Nat.card ↥⁅Uloc h.le L (p (critDist (puAmalgam h.le) + 4)), Vv (puAmalgam h.le) (p 6)⁆ =
      Fintype.card F := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  have hb : 4 < critDist (puAmalgam h.le) := by omega
  have hb0 := h.critDist_pos
  have hnb := hp.toIsNBPath
  obtain ⟨k, hk⟩ := ms21_v _ h.hyp20
  have hM : ∀ i, Even i → i ≤ critDist (puAmalgam h.le) + 8 → IsMVtx (puAmalgam h.le) (p i) :=
    fun i hi hiN => (hnb.isMVtx_iff hiN).mpr ⟨fun _ => hi, fun _ => hp.mvtx⟩
  have hd : ∀ i j, i ≤ j → j ≤ critDist (puAmalgam h.le) + 8 →
      (puAmalgam h.le).treeGraph.dist (p i) (p j) = j - i := fun i j hij hj => hnb.dist_eq' hij hj
  have hd' : ∀ i j, i ≤ j → j ≤ critDist (puAmalgam h.le) + 8 →
      (puAmalgam h.le).treeGraph.dist (p j) (p i) = j - i := fun i j hij hj => by
    rw [tdist_comm]; exact hd i j hij hj
  have hadj : ∀ i j, j = i + 1 → j ≤ critDist (puAmalgam h.le) + 8 →
      (puAmalgam h.le).treeGraph.Adj (p i) (p j) := fun i j hij hj => by
    subst hij; exact hp.adj i (by omega)
  have hα := hM (critDist (puAmalgam h.le) + 4) ⟨k + 2, by omega⟩ (by omega)
  have hα' := hM 4 ⟨2, rfl⟩ (by omega)
  have hp6 := hM 6 ⟨3, rfl⟩ (by omega)
  have hβα := hadj (critDist (puAmalgam h.le) + 3) (critDist (puAmalgam h.le) + 4) rfl (by omega)
  have hVβ : Vv (puAmalgam h.le) (p 6) ≤ Qv _ (p (critDist (puAmalgam h.le) + 3)) :=
    vv_le_qv_of_dist h hp6 (by rw [hd 6 _ (by omega) (by omega)]; omega)
  have hVs : Vv (puAmalgam h.le) (p 6) ≤ stab _ (p (critDist (puAmalgam h.le) + 4)) :=
    hVβ.trans (qv_le_stab_of_adj _ hβα)
  have hc4 : IsCritical (puAmalgam h.le) (p (critDist (puAmalgam h.le) + 4)) (p 4) := by
    have := hp.crit 4 ⟨2, rfl⟩ (by omega)
    rwa [show 4 + critDist (puAmalgam h.le) = critDist (puAmalgam h.le) + 4 by omega] at this
  have hZs : ZM (puAmalgam h.le) (p 4) ≤ stab _ (p (critDist (puAmalgam h.le) + 4)) :=
    zm_le_stab_of_isCritical _ h.hyp20 hb0 hc4
  have hZβ : ZM (puAmalgam h.le) (p 4) ≤ Qv _ (p (critDist (puAmalgam h.le) + 3)) :=
    zm_le_qv_of_dist_lt _ hα' (by rw [hd 4 _ (by omega) (by omega)]; omega)
  have hZV : ZM (puAmalgam h.le) (p 4) ≤ Vv _ (p 6) := by
    rw [← zv_of_isMVtx _ hα']
    exact zv_le_vv h (by rw [hd' 4 6 (by omega) (by omega)])
  have hRne : ⁅Uloc h.le L (p (critDist (puAmalgam h.le) + 4)), ZM (puAmalgam h.le) (p 4)⁆ ≠ ⊥ := by
    rw [← commutator_zm_eq_uloc h hfull hα hZs]
    exact ms22_ii _ h.hyp20 hb0 hC hc4
  have hRq := le_card_commutator_uloc h hφ hα hβα.symm hZβ hRne
  have hne2 := hp.commutator_uloc_vv_ne_usup h hφ hC hb6 hV h441
  have hq : 1 < Fintype.card F := by
    rw [← Nat.card_eq_fintype_card]
    exact Finite.one_lt_card
  obtain ⟨d, hd2, hcard⟩ := S46.card_commutator_uloc_le h hφ hα hβα.symm hVβ
  have hRV : ⁅Uloc h.le L (p (critDist (puAmalgam h.le) + 4)), ZM (puAmalgam h.le) (p 4)⁆ ≤
      ⁅Uloc h.le L (p (critDist (puAmalgam h.le) + 4)), Vv (puAmalgam h.le) (p 6)⁆ :=
    Subgroup.commutator_mono le_rfl hZV
  have hUVle : ⁅Uloc h.le L (p (critDist (puAmalgam h.le) + 4)), Vv (puAmalgam h.le) (p 6)⁆ ≤
      Usup (puAmalgam h.le) (p (critDist (puAmalgam h.le) + 4))
        (p (critDist (puAmalgam h.le) + 3)) := by
    rw [Usup, zv_of_isMVtx _ hα]
    exact Subgroup.commutator_mono (uloc_le_zm h hfull hα) hVβ
  have hfinU : Finite ↥(Usup (puAmalgam h.le) (p (critDist (puAmalgam h.le) + 4))
      (p (critDist (puAmalgam h.le) + 3))) :=
    Nat.finite_of_card_ne_zero (by
      rw [card_usup_eq_sq h hφ hC hb hα hβα.symm]
      exact pow_ne_zero _ Fintype.card_ne_zero)
  have hfin1 : Finite ↥⁅Uloc h.le L (p (critDist (puAmalgam h.le) + 4)),
      Vv (puAmalgam h.le) (p 6)⁆ := Finite.of_injective _ (Subgroup.inclusion_injective hUVle)
  have hd1 : d = 1 := by
    rcases (show d = 0 ∨ d = 1 ∨ d = 2 by omega) with h0 | h1 | h2
    · have := Subgroup.card_le_of_le hRV
      rw [hcard, h0, pow_zero] at this
      omega
    · exact h1
    · exfalso
      apply hne2
      exact Subgroup.eq_of_le_of_card_ge hUVle
        (by rw [card_usup_eq_sq h hφ hC hb hα hβα.symm, hcard, h2])
  have hRUV : ⁅Uloc h.le L (p (critDist (puAmalgam h.le) + 4)), ZM (puAmalgam h.le) (p 4)⁆ =
      ⁅Uloc h.le L (p (critDist (puAmalgam h.le) + 4)), Vv (puAmalgam h.le) (p 6)⁆ :=
    Subgroup.eq_of_le_of_card_ge hRV (by rw [hcard, hd1, pow_one]; exact hRq)
  exact ⟨hRUV, by rw [hcard, hd1, pow_one]⟩

theorem IsGoodPathB.commutator_uloc_zm_eq_inf (hC : CentHyp (puAmalgam h.le))
    (hb6 : 6 < critDist (puAmalgam h.le))
    (hV : ∀ δ δ' : Vtx (puAmalgam h.le), IsCritical (puAmalgam h.le) δ δ' →
      ¬ Vv (puAmalgam h.le) δ ≤ Qv _ (geo _ δ' δ 2))
    (h441 : ∀ δ δ' : Vtx (puAmalgam h.le), IsCritical (puAmalgam h.le) δ δ' →
      Concl441 h.le L δ (geo (puAmalgam h.le) δ δ' 2))
    {p : ℕ → Vtx (puAmalgam h.le)} (hp : IsGoodPathB _ p (critDist (puAmalgam h.le) + 8))
    (hgt : Fintype.card F < (Qv (puAmalgam h.le) (p (critDist (puAmalgam h.le) + 4))).relIndex
      (Vv (puAmalgam h.le) (p 6))) :
    ⁅Uloc h.le L (p (critDist (puAmalgam h.le) + 4)), ZM (puAmalgam h.le) (p 4)⁆ =
      Uloc h.le L (p (critDist (puAmalgam h.le) + 4)) ⊓
        Subgroup.centralizer (Vv (puAmalgam h.le) (p 6) : Set (puAmalgam h.le).Universal) ∧
    Nat.card ↥(Uloc h.le L (p (critDist (puAmalgam h.le) + 4)) ⊓
        Subgroup.centralizer (Vv (puAmalgam h.le) (p 6) : Set (puAmalgam h.le).Universal)) ≤
      Fintype.card F := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  have hb : 4 < critDist (puAmalgam h.le) := by omega
  have hb0 := h.critDist_pos
  have hnb := hp.toIsNBPath
  obtain ⟨k, hk⟩ := ms21_v _ h.hyp20
  have hM : ∀ i, Even i → i ≤ critDist (puAmalgam h.le) + 8 → IsMVtx (puAmalgam h.le) (p i) :=
    fun i hi hiN => (hnb.isMVtx_iff hiN).mpr ⟨fun _ => hi, fun _ => hp.mvtx⟩
  have hd : ∀ i j, i ≤ j → j ≤ critDist (puAmalgam h.le) + 8 →
      (puAmalgam h.le).treeGraph.dist (p i) (p j) = j - i := fun i j hij hj => hnb.dist_eq' hij hj
  have hd' : ∀ i j, i ≤ j → j ≤ critDist (puAmalgam h.le) + 8 →
      (puAmalgam h.le).treeGraph.dist (p j) (p i) = j - i := fun i j hij hj => by
    rw [tdist_comm]; exact hd i j hij hj
  have hadj : ∀ i j, j = i + 1 → j ≤ critDist (puAmalgam h.le) + 8 →
      (puAmalgam h.le).treeGraph.Adj (p i) (p j) := fun i j hij hj => by
    subst hij; exact hp.adj i (by omega)
  have hα := hM (critDist (puAmalgam h.le) + 4) ⟨k + 2, by omega⟩ (by omega)
  have hα' := hM 4 ⟨2, rfl⟩ (by omega)
  have hp6 := hM 6 ⟨3, rfl⟩ (by omega)
  have hβα := hadj (critDist (puAmalgam h.le) + 3) (critDist (puAmalgam h.le) + 4) rfl (by omega)
  have hVβ : Vv (puAmalgam h.le) (p 6) ≤ Qv _ (p (critDist (puAmalgam h.le) + 3)) :=
    vv_le_qv_of_dist h hp6 (by rw [hd 6 _ (by omega) (by omega)]; omega)
  have hVs : Vv (puAmalgam h.le) (p 6) ≤ stab _ (p (critDist (puAmalgam h.le) + 4)) :=
    hVβ.trans (qv_le_stab_of_adj _ hβα)
  have hc4 : IsCritical (puAmalgam h.le) (p (critDist (puAmalgam h.le) + 4)) (p 4) := by
    have := hp.crit 4 ⟨2, rfl⟩ (by omega)
    rwa [show 4 + critDist (puAmalgam h.le) = critDist (puAmalgam h.le) + 4 by omega] at this
  have hZs : ZM (puAmalgam h.le) (p 4) ≤ stab _ (p (critDist (puAmalgam h.le) + 4)) :=
    zm_le_stab_of_isCritical _ h.hyp20 hb0 hc4
  have hZβ : ZM (puAmalgam h.le) (p 4) ≤ Qv _ (p (critDist (puAmalgam h.le) + 3)) :=
    zm_le_qv_of_dist_lt _ hα' (by rw [hd 4 _ (by omega) (by omega)]; omega)
  have hZV : ZM (puAmalgam h.le) (p 4) ≤ Vv _ (p 6) := by
    rw [← zv_of_isMVtx _ hα']
    exact zv_le_vv h (by rw [hd' 4 6 (by omega) (by omega)])
  have hRne : ⁅Uloc h.le L (p (critDist (puAmalgam h.le) + 4)), ZM (puAmalgam h.le) (p 4)⁆ ≠ ⊥ := by
    rw [← commutator_zm_eq_uloc h hfull hα hZs]
    exact ms22_ii _ h.hyp20 hb0 hC hc4
  have hRq := le_card_commutator_uloc h hφ hα hβα.symm hZβ hRne
  have hab := vv_comm_eq_bot h hb hp6
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at hab
  have hq : 1 < Fintype.card F := by
    rw [← Nat.card_eq_fintype_card]
    exact Finite.one_lt_card
  obtain ⟨-, hcard⟩ := hp.card_commutator_uloc_vv h hφ hC hb6 hV h441
  obtain ⟨ψ, -, hψ⟩ := exists_natural_Uloc h hφ hα
  obtain ⟨n, hn⟩ := hφ.1
  have hFn : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card, hn]
  have : CharP F 2 := FFC.charP_two_of_card_pow hFn
  have hE := S46.card_natImage_eq_relIndex h hφ hα hψ hVs
  have hcomm := S46.I464.card_commutator_eq_pow hψ hVs
  rw [hcard, Nat.card_eq_fintype_card] at hcomm
  have hf1 : Module.finrank F (commN (natImage ψ (Vv (puAmalgam h.le) (p 6)))) = 1 :=
    (Nat.pow_right_injective hq (by simpa using hcomm)).symm
  have hfix : Module.finrank F (fixN (natImage ψ (Vv (puAmalgam h.le) (p 6)))) ≤ 1 := by
    by_contra h2
    push Not at h2
    have := S46.I464.card_le_of_finrank (E := natImage ψ (Vv (puAmalgam h.le) (p 6))) h2
      hf1.le
    rw [hE, Nat.card_eq_fintype_card] at this
    omega
  have hCq : Nat.card ↥(Uloc h.le L (p (critDist (puAmalgam h.le) + 4)) ⊓
      Subgroup.centralizer (Vv (puAmalgam h.le) (p 6) : Set (puAmalgam h.le).Universal)) ≤
        Fintype.card F := by
    rw [S46.I464.card_inf_centralizer_eq_pow hψ hVs, Nat.card_eq_fintype_card]
    calc Fintype.card F ^ Module.finrank F (fixN (natImage ψ (Vv (puAmalgam h.le) (p 6)))) ≤
        Fintype.card F ^ 1 := Nat.pow_le_pow_right (by omega) hfix
      _ = Fintype.card F := pow_one _
  have hRU : ⁅Uloc h.le L (p (critDist (puAmalgam h.le) + 4)), ZM (puAmalgam h.le) (p 4)⁆ ≤
      Uloc h.le L (p (critDist (puAmalgam h.le) + 4)) :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp
      (hZs.trans (stab_le_normalizer_uloc h _))
  have hRZ : ⁅Uloc h.le L (p (critDist (puAmalgam h.le) + 4)), ZM (puAmalgam h.le) (p 4)⁆ ≤
      ZM (puAmalgam h.le) (p 4) := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp ((uloc_le_zm h hfull hα).trans
      ((zm_le_stab_of_isCritical _ h.hyp20 hb0 (ms22_iii _ h.hyp20 hb0 hC hc4)).trans
        (stab_le_normalizer_zm _ _)))
  have hRC : ⁅Uloc h.le L (p (critDist (puAmalgam h.le) + 4)), ZM (puAmalgam h.le) (p 4)⁆ ≤
      Uloc h.le L (p (critDist (puAmalgam h.le) + 4)) ⊓
        Subgroup.centralizer (Vv (puAmalgam h.le) (p 6) : Set (puAmalgam h.le).Universal) :=
    le_inf hRU (hRZ.trans (hZV.trans hab))
  have hfinC : Finite ↥(Uloc h.le L (p (critDist (puAmalgam h.le) + 4)) ⊓
      Subgroup.centralizer (Vv (puAmalgam h.le) (p 6) : Set (puAmalgam h.le).Universal)) :=
    Nat.finite_of_card_ne_zero (by
      rw [S46.I464.card_inf_centralizer_eq_pow hψ hVs]
      exact pow_ne_zero _ Nat.card_pos.ne')
  exact ⟨Subgroup.eq_of_le_of_card_ge hRC (hCq.trans hRq), hCq⟩

theorem IsGoodPathB.critR_four_le (hC : CentHyp (puAmalgam h.le))
    (hb6 : 6 < critDist (puAmalgam h.le))
    (hV : ∀ δ δ' : Vtx (puAmalgam h.le), IsCritical (puAmalgam h.le) δ δ' →
      ¬ Vv (puAmalgam h.le) δ ≤ Qv _ (geo _ δ' δ 2))
    (h441 : ∀ δ δ' : Vtx (puAmalgam h.le), IsCritical (puAmalgam h.le) δ δ' →
      Concl441 h.le L δ (geo (puAmalgam h.le) δ δ' 2))
    {p : ℕ → Vtx (puAmalgam h.le)} (hp : IsGoodPathB _ p (critDist (puAmalgam h.le) + 8)) :
    ⁅ZM (puAmalgam h.le) (p (critDist (puAmalgam h.le) + 8)), ZM (puAmalgam h.le) (p 8)⁆ ≤
      Usup (puAmalgam h.le) (p (critDist (puAmalgam h.le) + 4))
        (p (critDist (puAmalgam h.le) + 5)) ∧
    ⁅ZM (puAmalgam h.le) (p (critDist (puAmalgam h.le) + 8)), ZM (puAmalgam h.le) (p 8)⁆ ≤
      Subgroup.centralizer (Vv (puAmalgam h.le) (p 6) : Set (puAmalgam h.le).Universal) ∧
    Fintype.card F ≤
      Nat.card ↥⁅ZM (puAmalgam h.le) (p (critDist (puAmalgam h.le) + 8)),
        ZM (puAmalgam h.le) (p 8)⁆ := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  have hb : 4 < critDist (puAmalgam h.le) := by omega
  have hb0 := h.critDist_pos
  have hnb := hp.toIsNBPath
  obtain ⟨k, hk⟩ := ms21_v _ h.hyp20
  have hM : ∀ i, Even i → i ≤ critDist (puAmalgam h.le) + 8 → IsMVtx (puAmalgam h.le) (p i) :=
    fun i hi hiN => (hnb.isMVtx_iff hiN).mpr ⟨fun _ => hi, fun _ => hp.mvtx⟩
  have hd : ∀ i j, i ≤ j → j ≤ critDist (puAmalgam h.le) + 8 →
      (puAmalgam h.le).treeGraph.dist (p i) (p j) = j - i := fun i j hij hj => hnb.dist_eq' hij hj
  have hd' : ∀ i j, i ≤ j → j ≤ critDist (puAmalgam h.le) + 8 →
      (puAmalgam h.le).treeGraph.dist (p j) (p i) = j - i := fun i j hij hj => by
    rw [tdist_comm]; exact hd i j hij hj
  have hadj : ∀ i j, j = i + 1 → j ≤ critDist (puAmalgam h.le) + 8 →
      (puAmalgam h.le).treeGraph.Adj (p i) (p j) := fun i j hij hj => by
    subst hij; exact hp.adj i (by omega)
  have hα := hM (critDist (puAmalgam h.le) + 4) ⟨k + 2, by omega⟩ (by omega)
  have hp8 := hM 8 ⟨4, rfl⟩ (by omega)
  have hc8 : IsCritical (puAmalgam h.le) (p (critDist (puAmalgam h.le) + 8)) (p 8) := by
    have := hp.crit 8 ⟨4, rfl⟩ (by omega)
    rwa [show 8 + critDist (puAmalgam h.le) = critDist (puAmalgam h.le) + 8 by omega] at this
  have hc8' := ms22_iii _ h.hyp20 hb0 hC hc8
  have hα4 := hM (critDist (puAmalgam h.le) + 8) ⟨k + 4, by omega⟩ le_rfl
  have hZ8s : ZM (puAmalgam h.le) (p 8) ≤ stab _ (p (critDist (puAmalgam h.le) + 8)) :=
    zm_le_stab_of_isCritical _ h.hyp20 hb0 hc8
  have hZ8s' : ZM (puAmalgam h.le) (p (critDist (puAmalgam h.le) + 8)) ≤ stab _ (p 8) :=
    zm_le_stab_of_isCritical _ h.hyp20 hb0 hc8'
  have hR4D : ⁅ZM (puAmalgam h.le) (p (critDist (puAmalgam h.le) + 8)), ZM (puAmalgam h.le) (p 8)⁆ ≤
      Dloc h.le L (p (critDist (puAmalgam h.le) + 6)) := by
    rw [Subgroup.commutator_comm]
    have := critR_le_dloc h hφ hC hb hV hc8' (h441 _ _ hc8)
    have hg : geo (puAmalgam h.le) (p (critDist (puAmalgam h.le) + 8)) (p 8) 2 =
        p (critDist (puAmalgam h.le) + 6) := by
      rw [hnb.eq_geo_rev (i := 8) (j := critDist (puAmalgam h.le) + 8)
        (k := critDist (puAmalgam h.le) + 6) (by omega) (by omega) le_rfl]
      congr 1
      omega
    rwa [hg] at this
  have h87 : ZM (puAmalgam h.le) (p 8) ≤ Qv _ (p (critDist (puAmalgam h.le) + 7)) :=
    zm_le_qv_of_dist_lt _ hp8 (by rw [hd 8 _ (by omega) (by omega)]; omega)
  have hR4U : ⁅ZM (puAmalgam h.le) (p (critDist (puAmalgam h.le) + 8)), ZM (puAmalgam h.le) (p 8)⁆ ≤
      Usup (puAmalgam h.le) (p (critDist (puAmalgam h.le) + 8))
        (p (critDist (puAmalgam h.le) + 7)) := by
    rw [Usup, zv_of_isMVtx _ hα4]
    exact Subgroup.commutator_mono le_rfl h87
  obtain ⟨s, hsL, hsa, hsb⟩ := hp.exists_ltil_mirror h hfull
    (i := critDist (puAmalgam h.le) + 6) ⟨k + 3, by omega⟩ (by omega) le_rfl
  rw [show critDist (puAmalgam h.le) + 6 + 2 = critDist (puAmalgam h.le) + 8 by omega,
    show critDist (puAmalgam h.le) + 6 - 2 = critDist (puAmalgam h.le) + 4 by omega] at hsa
  rw [show critDist (puAmalgam h.le) + 6 + 1 = critDist (puAmalgam h.le) + 7 by omega,
    show critDist (puAmalgam h.le) + 6 - 1 = critDist (puAmalgam h.le) + 5 by omega] at hsb
  have hcs := dloc_le_centralizer_ltil h (hM (critDist (puAmalgam h.le) + 6) ⟨k + 3, by omega⟩
    (by omega))
  refine ⟨fun x hx => ?_, ?_, ?_⟩
  · have hxs : s * x = x * s := Subgroup.mem_centralizer_iff.mp (hcs (hR4D hx)) s hsL
    have hx' : s * x * s⁻¹ ∈ Usup (puAmalgam h.le) (s • p (critDist (puAmalgam h.le) + 8))
        (s • p (critDist (puAmalgam h.le) + 7)) := by
      rw [usup_smul]
      exact ⟨x, hR4U hx, rfl⟩
    rwa [hsa, hsb, hxs, mul_inv_cancel_right] at hx'
  · have h1 : ⁅ZM (puAmalgam h.le) (p (critDist (puAmalgam h.le) + 8)),
        ZM (puAmalgam h.le) (p 8)⁆ ≤ ZM (puAmalgam h.le) (p 8) := by
      rw [Subgroup.commutator_comm]
      exact Subgroup.le_normalizer_iff_commutator_le_left.mp
        (hZ8s'.trans (stab_le_normalizer_zm _ _))
    exact h1.trans (Subgroup.le_centralizer_iff.mp (vv_le_centralizer_zm _ h.hyp20 hp8
      (by rw [hd' 6 8 (by omega) (by omega)]; omega)))
  · have hR4ne : ⁅Uloc h.le L (p (critDist (puAmalgam h.le) + 8)),
        ZM (puAmalgam h.le) (p 8)⁆ ≠ ⊥ := by
      rw [← commutator_zm_eq_uloc h hfull hα4 hZ8s]
      exact ms22_ii _ h.hyp20 hb0 hC hc8
    have hR4q := le_card_commutator_uloc h hφ hα4
      (hadj (critDist (puAmalgam h.le) + 7) _ rfl le_rfl).symm h87 hR4ne
    rwa [← commutator_zm_eq_uloc h hfull hα4 hZ8s] at hR4q

theorem IsGoodPathB.relIndex_qv_vv_le (hC : CentHyp (puAmalgam h.le))
    (hb6 : 6 < critDist (puAmalgam h.le))
    (hV : ∀ δ δ' : Vtx (puAmalgam h.le), IsCritical (puAmalgam h.le) δ δ' →
      ¬ Vv (puAmalgam h.le) δ ≤ Qv _ (geo _ δ' δ 2))
    (h441 : ∀ δ δ' : Vtx (puAmalgam h.le), IsCritical (puAmalgam h.le) δ δ' →
      Concl441 h.le L δ (geo (puAmalgam h.le) δ δ' 2))
    {p : ℕ → Vtx (puAmalgam h.le)} (hp : IsGoodPathB _ p (critDist (puAmalgam h.le) + 8)) :
    (Qv (puAmalgam h.le) (p (critDist (puAmalgam h.le) + 4))).relIndex
      (Vv (puAmalgam h.le) (p 6)) ≤ Fintype.card F := by
  have hb0 := h.critDist_pos
  obtain ⟨k, hk⟩ := ms21_v _ h.hyp20
  have hα : IsMVtx (puAmalgam h.le) (p (critDist (puAmalgam h.le) + 4)) :=
    (hp.toIsNBPath.isMVtx_iff (by omega)).mpr ⟨fun _ => ⟨k + 2, by omega⟩, fun _ => hp.mvtx⟩
  have hαγ : (puAmalgam h.le).treeGraph.Adj (p (critDist (puAmalgam h.le) + 4))
      (p (critDist (puAmalgam h.le) + 5)) := hp.adj _ (by omega)
  have hpe4 : ¬ ZM (puAmalgam h.le) (p 4) ≤ Subgroup.normalizer
      (Usup (puAmalgam h.le) (p (critDist (puAmalgam h.le) + 4))
        (p (critDist (puAmalgam h.le) + 5)) : Set (puAmalgam h.le).Universal) := by
    have := hp.pe (critDist (puAmalgam h.le) + 4) ⟨k + 2, by omega⟩ (by omega) (by omega)
    rwa [show critDist (puAmalgam h.le) + 4 - critDist (puAmalgam h.le) = 4 by omega] at this
  by_contra hgt
  push Not at hgt
  obtain ⟨hReq, hCq⟩ := hp.commutator_uloc_zm_eq_inf h hφ hC hb6 hV h441 hgt
  obtain ⟨hR4U, hR4C, hR4q⟩ := hp.critR_four_le h hφ hC hb6 hV h441
  have hR4le : ⁅ZM (puAmalgam h.le) (p (critDist (puAmalgam h.le) + 8)),
      ZM (puAmalgam h.le) (p 8)⁆ ≤
        ⁅Uloc h.le L (p (critDist (puAmalgam h.le) + 4)), ZM (puAmalgam h.le) (p 4)⁆ := by
    rw [hReq]
    exact le_inf (hR4U.trans (usup_le_uloc h hφ hα hαγ)) hR4C
  have hRU : ⁅Uloc h.le L (p (critDist (puAmalgam h.le) + 4)), ZM (puAmalgam h.le) (p 4)⁆ ≤
      stab (puAmalgam h.le) (p (critDist (puAmalgam h.le) + 4)) :=
    (hReq.le.trans inf_le_left).trans ((uloc_le_zm h (isSL3Full_iff_exists_via.mpr
      ⟨F, _, _, φ, hφ⟩) hα).trans ((zm_le_qv_self _ hα hb0).trans (qv_le_stab _ _)))
  have := finite_stab h hα
  have hfinR : Finite ↥⁅Uloc h.le L (p (critDist (puAmalgam h.le) + 4)),
      ZM (puAmalgam h.le) (p 4)⁆ := Finite.of_injective _ (Subgroup.inclusion_injective hRU)
  have hcR : Nat.card ↥⁅Uloc h.le L (p (critDist (puAmalgam h.le) + 4)),
      ZM (puAmalgam h.le) (p 4)⁆ ≤ Fintype.card F := by
    rw [hReq]; exact hCq
  have hR4R := Subgroup.eq_of_le_of_card_ge hR4le (hcR.trans hR4q)
  have hUU := usup_le_uloc h hφ hα hαγ
  apply hpe4
  refine Subgroup.le_normalizer_iff_commutator_le_left.mpr
    ((Subgroup.commutator_mono hUU le_rfl).trans ?_)
  rw [← hR4R]
  exact hR4U

end Step1

section Step3

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
  {F : Type} [Field F] [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)} (hφ : IsSL3FullVia M T L φ)
include h hφ

theorem IsGoodPathB.commutator_zm_inf_le (hC : CentHyp (puAmalgam h.le))
    (hb6 : 6 < critDist (puAmalgam h.le))
    (hV : ∀ δ δ' : Vtx (puAmalgam h.le), IsCritical (puAmalgam h.le) δ δ' →
      ¬ Vv (puAmalgam h.le) δ ≤ Qv _ (geo _ δ' δ 2))
    (h441 : ∀ δ δ' : Vtx (puAmalgam h.le), IsCritical (puAmalgam h.le) δ δ' →
      Concl441 h.le L δ (geo (puAmalgam h.le) δ δ' 2))
    {p : ℕ → Vtx (puAmalgam h.le)} (hp : IsGoodPathB _ p (critDist (puAmalgam h.le) + 8)) :
    ⁅ZM (puAmalgam h.le) (p (critDist (puAmalgam h.le) + 6)),
        Vv (puAmalgam h.le) (p 6) ⊓ Qv (puAmalgam h.le) (p (critDist (puAmalgam h.le) + 4))⁆ ≤
      ⁅ZM (puAmalgam h.le) (p (critDist (puAmalgam h.le) + 6)), ZM (puAmalgam h.le) (p 6)⁆ := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  have hb : 4 < critDist (puAmalgam h.le) := by omega
  have hb0 := h.critDist_pos
  have hnb := hp.toIsNBPath
  obtain ⟨k, hk⟩ := ms21_v _ h.hyp20
  have hM : ∀ i, Even i → i ≤ critDist (puAmalgam h.le) + 8 → IsMVtx (puAmalgam h.le) (p i) :=
    fun i hi hiN => (hnb.isMVtx_iff hiN).mpr ⟨fun _ => hi, fun _ => hp.mvtx⟩
  have hd : ∀ i j, i ≤ j → j ≤ critDist (puAmalgam h.le) + 8 →
      (puAmalgam h.le).treeGraph.dist (p i) (p j) = j - i := fun i j hij hj => hnb.dist_eq' hij hj
  have hd' : ∀ i j, i ≤ j → j ≤ critDist (puAmalgam h.le) + 8 →
      (puAmalgam h.le).treeGraph.dist (p j) (p i) = j - i := fun i j hij hj => by
    rw [tdist_comm]; exact hd i j hij hj
  have hadj : ∀ i j, j = i + 1 → j ≤ critDist (puAmalgam h.le) + 8 →
      (puAmalgam h.le).treeGraph.Adj (p i) (p j) := fun i j hij hj => by
    subst hij; exact hp.adj i (by omega)
  have hα := hM (critDist (puAmalgam h.le) + 4) ⟨k + 2, by omega⟩ (by omega)
  have hp6 := hM 6 ⟨3, rfl⟩ (by omega)
  have hp2 := hM 2 ⟨1, rfl⟩ (by omega)
  have hαm2 := hM (critDist (puAmalgam h.le) + 6) ⟨k + 3, by omega⟩ (by omega)
  have hc6 : IsCritical (puAmalgam h.le) (p (critDist (puAmalgam h.le) + 6)) (p 6) := by
    have := hp.crit 6 ⟨3, rfl⟩ (by omega)
    rwa [show 6 + critDist (puAmalgam h.le) = critDist (puAmalgam h.le) + 6 by omega] at this
  have hc6' := ms22_iii _ h.hyp20 hb0 hC hc6
  have hpe2 : ¬ ZM (puAmalgam h.le) (p 2) ≤ Subgroup.normalizer
      (Usup (puAmalgam h.le) (p (critDist (puAmalgam h.le) + 2))
        (p (critDist (puAmalgam h.le) + 3)) : Set (puAmalgam h.le).Universal) := by
    have := hp.pe (critDist (puAmalgam h.le) + 2) ⟨k + 1, by omega⟩ (by omega) (by omega)
    rwa [show critDist (puAmalgam h.le) + 2 - critDist (puAmalgam h.le) = 2 by omega] at this
  have hgeoα : geo (puAmalgam h.le) (p (critDist (puAmalgam h.le) + 6)) (p 6) 2 =
      p (critDist (puAmalgam h.le) + 4) := by
    rw [hnb.eq_geo_rev (i := 6) (j := critDist (puAmalgam h.le) + 6)
      (k := critDist (puAmalgam h.le) + 4) (by omega) (by omega) (by omega)]
    congr 1
    omega
  have hXQ : Vv (puAmalgam h.le) (p 6) ⊓ Qv (puAmalgam h.le) (p (critDist (puAmalgam h.le) + 4)) ≤
      Qv _ (geo (puAmalgam h.le) (p (critDist (puAmalgam h.le) + 6)) (p 6) 2) := by
    rw [hgeoα]; exact inf_le_right
  have hLX := commutator_conjCl_le_dloc_of_le h hφ hC hb hV hc6' (h441 _ _ hc6) inf_le_left hXQ
  rw [hgeoα] at hLX
  have hR1D := (Subgroup.commutator_mono (le_conjCl _ _) le_rfl).trans hLX
  have hαγ := hadj (critDist (puAmalgam h.le) + 4) (critDist (puAmalgam h.le) + 5) rfl (by omega)
  have hγδ := hadj (critDist (puAmalgam h.le) + 5) (critDist (puAmalgam h.le) + 6) rfl (by omega)
  have hXγ : Vv (puAmalgam h.le) (p 6) ⊓ Qv (puAmalgam h.le) (p (critDist (puAmalgam h.le) + 4)) ≤
      Qv _ (p (critDist (puAmalgam h.le) + 5)) :=
    inf_le_right.trans (qv_le_qv _ h.hyp20 hα hαγ)
  have hXs := hXγ.trans (qv_le_stab_of_adj _ hγδ)
  have hR1U : ⁅ZM (puAmalgam h.le) (p (critDist (puAmalgam h.le) + 6)),
      Vv (puAmalgam h.le) (p 6) ⊓ Qv (puAmalgam h.le) (p (critDist (puAmalgam h.le) + 4))⁆ ≤
        Usup (puAmalgam h.le) (p (critDist (puAmalgam h.le) + 6))
          (p (critDist (puAmalgam h.le) + 5)) := by
    rw [Usup, zv_of_isMVtx _ hαm2]
    exact Subgroup.commutator_mono le_rfl hXγ
  have hZ6X : ZM (puAmalgam h.le) (p 6) ≤
      Vv (puAmalgam h.le) (p 6) ⊓ Qv (puAmalgam h.le) (p (critDist (puAmalgam h.le) + 4)) :=
    le_inf (zm_le_vv h hp6) (zm_le_qv_of_dist_lt _ hp6
      (by rw [hd 6 _ (by omega) (by omega)]; omega))
  have hR21 := Subgroup.commutator_mono
    (le_refl (ZM (puAmalgam h.le) (p (critDist (puAmalgam h.le) + 6)))) hZ6X
  by_contra hnot
  have hR1eq := commutator_zm_eq_uloc h hfull hαm2 hXs
  obtain ⟨d, hd2, hcard⟩ := S46.card_commutator_uloc_le h hφ hαm2 hγδ.symm hXγ
  have hZ6s : ZM (puAmalgam h.le) (p 6) ≤ stab _ (p (critDist (puAmalgam h.le) + 6)) :=
    zm_le_stab_of_isCritical _ h.hyp20 hb0 hc6
  have hZ6γ : ZM (puAmalgam h.le) (p 6) ≤ Qv _ (p (critDist (puAmalgam h.le) + 5)) :=
    zm_le_qv_of_dist_lt _ hp6 (by rw [hd 6 _ (by omega) (by omega)]; omega)
  have hR2ne : ⁅Uloc h.le L (p (critDist (puAmalgam h.le) + 6)),
      ZM (puAmalgam h.le) (p 6)⁆ ≠ ⊥ := by
    rw [← commutator_zm_eq_uloc h hfull hαm2 hZ6s]
    exact ms22_ii _ h.hyp20 hb0 hC hc6
  have hR2q := le_card_commutator_uloc h hφ hαm2 hγδ.symm hZ6γ hR2ne
  rw [← commutator_zm_eq_uloc h hfull hαm2 hZ6s] at hR2q
  have hfinU : Finite ↥(Usup (puAmalgam h.le) (p (critDist (puAmalgam h.le) + 6))
      (p (critDist (puAmalgam h.le) + 5))) :=
    Nat.finite_of_card_ne_zero (by
      rw [card_usup_eq_sq h hφ hC hb hαm2 hγδ.symm]
      exact pow_ne_zero _ Fintype.card_ne_zero)
  have hfin1 : Finite ↥⁅ZM (puAmalgam h.le) (p (critDist (puAmalgam h.le) + 6)),
      Vv (puAmalgam h.le) (p 6) ⊓ Qv (puAmalgam h.le) (p (critDist (puAmalgam h.le) + 4))⁆ :=
    Finite.of_injective _ (Subgroup.inclusion_injective hR1U)
  have hlt : Nat.card ↥⁅ZM (puAmalgam h.le) (p (critDist (puAmalgam h.le) + 6)),
      ZM (puAmalgam h.le) (p 6)⁆ <
        Nat.card ↥⁅ZM (puAmalgam h.le) (p (critDist (puAmalgam h.le) + 6)),
        Vv (puAmalgam h.le) (p 6) ⊓ Qv (puAmalgam h.le) (p (critDist (puAmalgam h.le) + 4))⁆ := by
    by_contra hge
    push Not at hge
    exact hnot (Subgroup.eq_of_le_of_card_ge hR21 hge).symm.le
  rw [hR1eq, hcard] at hlt
  have hq : 1 < Fintype.card F := by
    rw [← Nat.card_eq_fintype_card]
    exact Finite.one_lt_card
  have hd2' : d = 2 := by
    rcases (show d = 0 ∨ d = 1 ∨ d = 2 by omega) with h0 | h1 | h2
    · rw [h0, pow_zero] at hlt; omega
    · rw [h1, pow_one] at hlt; omega
    · exact h2
  have hR1U' := Subgroup.eq_of_le_of_card_ge hR1U
    (by rw [card_usup_eq_sq h hφ hC hb hαm2 hγδ.symm, hR1eq, hcard, hd2'])
  have hmir := hp.usup_eq_of_le_dloc h hfull (i := critDist (puAmalgam h.le) + 4)
    ⟨k + 2, by omega⟩ (by omega) (by omega) hR1D (Or.inl (by
      rw [hR1U', show critDist (puAmalgam h.le) + 4 + 2 = critDist (puAmalgam h.le) + 6 by omega,
        show critDist (puAmalgam h.le) + 4 + 1 = critDist (puAmalgam h.le) + 5 by omega]))
  rw [show critDist (puAmalgam h.le) + 4 + 2 = critDist (puAmalgam h.le) + 6 by omega,
    show critDist (puAmalgam h.le) + 4 + 1 = critDist (puAmalgam h.le) + 5 by omega,
    show critDist (puAmalgam h.le) + 4 - 2 = critDist (puAmalgam h.le) + 2 by omega,
    show critDist (puAmalgam h.le) + 4 - 1 = critDist (puAmalgam h.le) + 3 by omega] at hmir
  have hR1V : ⁅ZM (puAmalgam h.le) (p (critDist (puAmalgam h.le) + 6)),
      Vv (puAmalgam h.le) (p 6) ⊓ Qv (puAmalgam h.le) (p (critDist (puAmalgam h.le) + 4))⁆ ≤
        Vv (puAmalgam h.le) (p 6) := by
    rw [Subgroup.commutator_comm]
    refine (Subgroup.commutator_mono inf_le_left le_rfl).trans ?_
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp
      ((zm_le_stab_of_isCritical _ h.hyp20 hb0 hc6').trans (stab_le_normalizer_vv h _))
  have hcen := vv_le_centralizer_zm _ h.hyp20 hp2 (by rw [hd 2 6 (by omega) (by omega)]; omega)
  apply hpe2
  rw [← hmir, ← hR1U']
  exact le_normalizer_of_le_centralizer (Subgroup.le_centralizer_iff.mp (hR1V.trans hcen))

end Step3

section Main

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
  {F : Type} [Field F] [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)} (hφ : IsSL3FullVia M T L φ)
include h hφ

theorem IsGoodPathB.isC1 (hFFc : S4CFFc) (hH : Hyp40 h φ) (hC : CentHyp (puAmalgam h.le))
    (hb6 : 6 < critDist (puAmalgam h.le))
    (hV : ∀ δ δ' : Vtx (puAmalgam h.le), IsCritical (puAmalgam h.le) δ δ' →
      ¬ Vv (puAmalgam h.le) δ ≤ Qv _ (geo _ δ' δ 2))
    (h441 : ∀ δ δ' : Vtx (puAmalgam h.le), IsCritical (puAmalgam h.le) δ δ' →
      Concl441 h.le L δ (geo (puAmalgam h.le) δ δ' 2))
    {p : ℕ → Vtx (puAmalgam h.le)} (hp : IsGoodPathB _ p (critDist (puAmalgam h.le) + 8)) :
    IsC1 h.le L (Fintype.card F) (p 6) (Vv (puAmalgam h.le) (p 6)) (ZM (puAmalgam h.le) (p 6)) := by
  have hb : 4 < critDist (puAmalgam h.le) := by omega
  have hb0 := h.critDist_pos
  have hnb := hp.toIsNBPath
  obtain ⟨k, hk⟩ := ms21_v _ h.hyp20
  have hp6 : IsMVtx (puAmalgam h.le) (p 6) :=
    (hnb.isMVtx_iff (by omega)).mpr ⟨fun _ => ⟨3, rfl⟩, fun _ => hp.mvtx⟩
  have hα : IsMVtx (puAmalgam h.le) (p (critDist (puAmalgam h.le) + 4)) :=
    (hnb.isMVtx_iff (by omega)).mpr ⟨fun _ => ⟨k + 2, by omega⟩, fun _ => hp.mvtx⟩
  have hc6 : IsCritical (puAmalgam h.le) (p (critDist (puAmalgam h.le) + 6)) (p 6) := by
    have := hp.crit 6 ⟨3, rfl⟩ (by omega)
    rwa [show 6 + critDist (puAmalgam h.le) = critDist (puAmalgam h.le) + 6 by omega] at this
  have hc6' := ms22_iii _ h.hyp20 hb0 hC hc6
  have h1 := hp.relIndex_qv_vv_le h hφ hC hb6 hV h441
  have h3 := hp.commutator_zm_inf_le h hφ hC hb6 hV h441
  have hZ6n : ZM (puAmalgam h.le) (p (critDist (puAmalgam h.le) + 6)) ≤
      Subgroup.normalizer (ZM (puAmalgam h.le) (p 6) : Set (puAmalgam h.le).Universal) :=
    (zm_le_stab_of_isCritical _ h.hyp20 hb0 hc6').trans (stab_le_normalizer_zm _ _)
  have hR2Z : ⁅ZM (puAmalgam h.le) (p (critDist (puAmalgam h.le) + 6)), ZM (puAmalgam h.le) (p 6)⁆ ≤
      ZM (puAmalgam h.le) (p 6) := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp hZ6n
  obtain ⟨ψ, -, hψ⟩ := exists_natural_Uloc h hφ hα
  have hVs : Vv (puAmalgam h.le) (p 6) ≤ stab _ (p (critDist (puAmalgam h.le) + 4)) := by
    have hβα : (puAmalgam h.le).treeGraph.Adj (p (critDist (puAmalgam h.le) + 3))
        (p (critDist (puAmalgam h.le) + 4)) := hp.adj _ (by omega)
    refine (vv_le_qv_of_dist h hp6 ?_).trans (qv_le_stab_of_adj _ hβα)
    rw [hnb.dist_eq' (by omega) (by omega)]
    omega
  have hne : (Qv (puAmalgam h.le) (p (critDist (puAmalgam h.le) + 4))).relIndex
      (Vv (puAmalgam h.le) (p 6)) ≠ 0 := by
    rw [← S46.card_natImage_eq_relIndex h hφ hα hψ hVs]
    exact Nat.card_pos.ne'
  refine hFFc G M T L h F inferInstance inferInstance φ hH (p (critDist (puAmalgam h.le) + 6))
    (p 6) hc6 ?_ (Vv (puAmalgam h.le) (p 6) ⊓
      Qv (puAmalgam h.le) (p (critDist (puAmalgam h.le) + 4)) ⊔ ZM (puAmalgam h.le) (p 6))
      le_sup_right (sup_le inf_le_left (zm_le_vv h hp6)) ?_ ?_
  · rw [vv_comm_eq_bot h hb hp6]
    exact bot_le
  · refine S4A.commutator_sup_le_of ?_ (Subgroup.le_normalizer_iff_commutator_le_left.mp hZ6n)
      ?_ Subgroup.le_normalizer
    · rw [Subgroup.commutator_comm]
      exact h3.trans hR2Z
    · exact inf_le_left.trans ((vv_le_qv h (by omega) hp6).trans
        ((qv_le_stab _ _).trans (stab_le_normalizer_zm _ _)))
  · calc (Vv (puAmalgam h.le) (p 6) ⊓ Qv (puAmalgam h.le) (p (critDist (puAmalgam h.le) + 4)) ⊔
          ZM (puAmalgam h.le) (p 6)).relIndex (Vv (puAmalgam h.le) (p 6)) ≤
          (Vv (puAmalgam h.le) (p 6) ⊓
            Qv (puAmalgam h.le) (p (critDist (puAmalgam h.le) + 4))).relIndex
              (Vv (puAmalgam h.le) (p 6)) :=
          Subgroup.relIndex_le_of_le_left le_sup_left (by rwa [Subgroup.inf_relIndex_left _ _])
      _ = (Qv (puAmalgam h.le) (p (critDist (puAmalgam h.le) + 4))).relIndex
          (Vv (puAmalgam h.le) (p 6)) := Subgroup.inf_relIndex_left _ _
      _ ≤ Fintype.card F := h1

end Main

theorem s445_of (h32 : S32) (h43 : S43) (h441 : S441) (h442 : S442) (hFFc : S4CFFc) : S445 := by
  intro G _ _ M T L h F _ _ φ hH hb μ hμ
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hH.2.2⟩
  have hC := centHyp_of_S32 h32 h
  have hb6 := s443_of h32 h441 h442 G M T L h F inferInstance inferInstance φ hH hb
  have hV := h43 G M T L h hH.1 hH.2.1 hfull
  have h441' := h441 G M T L h F inferInstance inferInstance φ hH hb
  have h444 := s444_of h32 h43 h441 G M T L h F inferInstance inferInstance φ hH hb
  obtain ⟨α₀, α₀', hc₀, hs₀⟩ := h442 G M T L h F inferInstance inferInstance φ hH hb
  have hd₀ : (puAmalgam h.le).treeGraph.dist α₀' α₀ = critDist (puAmalgam h.le) := by
    rw [tdist_comm]; exact hc₀.2.1
  have hδ₀ : IsMVtx (puAmalgam h.le) (geo _ α₀' α₀ 6) :=
    (isMVtx_geo _ (by omega)).mpr ⟨fun _ => ⟨3, rfl⟩, fun _ => hc₀.isMVtx_right _ h.hyp20⟩
  obtain ⟨g, hg⟩ := exists_smul_eq_of_isMVtx _ hδ₀ hμ
  have hc : IsCritical (puAmalgam h.le) (g • α₀) (g • α₀') := (isCritical_smul _ g _ _).mpr hc₀
  have hs : IsStraight (puAmalgam h.le) (g • α₀) (g • α₀') := (isStraight_smul _ g _ _).mpr hs₀
  obtain ⟨p, hp, hpi⟩ := exists_isGoodPathB h hb h444
    (fun δ δ' hc => exists_adj_not_le_normalizer_usup h hH.2.2 hC hb hc) hc hs 4
  have hp6 : p 6 = μ := by rw [hpi 6 (by omega), geo_smul, hg]
  rw [← hp6]
  exact hp.isC1 h hH.2.2 hFFc hH hC hb6 hV h441'

end CFSG.Quasithin.MS93.S4A
