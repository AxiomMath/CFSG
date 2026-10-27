module

public import CFSG.Quasithin.MS93.S4A44Lin
public import CFSG.Quasithin.MS93.S4A44Path
public import CFSG.Quasithin.MS93.S4A44Stmt

public section

namespace CFSG.Quasithin.MS93.S4A

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

section Chain

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
  {F : Type} [Field F] [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)} (hφ : IsSL3FullVia M T L φ)
include h hφ

theorem usup_eq_of_dloc_chain (hC : CentHyp (puAmalgam h.le))
    (hb : 4 < critDist (puAmalgam h.le))
    (hV : ∀ δ δ' : Vtx (puAmalgam h.le), IsCritical (puAmalgam h.le) δ δ' →
      ¬ Vv (puAmalgam h.le) δ ≤ Qv _ (geo _ δ' δ 2))
    {α α' : Vtx (puAmalgam h.le)} (hc : IsCritical (puAmalgam h.le) α α')
    (hs : IsStraight (puAmalgam h.le) α α')
    (hle : Usup (puAmalgam h.le) (geo _ α α' (critDist (puAmalgam h.le)))
        (geo _ α α' (critDist (puAmalgam h.le) - 1)) ≤
      Dloc h.le L (geo _ α α' (critDist (puAmalgam h.le) - 2)))
    (hVa : Usup (puAmalgam h.le) (geo _ α α' (critDist (puAmalgam h.le)))
        (geo _ α α' (critDist (puAmalgam h.le) - 1)) ≤ Vv _ α) :
    Usup (puAmalgam h.le) (geo _ α α' (critDist (puAmalgam h.le)))
        (geo _ α α' (critDist (puAmalgam h.le) - 1)) =
        Usup (puAmalgam h.le) (geo _ α α' 0) (geo _ α α' 1) ∨
      Usup (puAmalgam h.le) (geo _ α α' (critDist (puAmalgam h.le)))
        (geo _ α α' (critDist (puAmalgam h.le) - 1)) =
        Usup (puAmalgam h.le) (geo _ α α' 2) (geo _ α α' 3) := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  have hb0 := h.critDist_pos
  have hd : (puAmalgam h.le).treeGraph.dist α α' = critDist (puAmalgam h.le) := hc.2.1
  obtain ⟨n, hn⟩ := ms21_v _ h.hyp20
  set R := Usup (puAmalgam h.le) (geo _ α α' (critDist (puAmalgam h.le)))
    (geo _ α α' (critDist (puAmalgam h.le) - 1)) with hRdef
  have hM : ∀ i, i ≤ critDist (puAmalgam h.le) →
      IsMVtx (puAmalgam h.le) (geo _ α α' (2 * i)) ∨ critDist (puAmalgam h.le) < 2 * i := by
    intro i _
    by_cases hi : 2 * i ≤ critDist (puAmalgam h.le)
    · exact Or.inl ((isMVtx_geo _ (by omega)).mpr ⟨fun _ => even_two_mul i, fun _ => hc.1⟩)
    · exact Or.inr (by omega)
  have key : ∀ k j, n = j + 2 * k → 2 ≤ j →
      R = Usup (puAmalgam h.le) (geo _ α α' (2 * j)) (geo _ α α' (2 * j - 1)) ∧
      Usup (puAmalgam h.le) (geo _ α α' (2 * j)) (geo _ α α' (2 * j - 1)) ≤
        Dloc h.le L (geo _ α α' (2 * j - 2)) := by
    intro k
    induction k with
    | zero =>
      intro j hj _
      have e1 : 2 * j = critDist (puAmalgam h.le) := by omega
      rw [e1]
      exact ⟨rfl, hle⟩
    | succ k ih =>
      intro j hj hj2
      obtain ⟨hR, hD⟩ := ih (j + 2) (by omega) (by omega)
      have hDj : Usup (puAmalgam h.le) (geo _ α α' (2 * j)) (geo _ α α' (2 * j - 1)) ≤
          Dloc h.le L (geo _ α α' (2 * j - 2)) := by
        have := usup_le_dloc_transport h hfull hc hs (j := j + 1) (by omega) (by omega)
          (by convert hD using 3 <;> omega)
        convert this using 3 <;> omega
      have hK3a := usup_eq_of_le_dloc h hfull hc hs (j := j + 2) (by omega) (by omega) hD
      have hK3b := usup_eq_of_le_dloc h hfull hc hs (j := j) hj2 (by omega) hDj
      obtain ⟨δ, hδc, hδα⟩ := exists_isCritical_back _ h.hyp20 hb0 hV hc (n - j) (by omega)
      have e2 : critDist (puAmalgam h.le) - 2 * (n - j) = 2 * j := by omega
      rw [e2] at hδc
      have hδ : IsMVtx (puAmalgam h.le) δ := hδc.1
      have hδd := hδc.2.1
      have hdist : ∀ i, i ≤ 2 * j → (puAmalgam h.le).treeGraph.dist δ (geo _ α α' i) =
          critDist (puAmalgam h.le) - 2 * j + i := fun i hi =>
        dist_geo_back _ (by omega) hδd (by omega) (by omega) hi
      have hμ : IsMVtx (puAmalgam h.le) (geo _ α α' (2 * j)) :=
        (isMVtx_geo _ (by omega)).mpr ⟨fun _ => even_two_mul j, fun _ => hc.1⟩
      have hadj1 : (puAmalgam h.le).treeGraph.Adj (geo _ α α' (2 * j))
          (geo _ α α' (2 * j - 1)) := by
        have := adj_geo (puAmalgam h.le) (u := α) (w := α') (i := 2 * j - 1) (by omega)
        rw [show 2 * j - 1 + 1 = 2 * j by omega] at this
        exact this.symm
      have hadj2 : (puAmalgam h.le).treeGraph.Adj (geo _ α α' (2 * j))
          (geo _ α α' (2 * j + 1)) := adj_geo _ (by omega)
      have hZs : ZM (puAmalgam h.le) δ ≤ stab _ (geo _ α α' (2 * j)) :=
        (zm_le_qv_of_dist_lt _ hδ (by rw [hdist _ (by omega)]; omega)).trans
          (qv_le_stab_of_adj _ hadj1.symm)
      have hZQ : ¬ ZM (puAmalgam h.le) δ ≤ Qv _ (geo _ α α' (2 * j)) := hδc.2.2
      have hc1 : Usup (puAmalgam h.le) (geo _ α α' (2 * j)) (geo _ α α' (2 * j - 1)) ≤
          Subgroup.centralizer (ZM (puAmalgam h.le) δ : Set (puAmalgam h.le).Universal) := by
        rw [hK3b]
        have hμ4 : IsMVtx (puAmalgam h.le) (geo _ α α' (2 * j - 4)) :=
          (isMVtx_geo _ (by omega)).mpr ⟨fun _ => ⟨j - 2, by omega⟩, fun _ => hc.1⟩
        have hadj4 : (puAmalgam h.le).treeGraph.Adj (geo _ α α' (2 * j - 4))
            (geo _ α α' (2 * j - 3)) := by
          have := adj_geo (puAmalgam h.le) (u := α) (w := α') (i := 2 * j - 4) (by omega)
          rwa [show 2 * j - 4 + 1 = 2 * j - 3 by omega] at this
        have hUZ : Usup (puAmalgam h.le) (geo _ α α' (2 * j - 4)) (geo _ α α' (2 * j - 3)) ≤
            ZM (puAmalgam h.le) (geo _ α α' (2 * j - 4)) := by
          rw [Usup, zv_of_isMVtx _ hμ4]
          exact Subgroup.le_normalizer_iff_commutator_le_left.mp
            ((qv_le_stab_of_adj _ hadj4.symm).trans (stab_le_normalizer_zm _ _))
        refine hUZ.trans ((zm_le_centralizer_qv _ h.hyp20 hμ4).trans
          (Subgroup.centralizer_le ?_))
        exact zm_le_qv_of_dist_lt _ hδ (by rw [hdist _ (by omega)]; omega)
      have hc2 : Usup (puAmalgam h.le) (geo _ α α' (2 * j)) (geo _ α α' (2 * j + 1)) ≤
          Subgroup.centralizer (ZM (puAmalgam h.le) δ : Set (puAmalgam h.le).Universal) := by
        have e3 : Usup (puAmalgam h.le) (geo _ α α' (2 * j)) (geo _ α α' (2 * j + 1)) = R := by
          rw [hR, hK3a]
          congr 2
        rw [e3]
        refine hVa.trans (vv_le_centralizer_zm _ h.hyp20 hδ ?_)
        rw [hδα]
        omega
      have hfeq := usup_eq_of_le_centralizer h hφ hC hb hμ hadj1 hadj2 hZs hZQ hc1 hc2
      refine ⟨?_, hDj⟩
      rw [hfeq, hR, hK3a]
      congr 2
  have hn3 : 3 ≤ n := by omega
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · obtain ⟨hR, hD⟩ := key (m - 1) 2 (by omega) le_rfl
    left
    rw [hR, usup_eq_of_le_dloc h hfull hc hs (j := 2) le_rfl (by omega) hD]
  · obtain ⟨hR, hD⟩ := key (m - 1) 3 (by omega) (by norm_num)
    right
    rw [hR, usup_eq_of_le_dloc h hfull hc hs (j := 3) (by norm_num) (by omega) hD]


theorem commutator_zm_vv_le_dloc (hC : CentHyp (puAmalgam h.le))
    (hb : 4 < critDist (puAmalgam h.le))
    (hV : ∀ δ δ' : Vtx (puAmalgam h.le), IsCritical (puAmalgam h.le) δ δ' →
      ¬ Vv (puAmalgam h.le) δ ≤ Qv _ (geo _ δ' δ 2))
    (h441 : ∀ δ δ' : Vtx (puAmalgam h.le), IsCritical (puAmalgam h.le) δ δ' →
      Concl441 h.le L δ (geo (puAmalgam h.le) δ δ' 2))
    {γ α' : Vtx (puAmalgam h.le)} (hγ : IsMVtx _ γ) (hα' : IsMVtx _ α')
    (hd : (puAmalgam h.le).treeGraph.dist γ α' + 2 = critDist (puAmalgam h.le)) :
    ⁅ZM (puAmalgam h.le) γ, Vv (puAmalgam h.le) α'⁆ ≤ Dloc h.le L α' := by
  have hb0 := h.critDist_pos
  have hDn := stab_le_normalizer_dloc h α'
  have hVs : Vv (puAmalgam h.le) α' ≤ stab _ α' := (vv_le_qv h (by omega) hα').trans
    (qv_le_stab _ α')
  have hVeq : Vv (puAmalgam h.le) α' = ⨆ ρ : {ρ : Vtx (puAmalgam h.le) //
      (puAmalgam h.le).treeGraph.dist α' ρ ≤ 2}, Zv (puAmalgam h.le) (ρ : Vtx (puAmalgam h.le)) :=
    iSup_subtype'
  rw [Subgroup.commutator_comm, hVeq]
  refine commutator_iSup_le_of (fun ρ => ?_) (hVeq ▸ hVs.trans hDn)
  obtain ⟨ρ, hρ⟩ := ρ
  obtain ⟨μ, hμ, hdμ, hρμ⟩ := exists_zv_le_zm h hα' hρ
  refine (Subgroup.commutator_mono hρμ le_rfl).trans ?_
  by_cases hZ : ZM (puAmalgam h.le) γ ≤ Qv _ μ
  · rw [(Subgroup.commutator_eq_bot_iff_le_centralizer).mpr
      ((zm_le_centralizer_qv _ h.hyp20 hμ).trans (Subgroup.centralizer_le hZ))]
    exact bot_le
  · have t1 := dist_triangle _ γ α' μ
    have hge : critDist (puAmalgam h.le) ≤ (puAmalgam h.le).treeGraph.dist γ μ := by
      by_contra hlt
      exact hZ (zm_le_qv_of_dist_lt _ hγ (by omega))
    have hcγμ : IsCritical (puAmalgam h.le) γ μ := ⟨hγ, by omega, hZ⟩
    have hμα' : (puAmalgam h.le).treeGraph.dist μ α' = 2 := by
      rw [tdist_comm]
      omega
    have hgeo : α' = geo (puAmalgam h.le) μ γ 2 :=
      eq_geo_of_dist _ hμα' (by rw [hμα', tdist_comm _ α' γ, tdist_comm _ μ γ]; omega)
    have h441' := h441 μ γ (ms22_iii _ h.hyp20 hb0 hC hcγμ)
    rw [Subgroup.commutator_comm, hgeo]
    exact critR_le_dloc h hφ hC hb hV hcγμ h441'

theorem not_usup_le_uloc (hC : CentHyp (puAmalgam h.le)) (hb : 4 < critDist (puAmalgam h.le))
    (hV : ∀ δ δ' : Vtx (puAmalgam h.le), IsCritical (puAmalgam h.le) δ δ' →
      ¬ Vv (puAmalgam h.le) δ ≤ Qv _ (geo _ δ' δ 2))
    (h441 : ∀ δ δ' : Vtx (puAmalgam h.le), IsCritical (puAmalgam h.le) δ δ' →
      Concl441 h.le L δ (geo (puAmalgam h.le) δ δ' 2))
    {α α' : Vtx (puAmalgam h.le)} (hc : IsCritical (puAmalgam h.le) α α') :
    ¬ Usup (puAmalgam h.le) (geo _ α α' 2) (geo _ α α' 3) ≤ Uloc h.le L α' := by
  intro hle
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  have hb0 := h.critDist_pos
  have hd : (puAmalgam h.le).treeGraph.dist α α' = critDist (puAmalgam h.le) := hc.2.1
  obtain ⟨n, hn⟩ := ms21_v _ h.hyp20
  have hα' := hc.isMVtx_right _ h.hyp20
  have hγ : IsMVtx (puAmalgam h.le) (geo _ α α' 2) := isMVtx_geo_two _ h.hyp20 hb0 hc
  have hγρ : (puAmalgam h.le).treeGraph.Adj (geo _ α α' 2) (geo _ α α' 3) := adj_geo _ (by omega)
  have hρH : ¬ IsMVtx (puAmalgam h.le) (geo _ α α' 3) := by
    rw [← isMVtx_iff_of_adj _ hγρ]
    exact hγ
  have hdα'ρ : (puAmalgam h.le).treeGraph.dist α' (geo _ α α' 3) =
      critDist (puAmalgam h.le) - 3 := by
    rw [tdist_comm, dist_geo_right _ (by omega), hd]
  have hVρ : Vv (puAmalgam h.le) α' ≤ Qv _ (geo _ α α' 3) := vv_le_qv_of_dist h hα' (by omega)
  have hVγ : Vv (puAmalgam h.le) α' ≤ stab _ (geo _ α α' 2) :=
    hVρ.trans (qv_le_stab_of_adj _ hγρ.symm)
  have hab := vv_comm_eq_bot h hb hα'
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at hab
  have hcen : Usup (puAmalgam h.le) (geo _ α α' 2) (geo _ α α' 3) ≤
      Subgroup.centralizer (Vv (puAmalgam h.le) α' : Set (puAmalgam h.le).Universal) :=
    hle.trans ((uloc_le_zm h hfull hα').trans ((zm_le_vv h hα').trans hab))
  have hV2 : IsPGroup 2 ↥(Vv (puAmalgam h.le) α') :=
    (isPGroup_qv _ h.hyp20 hρH).to_le hVρ
  have h1 := commutator_uloc_le_usup h hφ hC hb hγ hγρ hVγ hV2 hcen
  have hdγ : (puAmalgam h.le).treeGraph.dist (geo _ α α' 2) α' + 2 =
      critDist (puAmalgam h.le) := by
    rw [dist_geo_right _ (by omega), hd]
    omega
  have h2 := commutator_zm_vv_le_dloc h hφ hC hb hV h441 hγ hα' hdγ
  have h3 : ⁅Uloc h.le L (geo _ α α' 2), Vv (puAmalgam h.le) α'⁆ ≤
      Uloc h.le L α' ⊓ Dloc h.le L α' :=
    le_inf (h1.trans hle) ((Subgroup.commutator_mono (uloc_le_zm h hfull hγ) le_rfl).trans h2)
  rw [uloc_inf_dloc h hφ α', le_bot_iff, Subgroup.commutator_eq_bot_iff_le_centralizer] at h3
  apply hV α' α (ms22_iii _ h.hyp20 hb0 hC hc)
  rw [← hC _ _ hγ hγρ]
  intro x hx
  refine ⟨hVρ hx, (mem_centralizer_zm_iff h hfull hγ (hVγ hx)).mpr ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  exact (Subgroup.mem_centralizer_iff.mp (h3 hu) x hx).symm

end Chain

section Main

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
  {F : Type} [Field F] [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)} (hφ : IsSL3FullVia M T L φ)
include h hφ

theorem commutator_conjCl_normalizer_not_le_zm (hC : CentHyp (puAmalgam h.le))
    (hb : 4 < critDist (puAmalgam h.le))
    (hV : ∀ δ δ' : Vtx (puAmalgam h.le), IsCritical (puAmalgam h.le) δ δ' →
      ¬ Vv (puAmalgam h.le) δ ≤ Qv _ (geo _ δ' δ 2))
    {α α' γ₀ : Vtx (puAmalgam h.le)} (hc : IsCritical (puAmalgam h.le) α α')
    (hαγ₀ : (puAmalgam h.le).treeGraph.Adj α γ₀)
    (hγ₀N : ¬ ZM (puAmalgam h.le) α' ≤
      Subgroup.normalizer (Usup (puAmalgam h.le) α γ₀ : Set (puAmalgam h.le).Universal))
    {t₀ : (puAmalgam h.le).Universal} (ht₀s : t₀ ∈ stab (puAmalgam h.le) α) :
    ¬ ⁅conjCl (stab (puAmalgam h.le) α ⊓
        Subgroup.normalizer (Usup (puAmalgam h.le) α γ₀ : Set (puAmalgam h.le).Universal))
        (ZM (puAmalgam h.le) (t₀ • geo _ α α' 2)), ZM (puAmalgam h.le) α'⁆ ≤ ZM _ α := by
  intro hle
  have hb0 := h.critDist_pos
  have hα := hc.1
  set P' := stab (puAmalgam h.le) α ⊓
    Subgroup.normalizer (Usup (puAmalgam h.le) α γ₀ : Set (puAmalgam h.le).Universal) with hP'
  set X := conjCl P' (ZM (puAmalgam h.le) (t₀ • geo _ α α' 2)) with hX
  have hZs : ZM (puAmalgam h.le) α' ≤ stab _ α := zm_le_stab_of_isCritical _ h.hyp20 hb0 hc
  have hZn := stab_le_normalizer_zm (puAmalgam h.le) α
  have hN1 : ZM (puAmalgam h.le) α' ≤ Subgroup.normalizer ((X ⊔ ZM (puAmalgam h.le) α :
      Subgroup _) : Set (puAmalgam h.le).Universal) :=
    le_normalizer_sup_of_commutator_le (hZs.trans hZn) (hle.trans le_sup_right)
  have hN2 : P' ≤ Subgroup.normalizer ((X ⊔ ZM (puAmalgam h.le) α : Subgroup _) :
      Set (puAmalgam h.le).Universal) :=
    le_normalizer_sup (le_normalizer_conjCl _ _) (inf_le_left.trans hZn)
  have hHs : stab (puAmalgam h.le) α ⊓ Subgroup.normalizer ((X ⊔ ZM (puAmalgam h.le) α :
      Subgroup _) : Set (puAmalgam h.le).Universal) = stab _ α := by
    refine eq_stab_of_le h hφ hC hb hα hαγ₀ inf_le_left (le_inf inf_le_left hN2) fun hle' => ?_
    exact hγ₀N fun z hz => (hle' ⟨hZs hz, hN1 hz⟩)
  have hNn : stab (puAmalgam h.le) α ≤ Subgroup.normalizer ((X ⊔ ZM (puAmalgam h.le) α :
      Subgroup _) : Set (puAmalgam h.le).Universal) := by
    rw [← hHs]
    exact inf_le_right
  have hγX : ZM (puAmalgam h.le) (geo _ α α' 2) ≤ X ⊔ ZM (puAmalgam h.le) α := by
    have h1 : ZM (puAmalgam h.le) (t₀ • geo _ α α' 2) ≤ X ⊔ ZM (puAmalgam h.le) α :=
      (le_conjCl _ _).trans le_sup_left
    rw [zm_smul] at h1
    have h2 := Subgroup.map_mono (f := (MulAut.conj t₀⁻¹).toMonoidHom) h1
    rw [Subgroup.map_map, map_conj_eq_of_mem_normalizer (hNn (inv_mem ht₀s))] at h2
    have e : ((MulAut.conj t₀⁻¹).toMonoidHom.comp (MulAut.conj t₀).toMonoidHom) =
        MonoidHom.id _ := by
      ext x
      simp
    rwa [e, Subgroup.map_id] at h2
  apply not_commutator_conjCl_le_zm h hφ hC hV hc
  refine (Subgroup.commutator_mono (conjCl_le_of_le_normalizer hγX hNn) le_rfl).trans ?_
  have hγ₁ : ZM (puAmalgam h.le) (t₀ • geo _ α α' 2) ≤ stab _ α := by
    have hd2 : (puAmalgam h.le).treeGraph.dist α (t₀ • geo _ α α' 2) = 2 := by
      have h2 : (puAmalgam h.le).treeGraph.dist (t₀ • α) (t₀ • geo _ α α' 2) = 2 := by
        rw [dist_smul]
        exact dist_geo _ (by rw [hc.2.1]; have := two_le_critDist _ h.hyp20 hb0; omega)
      rwa [(mem_stab _).mp ht₀s] at h2
    exact (zm_le_qv_of_dist_lt _ ((isMVtx_smul _ _ _).mpr (isMVtx_geo_two _ h.hyp20 hb0 hc))
      (by rw [tdist_comm, hd2]; omega)).trans (qv_le_stab _ α)
  have hXs : X ≤ stab (puAmalgam h.le) α :=
    conjCl_le_of_le_normalizer hγ₁ (inf_le_left.trans Subgroup.le_normalizer)
  exact S4A.commutator_sup_le_of hle
    (Subgroup.le_normalizer_iff_commutator_le_left.mp (hZs.trans hZn)) (hXs.trans hZn)
    Subgroup.le_normalizer


omit hφ in
theorem conjCl_zm_smul_le_vv {α α' : Vtx (puAmalgam h.le)} (hc : IsCritical (puAmalgam h.le) α α')
    {t₀ : (puAmalgam h.le).Universal} (ht₀s : t₀ ∈ stab (puAmalgam h.le) α)
    {H : Subgroup (puAmalgam h.le).Universal} (hH : H ≤ stab (puAmalgam h.le) α) :
    conjCl H (ZM (puAmalgam h.le) (t₀ • geo _ α α' 2)) ≤ Vv (puAmalgam h.le) α := by
  have hb0 := h.critDist_pos
  have hγ₁ : IsMVtx (puAmalgam h.le) (t₀ • geo _ α α' 2) :=
    (isMVtx_smul _ _ _).mpr (isMVtx_geo_two _ h.hyp20 hb0 hc)
  have hd₁ : (puAmalgam h.le).treeGraph.dist α (t₀ • geo _ α α' 2) = 2 := by
    have h2 : (puAmalgam h.le).treeGraph.dist (t₀ • α) (t₀ • geo _ α α' 2) = 2 := by
      rw [dist_smul]
      exact dist_geo _ (by rw [hc.2.1]; have := two_le_critDist _ h.hyp20 hb0; omega)
    rwa [(mem_stab _).mp ht₀s] at h2
  refine conjCl_le_of_le_normalizer ?_ (hH.trans (stab_le_normalizer_vv h α))
  rw [← zv_of_isMVtx _ hγ₁]
  exact zv_le_vv h hd₁.le

theorem commutator_conjCl_normalizer_eq_usup (hC : CentHyp (puAmalgam h.le))
    (hb : 4 < critDist (puAmalgam h.le))
    (hV : ∀ δ δ' : Vtx (puAmalgam h.le), IsCritical (puAmalgam h.le) δ δ' →
      ¬ Vv (puAmalgam h.le) δ ≤ Qv _ (geo _ δ' δ 2))
    {α α' γ₀ : Vtx (puAmalgam h.le)} (hc : IsCritical (puAmalgam h.le) α α')
    (hαγ₀ : (puAmalgam h.le).treeGraph.Adj α γ₀)
    (hγ₀N : ¬ ZM (puAmalgam h.le) α' ≤
      Subgroup.normalizer (Usup (puAmalgam h.le) α γ₀ : Set (puAmalgam h.le).Universal))
    {t₀ : (puAmalgam h.le).Universal} (ht₀s : t₀ ∈ stab (puAmalgam h.le) α)
    (ht₀ : t₀ • geo (puAmalgam h.le) α α' 1 = γ₀)
    (hXQ : conjCl (stab (puAmalgam h.le) α ⊓
        Subgroup.normalizer (Usup (puAmalgam h.le) α γ₀ : Set (puAmalgam h.le).Universal))
        (ZM (puAmalgam h.le) (t₀ • geo _ α α' 2)) ≤ Qv _ (geo _ α' α 2)) :
    ⁅conjCl (stab (puAmalgam h.le) α ⊓
        Subgroup.normalizer (Usup (puAmalgam h.le) α γ₀ : Set (puAmalgam h.le).Universal))
        (ZM (puAmalgam h.le) (t₀ • geo _ α α' 2)), ZM (puAmalgam h.le) α'⁆ =
      Usup (puAmalgam h.le) α' (geo _ α' α 1) := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  have hb0 := h.critDist_pos
  have hα := hc.1
  have hα' := hc.isMVtx_right _ h.hyp20
  have hd : (puAmalgam h.le).treeGraph.dist α α' = critDist (puAmalgam h.le) := hc.2.1
  have hd' : (puAmalgam h.le).treeGraph.dist α' α = critDist (puAmalgam h.le) := by
    rw [tdist_comm]; exact hd
  obtain ⟨n, hn⟩ := ms21_v _ h.hyp20
  set P' := stab (puAmalgam h.le) α ⊓
    Subgroup.normalizer (Usup (puAmalgam h.le) α γ₀ : Set (puAmalgam h.le).Universal) with hP'
  set X := conjCl P' (ZM (puAmalgam h.le) (t₀ • geo _ α α' 2)) with hX
  have hβ : (puAmalgam h.le).treeGraph.Adj α (geo _ α α' 1) := adj_geo_one_of_isCritical _ hb0 hc
  have hγ : IsMVtx (puAmalgam h.le) (geo _ α α' 2) := isMVtx_geo_two _ h.hyp20 hb0 hc
  have hβγ : (puAmalgam h.le).treeGraph.Adj (geo _ α α' 1) (geo _ α α' 2) := by
    have := adj_geo (puAmalgam h.le) (u := α) (w := α') (i := 1) (by omega)
    exact this
  have hγ₀γ₁ : (puAmalgam h.le).treeGraph.Adj γ₀ (t₀ • geo _ α α' 2) := by
    rw [← ht₀]
    exact (adj_smul _ t₀ _ _).mpr hβγ
  have hZs : ZM (puAmalgam h.le) α' ≤ stab _ α := zm_le_stab_of_isCritical _ h.hyp20 hb0 hc
  have hZβ : ZM (puAmalgam h.le) α' ≤ Qv _ (geo _ α α' 1) := zm_le_qv_geo_one _ h.hyp20 hb0 hc
  have hXV : X ≤ Vv (puAmalgam h.le) α := conjCl_zm_smul_le_vv h hc ht₀s inf_le_left
  have hXs : X ≤ stab (puAmalgam h.le) α := hXV.trans ((vv_le_qv h (by omega) hα).trans
    (qv_le_stab _ α))
  have hUX : Usup (puAmalgam h.le) α γ₀ ≤ X := by
    have hle := usup_le_of_inf_ne_bot h hφ hC hb hα hαγ₀ (N := X ⊓ Uloc h.le L α) inf_le_right
      (le_normalizer_inf (le_normalizer_conjCl _ _)
        (inf_le_left.trans (stab_le_normalizer_uloc h α))) ?_
    · exact hle.trans inf_le_left
    · refine ne_bot_of_le_ne_bot (zh_inf_usup_ne_bot h hφ hC hα hαγ₀)
        (le_inf (le_inf ?_ ?_) inf_le_right)
      · exact inf_le_left.trans ((zh_le_zm _ hγ₀γ₁.symm).trans (le_conjCl _ _))
      · exact inf_le_right.trans (usup_le_uloc h hφ hα hαγ₀)
  have hRZ : ⁅ZM (puAmalgam h.le) α, ZM _ α'⁆ ≤ Uloc h.le L α ⊓
      Subgroup.centralizer (ZM (puAmalgam h.le) α' : Set (puAmalgam h.le).Universal) := by
    refine le_inf (critR_le_uloc h hfull hC hc) ?_
    have h1 : ⁅ZM (puAmalgam h.le) α, ZM _ α'⁆ ≤ ZM _ α' := by
      rw [Subgroup.commutator_comm]
      exact Subgroup.le_normalizer_iff_commutator_le_left.mp
        ((zm_le_stab_right _ h.hyp20 hb0 hC hc).trans (stab_le_normalizer_zm _ α'))
    exact h1.trans ((zm_le_centralizer_qv _ h.hyp20 hα').trans
      (Subgroup.centralizer_le (zm_le_qv_self _ hα' hb0)))
  have hCnot : ¬ Uloc h.le L α ⊓
      Subgroup.centralizer (ZM (puAmalgam h.le) α' : Set (puAmalgam h.le).Universal) ≤
        Usup (puAmalgam h.le) α γ₀ := by
    intro hle
    apply hγ₀N
    rw [Subgroup.le_normalizer_iff_commutator_le_left]
    calc ⁅Usup (puAmalgam h.le) α γ₀, ZM (puAmalgam h.le) α'⁆ ≤
          ⁅Uloc h.le L α, ZM (puAmalgam h.le) α'⁆ :=
          Subgroup.commutator_mono (usup_le_uloc h hφ hα hαγ₀) le_rfl
      _ = ⁅ZM (puAmalgam h.le) α, ZM _ α'⁆ := (commutator_zm_eq_uloc h hfull hα hZs).symm
      _ ≤ Usup (puAmalgam h.le) α γ₀ := hRZ.trans hle
  have hdec := uloc_le_usup_sup h hφ hC hb hα hαγ₀ hZs hCnot
  have hRR : ⁅ZM (puAmalgam h.le) α, ZM _ α'⁆ ≤ ⁅X, ZM (puAmalgam h.le) α'⁆ := by
    rw [commutator_zm_eq_uloc h hfull hα hZs, Subgroup.commutator_le]
    intro u hu z hz
    have hn : Usup (puAmalgam h.le) α γ₀ ≤ Subgroup.normalizer ((Uloc h.le L α ⊓
        Subgroup.centralizer (ZM (puAmalgam h.le) α' : Set (puAmalgam h.le).Universal) :
          Subgroup _) : Set (puAmalgam h.le).Universal) := by
      refine le_normalizer_of_le_centralizer ?_
      refine (usup_le_uloc h hφ hα hαγ₀).trans ((uloc_le_zm h hfull hα).trans ?_)
      exact (zm_le_centralizer_qv _ h.hyp20 hα).trans (Subgroup.centralizer_le
        (inf_le_left.trans ((uloc_le_zm h hfull hα).trans (zm_le_qv_self _ hα hb0))))
    have hu' : u ∈ ((Usup (puAmalgam h.le) α γ₀ ⊔ (Uloc h.le L α ⊓
        Subgroup.centralizer (ZM (puAmalgam h.le) α' : Set (puAmalgam h.le).Universal)) :
          Subgroup _) : Set (puAmalgam h.le).Universal) := hdec hu
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hn] at hu'
    obtain ⟨k, hk, c, hcC, rfl⟩ := hu'
    have hcz : c * z = z * c := (Subgroup.mem_centralizer_iff.mp hcC.2 z hz).symm
    have e : ⁅k * c, z⁆ = ⁅k, z⁆ := by
      simp only [commutatorElement_def]
      calc k * c * z * (k * c)⁻¹ * z⁻¹ = k * (c * z) * c⁻¹ * k⁻¹ * z⁻¹ := by group
        _ = k * (z * c) * c⁻¹ * k⁻¹ * z⁻¹ := by rw [hcz]
        _ = k * z * k⁻¹ * z⁻¹ := by group
    rw [e]
    exact Subgroup.commutator_mem_commutator (hUX hk) hz
  have hα'ρ : (puAmalgam h.le).treeGraph.Adj α' (geo _ α' α 1) :=
    adj_geo_one _ (by rw [hd']; omega)
  have hγ' : IsMVtx (puAmalgam h.le) (geo _ α' α 2) :=
    (isMVtx_geo _ (by omega)).mpr ⟨fun _ => even_two, fun _ => hα'⟩
  have hγ'ρ : (puAmalgam h.le).treeGraph.Adj (geo _ α' α 2) (geo _ α' α 1) := by
    have := adj_geo (puAmalgam h.le) (u := α') (w := α) (i := 1) (by omega)
    exact this.symm
  have hXρ : X ≤ Qv _ (geo _ α' α 1) := hXQ.trans (qv_le_qv _ h.hyp20 hγ' hγ'ρ)
  have hXs' : X ≤ stab (puAmalgam h.le) α' := hXρ.trans (qv_le_stab_of_adj _ hα'ρ.symm)
  have hR0le : ⁅X, ZM (puAmalgam h.le) α'⁆ ≤ Usup (puAmalgam h.le) α' (geo _ α' α 1) := by
    rw [Usup, zv_of_isMVtx _ hα', Subgroup.commutator_comm]
    exact Subgroup.commutator_mono le_rfl hXρ
  have hR0eq : ⁅X, ZM (puAmalgam h.le) α'⁆ = ⁅Uloc h.le L α', X⁆ := by
    rw [Subgroup.commutator_comm, commutator_zm_eq_uloc h hfull hα' hXs']
  obtain ⟨d, hd2, hcard⟩ := S46.card_commutator_uloc_le h hφ hα' hα'ρ hXρ
  have hne : ⁅Uloc h.le L α, ZM (puAmalgam h.le) α'⁆ ≠ ⊥ := by
    rw [← commutator_zm_eq_uloc h hfull hα hZs]
    exact ms22_ii _ h.hyp20 hb0 hC hc
  have hRq := le_card_commutator_uloc h hφ hα hβ hZβ hne
  rw [← commutator_zm_eq_uloc h hfull hα hZs] at hRq
  have hfin : Finite ↥(Usup (puAmalgam h.le) α' (geo _ α' α 1)) :=
    Nat.finite_of_card_ne_zero (by
      rw [card_usup_eq_sq h hφ hC hb hα' hα'ρ]
      exact pow_ne_zero _ Fintype.card_ne_zero)
  have hfin0 : Finite ↥⁅X, ZM (puAmalgam h.le) α'⁆ :=
    Finite.of_injective _ (Subgroup.inclusion_injective hR0le)
  have hlt : Nat.card ↥⁅ZM (puAmalgam h.le) α, ZM _ α'⁆ <
      Nat.card ↥⁅X, ZM (puAmalgam h.le) α'⁆ := by
    by_contra hge
    push Not at hge
    have heq := Subgroup.eq_of_le_of_card_ge hRR hge
    apply commutator_conjCl_normalizer_not_le_zm h hφ hC hb hV hc hαγ₀ hγ₀N ht₀s
    rw [← heq]
    exact (critR_le_uloc h hfull hC hc).trans (uloc_le_zm h hfull hα)
  rw [hR0eq, hcard] at hlt
  have hq : 1 < Fintype.card F := by
    rw [← Nat.card_eq_fintype_card]
    exact Finite.one_lt_card
  have hd2' : d = 2 := by
    rcases (show d = 0 ∨ d = 1 ∨ d = 2 by omega) with h0 | h1 | h2
    · rw [h0, pow_zero] at hlt; omega
    · rw [h1, pow_one] at hlt; omega
    · exact h2
  refine Subgroup.eq_of_le_of_card_ge hR0le ?_
  rw [hR0eq, hcard, hd2', card_usup_eq_sq h hφ hC hb hα' hα'ρ]

theorem concl444_of (hC : CentHyp (puAmalgam h.le)) (hb : 4 < critDist (puAmalgam h.le))
    (hV : ∀ δ δ' : Vtx (puAmalgam h.le), IsCritical (puAmalgam h.le) δ δ' →
      ¬ Vv (puAmalgam h.le) δ ≤ Qv _ (geo _ δ' δ 2))
    (h441 : ∀ δ δ' : Vtx (puAmalgam h.le), IsCritical (puAmalgam h.le) δ δ' →
      Concl441 h.le L δ (geo (puAmalgam h.le) δ δ' 2))
    {α α' : Vtx (puAmalgam h.le)} (hc : IsCritical (puAmalgam h.le) α α')
    (hs : IsStraight (puAmalgam h.le) α α') : Concl444 h.le α α' := by
  intro γ₀ hαγ₀ hγ₀N
  have hb0 := h.critDist_pos
  have hα := hc.1
  have hα' := hc.isMVtx_right _ h.hyp20
  have hd : (puAmalgam h.le).treeGraph.dist α α' = critDist (puAmalgam h.le) := hc.2.1
  have hd' : (puAmalgam h.le).treeGraph.dist α' α = critDist (puAmalgam h.le) := by
    rw [tdist_comm]; exact hd
  have hβ : (puAmalgam h.le).treeGraph.Adj α (geo _ α α' 1) := adj_geo_one_of_isCritical _ hb0 hc
  obtain ⟨t₀, ht₀s, ht₀⟩ := exists_mem_stab_smul _ hβ hαγ₀
  set P' := stab (puAmalgam h.le) α ⊓
    Subgroup.normalizer (Usup (puAmalgam h.le) α γ₀ : Set (puAmalgam h.le).Universal) with hP'
  have hX : ¬ conjCl P' (ZM (puAmalgam h.le) (t₀ • geo _ α α' 2)) ≤ Qv _ (geo _ α' α 2) := by
    intro hXQ
    have hR0 := commutator_conjCl_normalizer_eq_usup h hφ hC hb hV hc hαγ₀ hγ₀N ht₀s ht₀ hXQ
    have hXV := conjCl_zm_smul_le_vv h hc ht₀s (H := P') inf_le_left
    have hZs : ZM (puAmalgam h.le) α' ≤ stab _ α := zm_le_stab_of_isCritical _ h.hyp20 hb0 hc
    have hR0D : Usup (puAmalgam h.le) α' (geo _ α' α 1) ≤ Dloc h.le L (geo _ α' α 2) := by
      rw [← hR0, Subgroup.commutator_comm]
      exact (Subgroup.commutator_mono (le_conjCl _ _) le_rfl).trans
        (commutator_conjCl_le_dloc_of_le h hφ hC hb hV hc
          (h441 α' α (ms22_iii _ h.hyp20 hb0 hC hc)) hXV hXQ)
    have hR0V : Usup (puAmalgam h.le) α' (geo _ α' α 1) ≤ Vv _ α := by
      rw [← hR0]
      exact (Subgroup.commutator_mono hXV le_rfl).trans
        (Subgroup.le_normalizer_iff_commutator_le_left.mp
          (hZs.trans (stab_le_normalizer_vv h α)))
    have e0 : geo (puAmalgam h.le) α α' (critDist (puAmalgam h.le)) = α' := by
      rw [← hd, geo_dist]
    have e1 : geo (puAmalgam h.le) α' α 1 = geo _ α α' (critDist (puAmalgam h.le) - 1) := by
      have := geo_symm (puAmalgam h.le) (u := α) (w := α')
        (i := critDist (puAmalgam h.le) - 1) (by omega)
      rwa [hd, show critDist (puAmalgam h.le) - (critDist (puAmalgam h.le) - 1) = 1 by omega]
        at this
    have e2 : geo (puAmalgam h.le) α' α 2 = geo _ α α' (critDist (puAmalgam h.le) - 2) := by
      have := geo_symm (puAmalgam h.le) (u := α) (w := α')
        (i := critDist (puAmalgam h.le) - 2) (by omega)
      rwa [hd, show critDist (puAmalgam h.le) - (critDist (puAmalgam h.le) - 2) = 2 by omega]
        at this
    have hch := usup_eq_of_dloc_chain h hφ hC hb hV hc hs
      (by rw [e0, ← e1, ← e2]; exact hR0D) (by rw [e0, ← e1]; exact hR0V)
    rw [e0, ← e1, geo_zero] at hch
    rcases hch with h1 | h2
    · apply commutator_conjCl_normalizer_not_le_zm h hφ hC hb hV hc hαγ₀ hγ₀N ht₀s
      rw [hR0, h1, Usup, zv_of_isMVtx _ hα]
      exact Subgroup.le_normalizer_iff_commutator_le_left.mp
        ((qv_le_stab_of_adj _ hβ.symm).trans (stab_le_normalizer_zm _ _))
    · have hα'ρ : (puAmalgam h.le).treeGraph.Adj α' (geo _ α' α 1) :=
        adj_geo_one _ (by rw [hd']; omega)
      apply not_usup_le_uloc h hφ hC hb hV h441 hc
      rw [← h2]
      exact usup_le_uloc h hφ hα' hα'ρ
  obtain ⟨p, hpP, hp⟩ : ∃ p ∈ P', ¬ (ZM (puAmalgam h.le) (t₀ • geo _ α α' 2)).map
      (MulAut.conj p).toMonoidHom ≤ Qv _ (geo _ α' α 2) := by
    by_contra hall
    push Not at hall
    exact hX (iSup₂_le hall)
  have hconj : (MulAut.conj (p * t₀)).toMonoidHom =
      (MulAut.conj p).toMonoidHom.comp (MulAut.conj t₀).toMonoidHom := by
    ext x
    simp [mul_assoc]
  refine ⟨p * t₀, mul_mem hpP.1 ht₀s, ?_, ?_⟩
  · rw [hconj, ← Subgroup.map_map, ← usup_smul, ht₀, (mem_stab _).mp ht₀s]
    exact map_conj_eq_of_mem_normalizer hpP.2
  · rw [hconj, ← Subgroup.map_map, ← zm_smul]
    exact hp

end Main

theorem s444_of (h32 : S32) (h43 : S43) (h441 : S441) : S444 := by
  intro G _ _ M T L h F _ _ φ hH hb α α' hc hs
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hH.2.2⟩
  exact concl444_of h hH.2.2 (centHyp_of_S32 h32 h) hb
    (h43 G M T L h hH.1 hH.2.1 hfull)
    (h441 G M T L h F inferInstance inferInstance φ hH hb) hc hs

end CFSG.Quasithin.MS93.S4A
