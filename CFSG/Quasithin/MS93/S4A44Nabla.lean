module

public import CFSG.Quasithin.MS93.S4A44End

public section

namespace CFSG.Quasithin.MS93.S4A

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

section Straighten

universe u v

variable {A B : Type u} {C : Type v} [Group A] [Group C] [Group B] (X : GoldAmalgam A C B)

@[expose] def IsStraightUpTo (α α' : Vtx X) (m : ℕ) : Prop :=
  ∀ i : ℕ, 0 < i → i ≤ m → 2 * i < X.treeGraph.dist α α' →
    ∃ g ∈ stab X (geo X α α' (2 * i)), g • geo X α α' (2 * i + 2) = geo X α α' (2 * i - 2)

theorem IsStraightUpTo.isStraight {α α' : Vtx X} {m : ℕ} (hs : IsStraightUpTo X α α' m)
    (hm : X.treeGraph.dist α α' ≤ 2 * m) : IsStraight X α α' :=
  fun i hi hib => hs i hi (by omega) hib

theorem isCritical_move (hb : 2 ≤ critDist X) {α α' ν : Vtx X} (hc : IsCritical X α α')
    (hν : IsMVtx X ν) (hdν : X.treeGraph.dist α ν = 2)
    (hνQ : ¬ ZM X ν ≤ Qv X (geo X α' α 2)) :
    IsCritical X ν (geo X α' α 2) ∧
      (∀ j, j + 2 ≤ critDist X → geo X ν (geo X α' α 2) (j + 2) = geo X α α' j) ∧
      geo X ν (geo X α' α 2) 1 = geo X ν α 1 := by
  have hd : X.treeGraph.dist α α' = critDist X := hc.2.1
  have hd' : X.treeGraph.dist α' α = critDist X := by rw [tdist_comm]; exact hd
  have hαν' : X.treeGraph.dist α (geo X α' α 2) = critDist X - 2 := by
    rw [tdist_comm, dist_geo_right X (by omega), hd']
  have hνα : X.treeGraph.dist ν α = 2 := by rw [tdist_comm]; exact hdν
  have hνν' : X.treeGraph.dist ν (geo X α' α 2) = critDist X := by
    have t := dist_triangle X ν α (geo X α' α 2)
    by_contra hne
    exact hνQ (zm_le_qv_of_dist_lt X hν (by omega))
  have hadd : X.treeGraph.dist ν (geo X α' α 2) =
      X.treeGraph.dist ν α + X.treeGraph.dist α (geo X α' α 2) := by omega
  refine ⟨⟨hν, hνν', hνQ⟩, fun j hj => ?_, geo_eq_of_dist_eq_add X hadd (by omega)⟩
  have hsym : geo X α' α 2 = geo X α α' (critDist X - 2) := by
    have := geo_symm X (u := α) (w := α') (i := critDist X - 2) (by omega)
    rwa [hd, show critDist X - (critDist X - 2) = 2 by omega] at this
  rw [show j + 2 = X.treeGraph.dist ν α + j by omega, geo_of_dist_eq_add X hadd (k := j) (by omega),
    hsym, geo_geo X (i := j) (j := critDist X - 2) (by omega) (by omega)]

theorem isStraightUpTo_move (h : Hyp20 X) (hb : 2 ≤ critDist X) {α α' : Vtx X}
    (hc : IsCritical X α α') {m : ℕ} (hs : IsStraightUpTo X α α' m) {g : X.Universal}
    (hg : g ∈ stab X α) (hνQ : ¬ ZM X (g • geo X α α' 2) ≤ Qv X (geo X α' α 2)) :
    IsStraightUpTo X (g • geo X α α' 2) (geo X α' α 2) (m + 1) := by
  have hd : X.treeGraph.dist α α' = critDist X := hc.2.1
  have hν : IsMVtx X (g • geo X α α' 2) :=
    (isMVtx_smul X g _).mpr (isMVtx_geo_two X h (by omega) hc)
  have hdν : X.treeGraph.dist α (g • geo X α α' 2) = 2 := by
    have := dist_smul X g α (geo X α α' 2)
    rwa [(mem_stab X).mp hg, dist_geo X (by omega)] at this
  obtain ⟨hc', hgeo, -⟩ := isCritical_move X hb hc hν hdν hνQ
  obtain ⟨k, hk⟩ := ms21_v X h
  intro i hi0 him hib
  rw [hc'.2.1] at hib
  rcases Nat.lt_or_ge 1 i with hi1 | hi1
  · obtain ⟨g', hg', hge⟩ := hs (i - 1) (by omega) (by omega) (by rw [hd]; omega)
    refine ⟨g', ?_, ?_⟩
    · rw [show 2 * i = 2 * (i - 1) + 2 by omega, hgeo (2 * (i - 1)) (by omega)]
      exact hg'
    · rw [show 2 * i + 2 = 2 * (i - 1) + 2 + 2 by omega, hgeo (2 * (i - 1) + 2) (by omega),
        show 2 * i - 2 = 2 * (i - 1) - 2 + 2 by omega, hgeo (2 * (i - 1) - 2) (by omega)]
      exact hge
  · obtain rfl : i = 1 := by omega
    refine ⟨g, ?_, ?_⟩
    · rw [show 2 * 1 = 0 + 2 from rfl, hgeo 0 (by omega), geo_zero]
      exact hg
    · rw [show 2 * 1 + 2 = 2 + 2 from rfl, hgeo 2 (by omega), show 2 * 1 - 2 = 0 from rfl,
        geo_zero]

theorem geo_smul_geo_two_one {α α' : Vtx X} (hd : 2 ≤ X.treeGraph.dist α α') {g : X.Universal}
    (hg : g ∈ stab X α) : geo X (g • geo X α α' 2) α 1 = g • geo X α α' 1 := by
  have h2 : X.treeGraph.dist α (geo X α α' 2) = 2 := dist_geo X hd
  have hs := geo_symm X (u := α) (w := geo X α α' 2) (i := 1) (by omega)
  rw [h2, show (2 : ℕ) - 1 = 1 from rfl, geo_geo X (i := 1) (by omega) hd] at hs
  have e := geo_smul X g (geo X α α' 2) α 1
  rw [(mem_stab X).mp hg] at e
  rw [e, hs]

end Straighten

section Move

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
  (hfull : IsSL3Full M T L)
include h hfull

theorem geo_two_mem_nablaSet (hC : CentHyp (puAmalgam h.le))
    (hb : 2 < critDist (puAmalgam h.le))
    (hV : ∀ δ δ' : Vtx (puAmalgam h.le), IsCritical (puAmalgam h.le) δ δ' →
      ¬ Vv (puAmalgam h.le) δ ≤ Qv _ (geo _ δ' δ 2))
    {α α' : Vtx (puAmalgam h.le)} (hc : IsCritical (puAmalgam h.le) α α') :
    geo (puAmalgam h.le) α α' 2 ∈ nablaSet h.le L α := by
  have hb0 := h.critDist_pos
  have hα := hc.1
  have hd : (puAmalgam h.le).treeGraph.dist α α' = critDist (puAmalgam h.le) := hc.2.1
  have hγ : IsMVtx (puAmalgam h.le) (geo _ α α' 2) := isMVtx_geo_two _ h.hyp20 hb0 hc
  have hβ : (puAmalgam h.le).treeGraph.Adj α (geo _ α α' 1) := adj_geo_one_of_isCritical _ hb0 hc
  have hβγ : (puAmalgam h.le).treeGraph.Adj (geo _ α α' 1) (geo _ α α' 2) :=
    adj_geo _ (i := 1) (by omega)
  refine ⟨dist_geo _ (by omega), fun hle => ?_⟩
  rw [zv_of_isMVtx _ hγ] at hle
  apply ms22_v _ h.hyp20 hb0 hC hV hc
  rw [xm_eq_zm h hfull hα, stab_eq_ltil_sup_qv_adj h hfull hα hβ]
  refine sup_le (le_normalizer_sup_of_commutator_le
    ((ltil_le_stab h α).trans (stab_le_normalizer_zm _ α))
    (((Subgroup.commutator_mono hle le_rfl).trans (commutator_bloc_le h hb hα)).trans
      le_sup_right)) ?_
  exact le_normalizer_sup ((qv_le_stab_of_adj _ hβγ).trans (stab_le_normalizer_zm _ _))
    ((qv_le_stab_of_adj _ hβ.symm).trans (stab_le_normalizer_zm _ α))

theorem not_vcirc_le_qv_of_isCritical (hb : 2 < critDist (puAmalgam h.le))
    (hV : ∀ δ δ' : Vtx (puAmalgam h.le), IsCritical (puAmalgam h.le) δ δ' →
      ¬ Vv (puAmalgam h.le) δ ≤ Qv _ (geo _ δ' δ 2))
    {α α' : Vtx (puAmalgam h.le)} (hc : IsCritical (puAmalgam h.le) α α') :
    ¬ Vcirc h.le L α ≤ Qv (puAmalgam h.le) (geo _ α' α 2) := by
  intro hle
  have hb0 := h.critDist_pos
  have hα := hc.1
  have hd : (puAmalgam h.le).treeGraph.dist α α' = critDist (puAmalgam h.le) := hc.2.1
  have hd' : (puAmalgam h.le).treeGraph.dist α' α = critDist (puAmalgam h.le) := by
    rw [tdist_comm]; exact hd
  have hβ : (puAmalgam h.le).treeGraph.Adj α (geo _ α α' 1) := adj_geo_one_of_isCritical _ hb0 hc
  obtain ⟨ρ, hρ, hρQ⟩ : ∃ ρ, (puAmalgam h.le).treeGraph.dist α ρ ≤ 2 ∧
      ¬ Zv (puAmalgam h.le) ρ ≤ Qv _ (geo _ α' α 2) := by
    by_contra hcon
    push Not at hcon
    exact hV α α' hc (iSup₂_le fun ρ hρ => hcon ρ hρ)
  obtain ⟨μ, hμ, hdμ, hρμ⟩ := exists_zv_le_zm h hα hρ
  have hμQ : ¬ ZM (puAmalgam h.le) μ ≤ Qv _ (geo _ α' α 2) := fun hle' => hρQ (hρμ.trans hle')
  have hdα2 : (puAmalgam h.le).treeGraph.dist α (geo _ α' α 2) =
      critDist (puAmalgam h.le) - 2 := by
    rw [tdist_comm, dist_geo_right _ (by omega), hd']
  have hμ2 : (puAmalgam h.le).treeGraph.dist α μ = 2 := by
    have hev := (even_dist_iff _ α μ).mpr ⟨fun _ => hμ, fun _ => hα⟩
    rcases (show (puAmalgam h.le).treeGraph.dist α μ = 0 ∨
        (puAmalgam h.le).treeGraph.dist α μ = 1 ∨
        (puAmalgam h.le).treeGraph.dist α μ = 2 by omega) with h0 | h1 | h2
    · refine absurd (zm_le_qv_of_dist_lt _ hμ ?_) hμQ
      have := dist_triangle _ μ α (geo _ α' α 2)
      rw [tdist_comm _ μ α, h0, hdα2] at this
      omega
    · exfalso; rw [h1] at hev; exact Nat.not_even_one hev
    · exact h2
  have hασ : (puAmalgam h.le).treeGraph.Adj α (geo _ α μ 1) := adj_geo_one _ (by omega)
  have hσμ : (puAmalgam h.le).treeGraph.Adj (geo _ α μ 1) μ := by
    have := adj_geo (puAmalgam h.le) (u := α) (w := μ) (i := 1) (by omega)
    rwa [show geo (puAmalgam h.le) α μ (1 + 1) = μ from geo_of_le _ (by omega)] at this
  obtain ⟨g, hg, hgσ⟩ := exists_mem_stab_smul _ hασ hβ
  obtain ⟨l, hl, hlμ⟩ := exists_ltil_smul_eq h hfull hα hασ hσμ hg
  have hlβ : (puAmalgam h.le).treeGraph.Adj (geo _ α α' 1) (l • μ) := by
    rw [hlμ, ← hgσ]
    exact (adj_smul _ g _ _).mpr hσμ
  have hdβ2 : (puAmalgam h.le).treeGraph.dist (geo _ α α' 1) (geo _ α' α 2) =
      critDist (puAmalgam h.le) - 3 := by
    have hsym : geo (puAmalgam h.le) α' α 2 = geo _ α α' (critDist (puAmalgam h.le) - 2) := by
      have := geo_symm (puAmalgam h.le) (u := α) (w := α') (i := critDist (puAmalgam h.le) - 2)
        (by omega)
      rwa [hd, show critDist (puAmalgam h.le) - (critDist (puAmalgam h.le) - 2) = 2 by omega]
        at this
    rw [hsym, dist_geo_geo _ (by omega) (by omega)]
    omega
  have hlμQ : ZM (puAmalgam h.le) (l • μ) ≤ Qv _ (geo _ α' α 2) := by
    refine zm_le_qv_of_dist_lt _ ((isMVtx_smul _ _ _).mpr hμ) ?_
    have := dist_triangle _ (l • μ) (geo _ α α' 1) (geo _ α' α 2)
    have h1 := dist_eq_one_of_adj _ hlβ.symm
    omega
  have hlμV : ZM (puAmalgam h.le) (l • μ) ≤ Vv _ α := by
    rw [← zv_of_isMVtx _ ((isMVtx_smul _ _ _).mpr hμ)]
    refine zv_le_vv h ?_
    have h2 : (puAmalgam h.le).treeGraph.dist (l • α) (l • μ) = 2 := by rw [dist_smul, hμ2]
    rw [(mem_stab _).mp (ltil_le_stab h _ hl)] at h2
    exact h2.le
  apply hμQ
  intro z hz
  have hw : l * z * l⁻¹ ∈ ZM (puAmalgam h.le) (l • μ) := by
    rw [zm_smul]; exact ⟨z, hz, rfl⟩
  have hcomm : ⁅(l * z * l⁻¹)⁻¹, l⁻¹⁆ ∈ Vcirc h.le L α :=
    Subgroup.commutator_mem_commutator ((Vv _ α).inv_mem (hlμV hw)) ((Ltil h.le L α).inv_mem hl)
  have hz' : z = (l * z * l⁻¹) * ⁅(l * z * l⁻¹)⁻¹, l⁻¹⁆ := by
    rw [commutatorElement_def]; group
  rw [hz']
  exact (Qv _ _).mul_mem (hlμQ hw) (hle hcomm)

theorem exists_smul_not_le_qv (hC : CentHyp (puAmalgam h.le))
    (hb : 2 < critDist (puAmalgam h.le))
    (hV : ∀ δ δ' : Vtx (puAmalgam h.le), IsCritical (puAmalgam h.le) δ δ' →
      ¬ Vv (puAmalgam h.le) δ ≤ Qv _ (geo _ δ' δ 2))
    {α α' : Vtx (puAmalgam h.le)} (hc : IsCritical (puAmalgam h.le) α α') {q : ℕ}
    (hc1 : IsC1 h.le L q α (Vv (puAmalgam h.le) α) (ZM (puAmalgam h.le) α)) :
    ∃ g ∈ stab (puAmalgam h.le) α,
      ¬ ZM (puAmalgam h.le) (g • geo _ α α' 2) ≤ Qv (puAmalgam h.le) (geo _ α' α 2) := by
  by_contra hall
  push Not at hall
  apply not_vcirc_le_qv_of_isCritical h hfull hb hV hc
  refine (vcirc_le_conjCl h hfull hb hc.1 hc1 (geo_two_mem_nablaSet h hfull hC hb hV hc)).trans ?_
  refine iSup₂_le fun g hg => ?_
  rw [← zm_smul]
  exact hall g hg

end Move

section Iterate

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
  (hfull : IsSL3Full M T L)
include h hfull

theorem exists_isCritical_move (hC : CentHyp (puAmalgam h.le))
    (hb : 2 < critDist (puAmalgam h.le))
    (hV : ∀ δ δ' : Vtx (puAmalgam h.le), IsCritical (puAmalgam h.le) δ δ' →
      ¬ Vv (puAmalgam h.le) δ ≤ Qv _ (geo _ δ' δ 2)) {q : ℕ}
    (hc1 : ∀ μ, IsMVtx (puAmalgam h.le) μ →
      IsC1 h.le L q μ (Vv (puAmalgam h.le) μ) (ZM (puAmalgam h.le) μ))
    {x x' a b c : Vtx (puAmalgam h.le)} (hc : IsCritical (puAmalgam h.le) x x') {m : ℕ}
    (hs : IsStraightUpTo (puAmalgam h.le) x x' m) {t : (puAmalgam h.le).Universal}
    (hta : t • a = x) (htb : t • b = geo _ x x' 1) (htc : t • c = geo _ x x' 2) :
    ∃ y y' : Vtx (puAmalgam h.le), ∃ t' : (puAmalgam h.le).Universal,
      IsCritical (puAmalgam h.le) y y' ∧ IsStraightUpTo (puAmalgam h.le) y y' (m + 1) ∧
        t' • c = y ∧ t' • b = geo _ y y' 1 ∧ t' • a = geo _ y y' 2 := by
  have hd : (puAmalgam h.le).treeGraph.dist x x' = critDist (puAmalgam h.le) := hc.2.1
  obtain ⟨g, hg, hgQ⟩ := exists_smul_not_le_qv h hfull hC hb hV hc (hc1 x hc.1)
  have hν : IsMVtx (puAmalgam h.le) (g • geo _ x x' 2) :=
    (isMVtx_smul _ g _).mpr (isMVtx_geo_two _ h.hyp20 h.critDist_pos hc)
  have hdν : (puAmalgam h.le).treeGraph.dist x (g • geo _ x x' 2) = 2 := by
    have := dist_smul _ g x (geo _ x x' 2)
    rwa [(mem_stab _).mp hg, dist_geo _ (by omega)] at this
  obtain ⟨hc', hgeo, hgeo1⟩ := isCritical_move _ hb.le hc hν hdν hgQ
  refine ⟨g • geo _ x x' 2, geo _ x' x 2, g * t, hc',
    isStraightUpTo_move _ h.hyp20 hb.le hc hs hg hgQ, ?_, ?_, ?_⟩
  · rw [mul_smul, htc]
  · rw [mul_smul, htb, hgeo1, geo_smul_geo_two_one _ (by omega) hg]
  · rw [mul_smul, hta, (mem_stab _).mp hg]
    exact ((hgeo 0 (by omega)).trans (geo_zero _ x x')).symm

theorem exists_isStraightUpTo (hC : CentHyp (puAmalgam h.le))
    (hb : 2 < critDist (puAmalgam h.le))
    (hV : ∀ δ δ' : Vtx (puAmalgam h.le), IsCritical (puAmalgam h.le) δ δ' →
      ¬ Vv (puAmalgam h.le) δ ≤ Qv _ (geo _ δ' δ 2)) {q : ℕ}
    (hc1 : ∀ μ, IsMVtx (puAmalgam h.le) μ →
      IsC1 h.le L q μ (Vv (puAmalgam h.le) μ) (ZM (puAmalgam h.le) μ))
    {x x' a b c : Vtx (puAmalgam h.le)} (hc : IsCritical (puAmalgam h.le) x x')
    {t : (puAmalgam h.le).Universal} (hta : t • a = x) (htb : t • b = geo _ x x' 1)
    (htc : t • c = geo _ x x' 2) (n : ℕ) :
    ∃ y y' : Vtx (puAmalgam h.le), ∃ t' : (puAmalgam h.le).Universal,
      IsCritical (puAmalgam h.le) y y' ∧ IsStraightUpTo (puAmalgam h.le) y y' (2 * n) ∧
        t' • a = y ∧ t' • b = geo _ y y' 1 ∧ t' • c = geo _ y y' 2 := by
  induction n with
  | zero => exact ⟨x, x', t, hc, fun i hi him _ => by omega, hta, htb, htc⟩
  | succ n ih =>
    obtain ⟨y, y', t', hcy, hsy, hya, hyb, hyc⟩ := ih
    obtain ⟨z, z', s, hcz, hsz, hzc, hzb, hza⟩ :=
      exists_isCritical_move h hfull hC hb hV hc1 hcy hsy hya hyb hyc
    obtain ⟨w, w', r, hcw, hsw, hwa, hwb, hwc⟩ :=
      exists_isCritical_move h hfull hC hb hV hc1 hcz hsz hzc hzb hza
    refine ⟨w, w', r, hcw, ?_, hwa, hwb, hwc⟩
    rwa [show 2 * (n + 1) = 2 * n + 1 + 1 by omega]

end Iterate

theorem endNabla_of (h32 : S32) (h43 : S43) (h441 : S441) (h442 : S442) (hFFc : S4CFFc) :
    EndNabla := by
  intro G _ _ M T L h F _ _ φ hH hb α β δ hα hαβ hβδ hδ
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hH.2.2⟩
  have hC := centHyp_of_S32 h32 h
  have hb6 := s443_of h32 h441 h442 G M T L h F inferInstance inferInstance φ hH hb
  have hV := h43 G M T L h hH.1 hH.2.1 hfull
  have h441' := h441 G M T L h F inferInstance inferInstance φ hH hb
  have h444 := s444_of h32 h43 h441 G M T L h F inferInstance inferInstance φ hH hb
  have hc1 := s445_of h32 h43 h441 h442 hFFc G M T L h F inferInstance inferInstance φ hH hb
  have hb2 : 2 < critDist (puAmalgam h.le) := by omega
  have hδ2 : (puAmalgam h.le).treeGraph.dist α δ = 2 := hδ.1
  have hδM : IsMVtx (puAmalgam h.le) δ :=
    ((even_dist_iff _ α δ).mp (by rw [hδ2]; exact even_two)).mp hα
  have hβδα : geo (puAmalgam h.le) δ α 1 = β := by
    refine (eq_geo_one _ hβδ.symm ?_).symm
    have h1 := dist_eq_one_of_adj _ hαβ.symm
    have h2 := tdist_comm (puAmalgam h.le) δ α
    omega
  obtain ⟨α', hc⟩ := exists_isCritical_of_isMVtx _ h.hyp20 hα
  obtain ⟨g, hg, hgQ⟩ : ∃ g ∈ stab (puAmalgam h.le) α,
      ¬ ZM (puAmalgam h.le) (g • δ) ≤ Qv (puAmalgam h.le) (geo _ α' α 2) := by
    by_contra hall
    push Not at hall
    apply not_vcirc_le_qv_of_isCritical h hfull hb2 hV hc
    refine (vcirc_le_conjCl h hfull hb2 hα (hc1 α hα) hδ).trans (iSup₂_le fun g hg => ?_)
    rw [← zm_smul]
    exact hall g hg
  have hgδ : (puAmalgam h.le).treeGraph.dist α (g • δ) = 2 := by
    have := dist_smul _ g α δ
    rwa [(mem_stab _).mp hg, hδ2] at this
  obtain ⟨hc₀, hgeo, hgeo1⟩ :=
    isCritical_move _ hb2.le hc ((isMVtx_smul _ g δ).mpr hδM) hgδ hgQ
  have htb : g • β = geo _ (g • δ) (geo _ α' α 2) 1 := by
    rw [hgeo1, ← hβδα, ← geo_smul, (mem_stab _).mp hg]
  have htc : g • α = geo _ (g • δ) (geo _ α' α 2) 2 := by
    rw [(mem_stab _).mp hg]
    exact ((hgeo 0 (by omega)).trans (geo_zero _ α α')).symm
  obtain ⟨y, y', t, hcy, hsy, hta, htb', htc'⟩ := exists_isStraightUpTo h hfull hC hb2 hV hc1
    hc₀ (a := δ) (t := g) rfl htb htc (critDist (puAmalgam h.le))
  have hs : IsStraight (puAmalgam h.le) y y' := hsy.isStraight _ (by rw [hcy.2.1]; omega)
  have key := usup_le_dloc_of_straight h hH.2.2 hC hb6 hV h441' h444
    (ms22_iii _ h.hyp20 h.critDist_pos hC hcy) (isStraight_symm _ h.hyp20 hcy hs)
  rw [← htb', ← htc', ← hta, usup_smul, dloc_smul h] at key
  exact (Subgroup.map_le_map_iff_of_injective (MulAut.conj t).injective).mp key

end CFSG.Quasithin.MS93.S4A
