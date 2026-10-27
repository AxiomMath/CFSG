module

public import CFSG.Quasithin.MS93.S46I465

public section

namespace CFSG.Quasithin.MS93.S46

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S4A
open scoped commutatorElement

section TypeIII

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
  {F : Type} [Field F] [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)} (hφ : IsSL3FullVia M T L φ)
  (hC : CentHyp (puAmalgam h.le))

omit hφ in
include h hC in
theorem zc23_of_critR_eq {α α' : Vtx (puAmalgam h.le)} (hc : IsCritical (puAmalgam h.le) α α')
    (hR : critR (puAmalgam h.le) α' α = Usup _ α' (geo _ α' α 1)) :
    ∃ Z : Subgroup (puAmalgam h.le).Universal, Z ≤ XM _ α' ∧ ¬ Z ≤ Qv _ α ∧
      ∀ Y : Subgroup (puAmalgam h.le).Universal, Y ≤ Qv _ (geo _ α' α 1) →
        CFSG.Open.IsElemAbelian 2 (Y ⊔ XM _ α) →
          ⁅Y, Z⁆ ≤ ⁅XM _ α, XM _ α'⁆ ⊔ ⁅Y, XM _ α' ⊓ Qv _ α⁆ := by
  have hb0 := h.critDist_pos
  have h20 := h.hyp20
  have hc' := ms22_iii _ h20 hb0 hC hc
  refine ⟨ZM _ α', zm_le_xm _ h20 hb0 hc'.1, hc'.2.2, fun Y hY _ => le_sup_of_le_left ?_⟩
  calc ⁅Y, ZM (puAmalgam h.le) α'⁆ ≤ ⁅Qv _ (geo _ α' α 1), ZM _ α'⁆ :=
        Subgroup.commutator_mono hY le_rfl
    _ = Usup _ α' (geo _ α' α 1) := by
        rw [Usup, zv_of_isMVtx _ hc'.1, Subgroup.commutator_comm]
    _ = critR _ α' α := hR.symm
    _ = ⁅ZM (puAmalgam h.le) α, ZM _ α'⁆ := by rw [critR, Subgroup.commutator_comm]
    _ ≤ ⁅XM (puAmalgam h.le) α, XM _ α'⁆ :=
        Subgroup.commutator_mono (zm_le_xm _ h20 hb0 hc.1) (zm_le_xm _ h20 hb0 hc'.1)

include h hφ in
theorem not_normal_of_le_uloc {α : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α)
    {A : Subgroup (puAmalgam h.le).Universal} (hAU : A ≤ Uloc h.le L α)
    (hcard : Nat.card A = Fintype.card F ∨ Nat.card A = Fintype.card F ^ 2) :
    ¬ stab _ α ≤ Subgroup.normalizer (A : Set (puAmalgam h.le).Universal) := by
  intro hn
  have hq2 := two_le_card_field (F := F)
  obtain ⟨ψ, hψs, hψ⟩ := exists_natural_Uloc h hφ hα
  have h3 := card_field_lt_pow_three (F := F)
  have h2 : Fintype.card F ^ 2 < Fintype.card F ^ 3 :=
    Nat.pow_lt_pow_right (by omega) (by norm_num)
  rcases eq_or_eq_of_natural hψs statedSL3_transitive hψ bot_le hAU hn with he | he
  · rw [he, Subgroup.card_bot] at hcard
    have : 1 < Fintype.card F ^ 2 := Nat.one_lt_pow (by norm_num) (by omega)
    omega
  · rw [he, card_eq_of_natural hψ, Nat.card_eq_fintype_card] at hcard
    omega

theorem critR_le_usup_one {α α' : Vtx (puAmalgam h.le)} (hc : IsCritical (puAmalgam h.le) α α') :
    critR (puAmalgam h.le) α α' ≤ Usup _ α (geo _ α α' 1) := by
  rw [critR, Usup, zv_of_isMVtx _ hc.1]
  exact Subgroup.commutator_mono le_rfl (zm_le_qv_geo_one _ h.hyp20 h.critDist_pos hc)

omit [Field F] in
theorem critR_eq_usup_of_card_sq {α α' : Vtx (puAmalgam h.le)}
    (hc : IsCritical (puAmalgam h.le) α α')
    (hsq : Nat.card ↥(Usup (puAmalgam h.le) α (geo _ α α' 1)) = Fintype.card F ^ 2)
    (hR : Nat.card ↥(critR (puAmalgam h.le) α α') = Fintype.card F ^ 2) :
    critR (puAmalgam h.le) α α' = Usup _ α (geo _ α α' 1) := by
  have := finite_usup h hc.1 (adj_geo_one_of_isCritical _ h.critDist_pos hc)
  exact Subgroup.eq_of_le_of_card_ge (critR_le_usup_one h hc) (by rw [hR, hsq])

variable (hR : ∀ α α' : Vtx (puAmalgam h.le), IsCritical (puAmalgam h.le) α α' →
    critR (puAmalgam h.le) α α' = Usup _ α (geo _ α α' 1))
  (hsq : ∀ δ ρ : Vtx (puAmalgam h.le), IsMVtx _ δ → (puAmalgam h.le).treeGraph.Adj δ ρ →
    Nat.card ↥(Usup (puAmalgam h.le) δ ρ) = Fintype.card F ^ 2)

include hφ hC hR hsq in
theorem stab_geo_two_le_normalizer_usup_of (hb4 : critDist (puAmalgam h.le) = 4)
    {α α' : Vtx (puAmalgam h.le)} (hc : IsCritical (puAmalgam h.le) α α') :
    stab _ (geo _ α α' 2) ≤
      Subgroup.normalizer (Usup (puAmalgam h.le) α (geo _ α α' 1) : Set _) := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  have hb0 := h.critDist_pos
  have hαβ := adj_geo_one_of_isCritical _ hb0 hc
  have hAT : Qv (puAmalgam h.le) (geo _ α α' 1) ≤
      Subgroup.normalizer (Usup (puAmalgam h.le) α (geo _ α α' 1) : Set _) := by
    refine le_normalizer_of_map_conj_le fun t ht => ?_
    rw [Usup, zv_of_isMVtx _ hc.1, Subgroup.map_commutator,
      map_conj_eq_of_mem_normalizer
        (stab_le_normalizer_zm _ α (qv_le_stab_of_adj _ hαβ.symm ht)),
      map_conj_eq_of_mem_normalizer (Subgroup.le_normalizer ht)]
  have hAc : ∀ δ' : Vtx (puAmalgam h.le), IsCritical (puAmalgam h.le) α δ' →
      geo _ α δ' 1 = geo _ α α' 1 →
        Usup (puAmalgam h.le) α (geo _ α α' 1) ≤ ⁅XM _ α, XM _ δ'⁆ := by
    intro δ' hcδ hgeo
    rw [← hgeo, ← hR α δ' hcδ, critR]
    exact Subgroup.commutator_mono (zm_le_xm _ h.hyp20 hb0 hc.1)
      (zm_le_xm _ h.hyp20 hb0 (hcδ.isMVtx_right _ h.hyp20))
  have hAG : ¬ stab _ α ≤ Subgroup.normalizer (Usup (puAmalgam h.le) α (geo _ α α' 1) : Set _) :=
    not_normal_of_le_uloc h hφ hc.1 (usup_le_uloc h hfull hc.1 hαβ) (Or.inr (hsq α _ hc.1 hαβ))
  obtain ⟨-, h23⟩ := ms23 _ h.hyp20 hc.1 hαβ (by omega) (gen23At_of h hfull hc.1 hαβ)
    (fun α₁ hc₁ _ => zc23_of_critR_eq h hC hc₁ (hR _ _ (ms22_iii _ h.hyp20 hb0 hC hc₁)))
    hAT hAG hAc
  exact h23 α' hc rfl

include hφ hC hR hsq in
theorem usup_le_dloc_of (hb4 : critDist (puAmalgam h.le) = 4)
    (h464 : ∀ δ ρ : Vtx (puAmalgam h.le), IsMVtx _ δ → (puAmalgam h.le).treeGraph.Adj δ ρ →
      Usup (puAmalgam h.le) δ ρ ≤ ZH _ ρ)
    {α α' : Vtx (puAmalgam h.le)} (hc : IsCritical (puAmalgam h.le) α α') :
    Usup (puAmalgam h.le) α (geo _ α α' 1) ≤ Dloc h.le L (geo _ α α' 2) := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  have hb0 := h.critDist_pos
  have hαβ := adj_geo_one_of_isCritical _ hb0 hc
  have hγ : IsMVtx _ (geo (puAmalgam h.le) α α' 2) := isMVtx_geo_two' hb4 hc
  have hβγ := adj_geo_crit hb4 hc (i := 1) (by norm_num)
  set U := Usup (puAmalgam h.le) α (geo _ α α' 1) with hUdef
  have hUZ : U ≤ ZM _ (geo (puAmalgam h.le) α α' 2) :=
    (h464 α _ hc.1 hαβ).trans (zh_le_zm _ hβγ.symm)
  have hUQ : U ≤ Qv _ (geo (puAmalgam h.le) α α' 2) := hUZ.trans (zm_le_qv_self _ hγ hb0)
  have hn := stab_geo_two_le_normalizer_usup_of h hφ hC hR hsq hb4 hc
  have hUn := stab_le_normalizer_puTrans h.le (S4A.Uq_normal h) (geo (puAmalgam h.le) α α' 2)
  have hYn : stab _ (geo (puAmalgam h.le) α α' 2) ≤
      Subgroup.normalizer ((U ⊓ Uloc h.le L (geo _ α α' 2) : Subgroup _) : Set _) :=
    (le_inf hn hUn).trans Subgroup.inf_normalizer_le_normalizer_inf
  obtain ⟨ψ, hψs, hψ⟩ := exists_natural_Uloc h hφ hγ
  have hLs := ltil_le_stab h (geo (puAmalgam h.le) α α' 2)
  have hcomm : ⁅U, Ltil h.le L (geo _ α α' 2)⁆ ≤ U ⊓ Uloc h.le L (geo _ α α' 2) := by
    refine le_inf (Subgroup.le_normalizer_iff_commutator_le_left.mp (hLs.trans hn)) ?_
    refine (Subgroup.commutator_mono hUZ le_rfl).trans ?_
    rw [commutator_zm_eq_uloc h hfull hγ hLs]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp (hLs.trans hUn)
  rcases eq_or_eq_of_natural hψs statedSL3_transitive hψ bot_le inf_le_right hYn with hY | hY
  · exact le_dloc_of_commutator_le h hγ hUQ ((hcomm.trans hY.le).trans bot_le)
  · exfalso
    have := finite_usup h hc.1 hαβ
    have h1 := Subgroup.card_le_of_le (inf_le_left : U ⊓ Uloc h.le L (geo _ α α' 2) ≤ U)
    rw [hY, card_eq_of_natural hψ, hsq α _ hc.1 hαβ, Nat.card_eq_fintype_card] at h1
    have hq2 := two_le_card_field (F := F)
    have : Fintype.card F ^ 2 < Fintype.card F ^ 3 := Nat.pow_lt_pow_right (by omega) (by norm_num)
    omega

include hφ hC hR hsq in
theorem commutator_vv_le_dloc_of (hb4 : critDist (puAmalgam h.le) = 4)
    (h464 : ∀ δ ρ : Vtx (puAmalgam h.le), IsMVtx _ δ → (puAmalgam h.le).treeGraph.Adj δ ρ →
      Usup (puAmalgam h.le) δ ρ ≤ ZH _ ρ)
    {x : Vtx (puAmalgam h.le)} (hx : IsMVtx _ x) :
    ⁅Vv (puAmalgam h.le) x, Vv _ x⁆ ≤ Dloc h.le L x := by
  have hb : 2 < critDist (puAmalgam h.le) := by omega
  refine commutator_vv_le_of_critR h.hyp20 hb4 hx (((vv_le_qv h hb hx).trans (qv_le_stab _ x)).trans
    (stab_le_normalizer_puTrans h.le (S4A.Dq_normal h) x)) fun μ ν hc hgeo => ?_
  rw [hR μ ν hc, ← hgeo]
  exact usup_le_dloc_of h hφ hC hR hsq hb4 h464 hc

omit hφ hsq in
include hC hR in
theorem commutator_vv_inf_qv_critGen_le_zm_of (hb4 : critDist (puAmalgam h.le) = 4)
    {x y : Vtx (puAmalgam h.le)} (hy : IsMVtx _ y)
    (hd : (puAmalgam h.le).treeGraph.dist x y = 2) :
    ⁅Vv (puAmalgam h.le) x ⊓ Qv _ y, critGen _ x y⁆ ≤ ZM _ x := by
  have hb : 2 < critDist (puAmalgam h.le) := by omega
  have hb0 := h.critDist_pos
  have h20 := h.hyp20
  set β := geo (puAmalgam h.le) x y 1
  have hxβ : (puAmalgam h.le).treeGraph.Adj x β := adj_geo_one _ (by omega)
  have hβy : (puAmalgam h.le).treeGraph.Adj β y := by
    have := adj_geo (puAmalgam h.le) (u := x) (w := y) (i := 1) (by omega)
    rwa [geo_of_le _ (by omega : (puAmalgam h.le).treeGraph.dist x y ≤ 1 + 1)] at this
  have hWs : critGen (puAmalgam h.le) x y ≤ stab _ x :=
    (critGen_le_vv hb4 x y).trans ((vv_le_qv h hb hy).trans
      ((qv_le_qv _ h20 hy hβy.symm).trans (qv_le_stab_of_adj _ hxβ.symm)))
  rw [Subgroup.commutator_comm, critGen, iSup_subtype']
  refine commutator_iSup_le_of (fun δ => ?_) ?_
  · obtain ⟨δ, hc, hgeo⟩ := δ
    have hc' := ms22_iii _ h20 hb0 hC hc
    have hyε : (puAmalgam h.le).treeGraph.Adj y (geo _ δ x 1) := by
      rw [geo_rev_one hb4 hc, ← hgeo]
      exact adj_geo_crit hb4 hc (i := 2) (by norm_num)
    rw [Subgroup.commutator_comm]
    calc ⁅Vv (puAmalgam h.le) x ⊓ Qv _ y, ZM _ δ⁆ ≤ ⁅Qv _ (geo (puAmalgam h.le) δ x 1), ZM _ δ⁆ :=
          Subgroup.commutator_mono (inf_le_right.trans (qv_le_qv _ h20 hy hyε)) le_rfl
      _ = Usup _ δ (geo (puAmalgam h.le) δ x 1) := by
          rw [Usup, zv_of_isMVtx _ hc'.1, Subgroup.commutator_comm]
      _ = critR _ δ x := (hR δ x hc').symm
      _ = ⁅ZM (puAmalgam h.le) x, ZM _ δ⁆ := by rw [critR, Subgroup.commutator_comm]
      _ ≤ ZM _ x := Subgroup.le_normalizer_iff_commutator_le_left.mp
          ((zm_le_stab_of_isCritical _ h20 hb0 hc).trans (stab_le_normalizer_zm _ x))
  · rw [← iSup_subtype' (f := fun δ (_ : δ ∈ {δ : Vtx (puAmalgam h.le) |
      IsCritical (puAmalgam h.le) x δ ∧ geo (puAmalgam h.le) x δ 2 = y}) =>
        ZM (puAmalgam h.le) δ), ← critGen]
    exact hWs.trans (stab_le_normalizer_zm _ x)

include hφ hR hsq in
theorem false_of_critR_eq_usup (h43 : S43) (hmin : PUMin M T L)
    (hb4 : critDist (puAmalgam h.le) = 4)
    (h462 : ∀ (x : Vtx (puAmalgam h.le)) (As : Subgroup (puAmalgam h.le).Universal),
      IsMVtx _ x → IsOffenderOn (puAmalgam h.le) x (Bloc h.le L x) As →
        ⁅Vv (puAmalgam h.le) x, Vv _ x⁆ ≤ Uloc h.le L x)
    (h463 : ∀ x : Vtx (puAmalgam h.le), IsMVtx _ x → ⁅Vv (puAmalgam h.le) x, Vv _ x⁆ ≤ ZM _ x)
    (h464 : ∀ δ ρ : Vtx (puAmalgam h.le), IsMVtx _ δ → (puAmalgam h.le).treeGraph.Adj δ ρ →
      Usup (puAmalgam h.le) δ ρ ≤ ZH _ ρ) : False := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  have hC := centHyp_of_gen23 h hfull
  have hb : 2 < critDist (puAmalgam h.le) := by omega
  obtain ⟨α, α', hc⟩ := exists_isCritical _ h.hyp20
  have hcomm : ∀ x y : Vtx (puAmalgam h.le), IsMVtx _ x → IsMVtx _ y →
      (puAmalgam h.le).treeGraph.dist x y = 2 →
        ⁅Vv (puAmalgam h.le) x ⊓ Qv _ y, critGen _ x y⁆ ≤ Bloc h.le L x :=
    fun x y hx hy hd => (commutator_vv_inf_qv_critGen_le_zm_of h hC hR hb4 hy hd).trans
      (zm_le_bloc h hb hx)
  have key : ∀ (x : Vtx (puAmalgam h.le)) (As : Subgroup (puAmalgam h.le).Universal),
      IsMVtx _ x → IsOffenderOn (puAmalgam h.le) x (Bloc h.le L x) As → False := by
    intro x As hx hA
    apply commutator_vv_ne_bot h hC h43 hmin hfull hb4 hx
    rw [eq_bot_iff, ← uloc_inf_dloc_eq_bot h hφ x]
    exact le_inf (h462 x As hx hA) (commutator_vv_le_dloc_of h hφ hC hR hsq hb4 h464 hx)
  rcases exists_offender_bloc h hC h43 hmin hfull hb4 h463 hcomm hc with ⟨As, hA⟩ | ⟨As, hA⟩
  · exact key α As hc.1 hA
  · exact key _ As (isMVtx_geo_two' hb4 hc) hA

end TypeIII

section TypeII

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
  {F : Type} [Field F] [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)} (hφ : IsSL3FullVia M T L φ)
  (hC : CentHyp (puAmalgam h.le))

include h hφ hC in
theorem relIndex_zm_lt_of_lt {α α' : Vtx (puAmalgam h.le)} (hc : IsCritical (puAmalgam h.le) α α')
    (hS : (Qv (puAmalgam h.le) α).relIndex (Qv _ (geo _ α α' 1)) < Fintype.card F ^ 2) :
    (Qv (puAmalgam h.le) α').relIndex (ZM _ α) < Fintype.card F ^ 2 := by
  have hb0 := h.critDist_pos
  have hαβ := adj_geo_one_of_isCritical _ hb0 hc
  have := finite_stab h hc.1
  have : Finite ↥(Qv (puAmalgam h.le) (geo _ α α' 1)) :=
    Finite.of_injective _ (Subgroup.inclusion_injective (qv_le_stab_of_adj _ hαβ.symm))
  rw [relIndex_zm_comm h hφ hC hc]
  refine lt_of_le_of_lt (Subgroup.relIndex_le_of_le_right
    (zm_le_qv_geo_one _ h.hyp20 hb0 hc) ?_) hS
  rw [Subgroup.relIndex]
  exact Subgroup.index_ne_zero_of_finite

end TypeII

theorem exists_typeII_pair (h43 : S43) (h462 : I462) (h463 : I463) (h464 : I464)
    (h465 : I465) {G : Type} [Group G] [Finite G] {M T L : Subgroup G} {F : Type} [Field F]
    [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)} (c : Hyp46 M T L φ)
    (hS : ∀ α β : Vtx (puAmalgam c.pu.le), IsMVtx _ α → (puAmalgam c.pu.le).treeGraph.Adj α β →
      (Qv _ α).relIndex (Qv _ β) < Fintype.card F ^ 2) :
    ∃ α α' : Vtx (puAmalgam c.pu.le), IsCritical _ α α' ∧
      Nat.card ↥(critR (puAmalgam c.pu.le) α α') = Fintype.card F := by
  obtain ⟨h, hmin, hb4, hφ⟩ := c
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  have hC := centHyp_of_gen23 h hfull
  by_contra hno
  push Not at hno
  have hsq : ∀ δ ρ : Vtx (puAmalgam h.le), IsMVtx _ δ → (puAmalgam h.le).treeGraph.Adj δ ρ →
      Nat.card ↥(Usup (puAmalgam h.le) δ ρ) = Fintype.card F ^ 2 :=
    fun δ ρ hδ hδρ => (h465 G M T L F φ ⟨h, hmin, hb4, hφ⟩ δ ρ hδ hδρ).1
  have hR : ∀ α α' : Vtx (puAmalgam h.le), IsCritical (puAmalgam h.le) α α' →
      critR (puAmalgam h.le) α α' = Usup _ α (geo _ α α' 1) := by
    intro α α' hc
    have hαβ := adj_geo_one_of_isCritical _ h.critDist_pos hc
    refine critR_eq_usup_of_card_sq h hc (hsq α _ hc.1 hαβ) ?_
    rcases crit_type h hφ hC hc with ⟨hI, -⟩ | ⟨-, hII⟩ | ⟨-, hIII, -⟩
    · have := relIndex_zm_lt_of_lt h hφ hC hc (hS α _ hc.1 hαβ)
      omega
    · exact absurd hII (hno α α' hc)
    · exact hIII
  exact false_of_critR_eq_usup h hφ hR hsq h43 hmin hb4
    (fun x As hx hA => h462 G M T L F φ ⟨h, hmin, hb4, hφ⟩ x As hx hA)
    (fun x hx => (h463 G M T L F φ ⟨h, hmin, hb4, hφ⟩ x hx).2)
    (fun δ ρ hδ hδρ => h464 G M T L F φ ⟨h, hmin, hb4, hφ⟩ δ ρ hδ hδρ)

theorem exists_typeII_pair_at_edge (h43 : S43) (h462 : I462) (h463 : I463)
    (h464 : I464) (h465 : I465) {G : Type} [Group G] [Finite G] {M T L : Subgroup G} {F : Type}
    [Field F] [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)} (c : Hyp46 M T L φ)
    (hS : ∀ α β : Vtx (puAmalgam c.pu.le), IsMVtx _ α → (puAmalgam c.pu.le).treeGraph.Adj α β →
      (Qv _ α).relIndex (Qv _ β) < Fintype.card F ^ 2)
    {α β : Vtx (puAmalgam c.pu.le)} (hα : IsMVtx _ α)
    (hαβ : (puAmalgam c.pu.le).treeGraph.Adj α β) :
    ∃ α' : Vtx (puAmalgam c.pu.le), IsCritical _ α α' ∧ geo _ α α' 1 = β ∧
      Nat.card ↥(critR (puAmalgam c.pu.le) α α') = Fintype.card F := by
  obtain ⟨α₀, α₀', hc, hcard⟩ := exists_typeII_pair h43 h462 h463 h464 h465 c hS
  obtain ⟨g, rfl, rfl⟩ := exists_smul_edge_of_isMVtx _ hc.1
    (adj_geo_one_of_isCritical _ c.pu.critDist_pos hc) hα hαβ
  refine ⟨g • α₀', (isCritical_smul _ g α₀ α₀').mpr hc, geo_smul _ g α₀ α₀' 1, ?_⟩
  rw [critR, zm_smul, zm_smul, ← Subgroup.map_commutator,
    Subgroup.card_map_of_injective (MulAut.conj g).injective]
  exact hcard

end CFSG.Quasithin.MS93.S46
