module

public import CFSG.Quasithin.MS93.S34GB
public import CFSG.Quasithin.MS93.S34F461
public import CFSG.Quasithin.MS93.S4A431G

public section

namespace CFSG.Quasithin.MS93.S34G

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S4A CFSG.Quasithin.MS93.S46 CFSG.Quasithin.MS93.S34F
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
  (hU : IsSL3U M T L) (hC : CentHyp (puAmalgam h.le))
include h hU hC

theorem vv_le_flat_of_star (hb : 2 < critDist (puAmalgam h.le)) {α α' : Vtx (puAmalgam h.le)}
    (hs : Star (puAmalgam h.le) α α') :
    Vv (puAmalgam h.le) α ≤ Qv _ (geo (puAmalgam h.le) α' α 1) ⊓ flat h α' := by
  obtain ⟨hc, hstar⟩ := hs
  have h20 := h.hyp20
  have hb0 := h.critDist_pos
  have hc' := ms22_iii _ h20 hb0 hC hc
  have hα := hc.1
  have hβ'γ' : (puAmalgam h.le).treeGraph.Adj (geo (puAmalgam h.le) α' α 1)
      (geo (puAmalgam h.le) α' α 2) := adj_geo _ (i := 1) (by have := hc'.2.1; omega)
  have hγ' : IsMVtx (puAmalgam h.le) (geo (puAmalgam h.le) α' α 2) :=
    isMVtx_geo_two _ h20 hb0 hc'
  have hVβ' : Vv (puAmalgam h.le) α ≤ Qv _ (geo (puAmalgam h.le) α' α 1) :=
    hstar.trans (qv_le_qv _ h20 hγ' hβ'γ'.symm)
  have hZ's : ZM (puAmalgam h.le) α' ≤ stab _ α := zm_le_stab_right _ h20 hb0 hC hc'
  have hRZ : critR (puAmalgam h.le) α α' ≤ ZM (puAmalgam h.le) α :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp (hZ's.trans (stab_le_normalizer_zm _ α))
  have hVc : Vv (puAmalgam h.le) α ≤
      Subgroup.centralizer (critR (puAmalgam h.le) α α' : Set (puAmalgam h.le).Universal) := by
    rw [Subgroup.le_centralizer_iff]
    exact hRZ.trans ((zm_le_centralizer_qv _ h20 hα).trans
      (Subgroup.centralizer_le (vv_le_qv h hb hα)))
  exact le_inf hVβ' ((le_inf hVβ' hVc).trans (qv_inf_centralizer_critR_le_flat h hU hc))

variable {F : Type} [Field F] [Fintype F] {n : ℕ} (hcard : Fintype.card F = 2 ^ n)
  {φ : ↥(L ⊔ pCoreOf 2 M) →* ↥(StatedSL 3 F)} (hφs : Function.Surjective φ)
  (hφ : IsSumOfNaturalModulesVia (L ⊔ pCoreOf 2 M) (Uq M T L) ⊥ φ false 1)
include hcard hφs hφ

theorem card_critR0_flat (hb : 2 < critDist (puAmalgam h.le)) {α α' : Vtx (puAmalgam h.le)}
    (hs : Star (puAmalgam h.le) α α') :
    Nat.card ↥(critR0 (puAmalgam h.le) α α') = Nat.card F ^ 2 ∧
      Nat.card ↥(critR (puAmalgam h.le) α α') = Nat.card F := by
  have hVfl := vv_le_flat_of_star h hU hC hb hs
  obtain ⟨hc, -⟩ := hs
  have h20 := h.hyp20
  have hb0 := h.critDist_pos
  have hFn : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card, hcard]
  have : CharP F 2 := FFC.charP_two_of_card_pow hFn
  have hq : 2 ≤ Nat.card F := Finite.one_lt_card
  have hc' := ms22_iii _ h20 hb0 hC hc
  have hα := hc.1
  have hα' := hc'.1
  have hα'β' : (puAmalgam h.le).treeGraph.Adj α' (geo (puAmalgam h.le) α' α 1) :=
    adj_geo_one_of_isCritical _ hb0 hc'
  have hβ'H : ¬ IsMVtx (puAmalgam h.le) (geo (puAmalgam h.le) α' α 1) := by
    rw [← isMVtx_iff_of_adj _ hα'β']
    exact hα'
  have hVβ' : Vv (puAmalgam h.le) α ≤ Qv _ (geo (puAmalgam h.le) α' α 1) := hVfl.trans inf_le_left
  have hVs' : Vv (puAmalgam h.le) α ≤ flat h α' := hVfl.trans inf_le_right
  have hZs' : ZM (puAmalgam h.le) α ≤ flat h α' := (zm_le_vv h hα).trans hVs'
  have hT2 := isPGroup_qv _ h20 hβ'H
  obtain ⟨ψ', -, hψ'⟩ := exists_natural_flat_at h hφs hφ hα'
  obtain ⟨ψ, -, hψ⟩ := exists_natural_flat_at h hφs hφ hα
  have hR0 : critR0 (puAmalgam h.le) α α' = ⁅Uloc h.le L α', Vv (puAmalgam h.le) α⁆ := by
    rw [critR0, Subgroup.commutator_comm,
      commutator_zm_eq_commutator_uloc_of_le_qv h hα' hα'β' hVβ']
  have hR : critR (puAmalgam h.le) α α' = ⁅Uloc h.le L α', ZM (puAmalgam h.le) α⁆ := by
    rw [critR, Subgroup.commutator_comm,
      commutator_zm_eq_commutator_uloc_of_le_qv h hα' hα'β' ((zm_le_vv h hα).trans hVβ')]
  have hR0card : Nat.card ↥(critR0 (puAmalgam h.le) α α') =
      Nat.card F ^ Module.finrank F (commN (natImage ψ' (Vv (puAmalgam h.le) α))) := by
    rw [hR0, card_commutator_eq hψ' hVs']
    exact Module.natCard_eq_pow_finrank
  have hRcard : Nat.card ↥(critR (puAmalgam h.le) α α') =
      Nat.card F ^ Module.finrank F (commN (natImage ψ' (ZM (puAmalgam h.le) α))) := by
    rw [hR, card_commutator_eq hψ' hZs']
    exact Module.natCard_eq_pow_finrank
  have hEne : natImage ψ' (ZM (puAmalgam h.le) α) ≠ ⊥ :=
    (s35_core_flat h hU hC hcard hc' hψ' hψ).2.2.2.2.2
  have hc1 : 1 ≤ Module.finrank F (commN (natImage ψ' (ZM (puAmalgam h.le) α))) := by
    rw [Nat.one_le_iff_ne_zero, Ne, Submodule.finrank_eq_zero]
    exact commN_ne_bot hEne
  have hnat2 : IsPGroup 2 ↥(natImage ψ' (Vv (puAmalgam h.le) α)) := by
    have h1 : IsPGroup 2 ↥((Vv (puAmalgam h.le) α).subgroupOf (flat h α')) :=
      (hT2.to_le hVβ').of_equiv (Subgroup.subgroupOfEquivOfLe hVs').symm
    exact h1.map _
  have ha2 : Module.finrank F (commN (natImage ψ' (Vv (puAmalgam h.le) α))) ≤ 2 :=
    finrank_commN_le_two hnat2
  have hRle : critR (puAmalgam h.le) α α' ≤ critR0 _ α α' :=
    Subgroup.commutator_mono (zm_le_vv h hα) le_rfl
  have hZ's : ZM (puAmalgam h.le) α' ≤ stab _ α := zm_le_stab_right _ h20 hb0 hC hc'
  have hR0V : critR0 (puAmalgam h.le) α α' ≤ Vv _ α :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp (hZ's.trans (stab_le_normalizer_vv h α))
  have hfinR0 : Finite ↥(critR0 (puAmalgam h.le) α α') :=
    have := finite_qv _ h20 hβ'H
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
    apply not_commutator_vv_le_zm_gen h hb hα (adj_geo_one_of_isCritical _ hb0 hc)
      (zm_le_qv_geo_one _ h20 hb0 hc) hc'.2.2
    rw [← critR0, ← hRR0, critR]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp
      (hZ's.trans (stab_le_normalizer_zm _ α))
  have hc_eq : Module.finrank F (commN (natImage ψ' (ZM (puAmalgam h.le) α))) = 1 := by omega
  have ha_eq : Module.finrank F (commN (natImage ψ' (Vv (puAmalgam h.le) α))) = 2 := by omega
  exact ⟨by rw [hR0card, ha_eq], by rw [hRcard, hc_eq, pow_one]⟩

theorem relIndex_critR0_sup_zm_le_flat (hb : 2 < critDist (puAmalgam h.le))
    {α α' : Vtx (puAmalgam h.le)} (hs : Star (puAmalgam h.le) α α') :
    (ZM (puAmalgam h.le) α).relIndex
        (⁅Vv (puAmalgam h.le) α, ZM (puAmalgam h.le) α'⁆ ⊔ ZM (puAmalgam h.le) α) ≤
      Fintype.card F := by
  have h20 := h.hyp20
  have hb0 := h.critDist_pos
  have hα := hs.1.1
  have hVfl := vv_le_flat_of_star h hU hC hb hs
  obtain ⟨hR0, hR⟩ := card_critR0_flat h hU hC hcard hφs hφ hb hs
  unfold critR0 at hR0
  have hc' := ms22_iii _ h20 hb0 hC hs.1
  have hZ's : ZM (puAmalgam h.le) α' ≤ stab _ α := zm_le_stab_right _ h20 hb0 hC hc'
  have hR0V : ⁅Vv (puAmalgam h.le) α, ZM (puAmalgam h.le) α'⁆ ≤ Vv _ α :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp (hZ's.trans (stab_le_normalizer_vv h α))
  have hVs : Vv (puAmalgam h.le) α ≤ stab _ α := (vv_le_qv h hb hα).trans (qv_le_stab _ α)
  rw [relIndex_sup_of_le_normalizer ((hR0V.trans hVs).trans (stab_le_normalizer_zm _ α))]
  have hRZ : critR (puAmalgam h.le) α α' ≤ ZM _ α :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp (hZ's.trans (stab_le_normalizer_zm _ α))
  have hRR0 : critR (puAmalgam h.le) α α' ≤ ⁅Vv (puAmalgam h.le) α, ZM (puAmalgam h.le) α'⁆ :=
    Subgroup.commutator_mono (zm_le_vv h hα) le_rfl
  have hβ' := adj_geo_one_of_isCritical _ hb0 hc'
  have hfin : Finite ↥⁅Vv (puAmalgam h.le) α, ZM (puAmalgam h.le) α'⁆ := by
    have := finite_qv _ h20 (by rw [← isMVtx_iff_of_adj _ hβ']; exact hc'.1)
    exact Finite.of_injective _ (Subgroup.inclusion_injective
      (hR0V.trans (hVfl.trans inf_le_left)))
  have hne : (critR (puAmalgam h.le) α α').relIndex
      ⁅Vv (puAmalgam h.le) α, ZM (puAmalgam h.le) α'⁆ ≠ 0 :=
    Subgroup.index_ne_zero_of_finite
  refine (Subgroup.relIndex_le_of_le_left hRZ hne).trans ?_
  have hmul := relIndex_mul_card_inf (critR (puAmalgam h.le) α α')
    ⁅Vv (puAmalgam h.le) α, ZM (puAmalgam h.le) α'⁆
  rw [inf_of_le_left hRR0, hR0, hR, sq] at hmul
  have hq : 0 < Nat.card F := Nat.card_pos
  rw [← Nat.card_eq_fintype_card]
  exact (Nat.eq_of_mul_eq_mul_right hq hmul).le

theorem commutator_critR0_vv_le_flat (hb : 2 < critDist (puAmalgam h.le))
    {α α' : Vtx (puAmalgam h.le)} (hs : Star (puAmalgam h.le) α α') :
    ⁅critR0 (puAmalgam h.le) α α', Vv (puAmalgam h.le) α⁆ ≤ critR (puAmalgam h.le) α α' := by
  have hVfl := vv_le_flat_of_star h hU hC hb hs
  obtain ⟨hR0q, hRq⟩ := card_critR0_flat h hU hC hcard hφs hφ hb hs
  obtain ⟨hc, -⟩ := hs
  have h20 := h.hyp20
  have hb0 := h.critDist_pos
  have hFn : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card, hcard]
  have : CharP F 2 := FFC.charP_two_of_card_pow hFn
  have hq : 2 ≤ Nat.card F := Finite.one_lt_card
  have hc' := ms22_iii _ h20 hb0 hC hc
  have hα := hc.1
  have hα' := hc'.1
  have hα'β' : (puAmalgam h.le).treeGraph.Adj α' (geo (puAmalgam h.le) α' α 1) :=
    adj_geo_one_of_isCritical _ hb0 hc'
  have hβ'H : ¬ IsMVtx (puAmalgam h.le) (geo (puAmalgam h.le) α' α 1) := by
    rw [← isMVtx_iff_of_adj _ hα'β']
    exact hα'
  have hVβ' : Vv (puAmalgam h.le) α ≤ Qv _ (geo (puAmalgam h.le) α' α 1) := hVfl.trans inf_le_left
  have hVs' : Vv (puAmalgam h.le) α ≤ flat h α' := hVfl.trans inf_le_right
  have hZs' : ZM (puAmalgam h.le) α ≤ flat h α' := (zm_le_vv h hα).trans hVs'
  have hVs : Vv (puAmalgam h.le) α ≤ stab _ α := (vv_le_qv h hb hα).trans (qv_le_stab _ α)
  have hT2 : IsPGroup 2 ↥(Vv (puAmalgam h.le) α) := (isPGroup_qv _ h20 hβ'H).to_le hVβ'
  obtain ⟨ψ', -, hψ'⟩ := exists_natural_flat_at h hφs hφ hα'
  have hUn : flat h α' ≤
      Subgroup.normalizer (Uloc h.le L α' : Set (puAmalgam h.le).Universal) := hψ'.1
  have hR0 : critR0 (puAmalgam h.le) α α' = ⁅Uloc h.le L α', Vv (puAmalgam h.le) α⁆ := by
    rw [critR0, Subgroup.commutator_comm,
      commutator_zm_eq_commutator_uloc_of_le_qv h hα' hα'β' hVβ']
  have hR : critR (puAmalgam h.le) α α' = ⁅Uloc h.le L α', ZM (puAmalgam h.le) α⁆ := by
    rw [critR, Subgroup.commutator_comm,
      commutator_zm_eq_commutator_uloc_of_le_qv h hα' hα'β' ((zm_le_vv h hα).trans hVβ')]
  have hdim2 : Module.finrank F (commN (natImage ψ' (Vv (puAmalgam h.le) α))) = 2 := by
    have := hR0q
    rw [hR0, card_commutator_eq hψ' hVs', Module.natCard_eq_pow_finrank (K := F)] at this
    exact Nat.pow_right_injective hq this
  have hdim1 : Module.finrank F (commN (natImage ψ' (ZM (puAmalgam h.le) α))) = 1 := by
    have := hRq
    rw [hR, card_commutator_eq hψ' hZs', Module.natCard_eq_pow_finrank (K := F)] at this
    exact Nat.pow_right_injective hq
      (show Nat.card F ^ _ = Nat.card F ^ 1 by rw [pow_one]; exact this)
  have h12 : commN (natImage ψ' (ZM (puAmalgam h.le) α)) ≤
      commN (natImage ψ' (Vv (puAmalgam h.le) α)) :=
    commN_mono (natImage_mono (zm_le_vv h hα))
  have hVnV : Vv (puAmalgam h.le) α ≤
      Subgroup.normalizer (Vv (puAmalgam h.le) α : Set (puAmalgam h.le).Universal) :=
    Subgroup.le_normalizer
  have hVnZ : Vv (puAmalgam h.le) α ≤
      Subgroup.normalizer (ZM (puAmalgam h.le) α : Set (puAmalgam h.le).Universal) :=
    hVs.trans (stab_le_normalizer_zm _ α)
  have hinv : ∀ {A : Subgroup (puAmalgam h.le).Universal}, A ≤ flat h α' →
      Vv (puAmalgam h.le) α ≤ Subgroup.normalizer (A : Set (puAmalgam h.le).Universal) →
      ∀ t (ht : t ∈ Vv (puAmalgam h.le) α), ∀ x ∈ commN (natImage ψ' A),
        ((toSL3 ψ' ⟨t, hVs' ht⟩ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x ∈
          commN (natImage ψ' A) := by
    intro A hA hVA t ht x hx
    obtain ⟨u, rfl⟩ := natVec_surjective hψ' x
    have hu : (u : (puAmalgam h.le).Universal) ∈ ⁅Uloc h.le L α', A⁆ :=
      (mem_commutator_iff_natVec hψ' hA u).mpr hx
    have hn : Vv (puAmalgam h.le) α ≤
        Subgroup.normalizer ((⁅Uloc h.le L α', A⁆ : Subgroup (puAmalgam h.le).Universal) :
          Set (puAmalgam h.le).Universal) :=
      le_normalizer_commutator (hVs'.trans hUn) hVA
    have hmemU : t * (u : (puAmalgam h.le).Universal) * t⁻¹ ∈ Uloc h.le L α' :=
      (Subgroup.mem_normalizer_iff.mp (hUn (hVs' ht)) _).mp u.2
    have hmem : t * (u : (puAmalgam h.le).Universal) * t⁻¹ ∈ ⁅Uloc h.le L α', A⁆ :=
      (Subgroup.mem_normalizer_iff.mp (hn ht) _).mp hu
    rw [← natVec_conj hψ' ⟨t, hVs' ht⟩ u ⟨_, hmemU⟩ rfl]
    exact (mem_commutator_iff_natVec hψ' hA ⟨_, hmemU⟩).mp hmem
  rw [hR0, hR, Subgroup.commutator_le]
  intro r hr t ht
  have hrU : r ∈ Uloc h.le L α' :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp (hVs'.trans hUn) hr
  obtain ⟨k, hk⟩ := hT2 ⟨t, ht⟩
  have hg : ((toSL3 ψ' ⟨t, hVs' ht⟩ : SL3 F) : Matrix (Fin 3) (Fin 3) F) ^ 2 ^ k = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_pow, ← map_pow]
    have : (⟨t, hVs' ht⟩ : ↥(flat h α')) ^ 2 ^ k = 1 := by
      apply Subtype.ext
      have := congrArg Subtype.val hk
      simpa using this
    rw [this, map_one]
    rfl
  have hlin := sub_mem_of_finrank_eq_succ h12 (by rw [hdim1, hdim2]) hg
    (hinv hZs' hVnZ t ht) (hinv hVs' hVnV t ht) (natVec hψ' ⟨r, hrU⟩)
    ((mem_commutator_iff_natVec hψ' hVs' ⟨r, hrU⟩).mp hr)
  have hcU : ⁅r, t⁆ ∈ Uloc h.le L α' :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp (hVs'.trans hUn)
      (Subgroup.commutator_mem_commutator hrU ht)
  have hw := natVec_commutator hψ' ⟨t, hVs' ht⟩ ⟨r, hrU⟩ ⟨_, hcU⟩ rfl
  refine (mem_commutator_iff_natVec hψ' hZs' ⟨_, hcU⟩).mpr ?_
  rw [hw, ← neg_sub]
  exact Submodule.neg_mem _ hlin

theorem vv_comm_le_zm_of_star_flat (hb : 2 < critDist (puAmalgam h.le))
    {α α' : Vtx (puAmalgam h.le)} (hs : Star (puAmalgam h.le) α α') :
    ⁅Vv (puAmalgam h.le) α, Vv (puAmalgam h.le) α⁆ ≤ ZM (puAmalgam h.le) α := by
  have h20 := h.hyp20
  have hb0 := h.critDist_pos
  have hc := hs.1
  have hc' := ms22_iii _ h20 hb0 hC hc
  have hα := hc.1
  have hKn : stab (puAmalgam h.le) α ≤
      Subgroup.normalizer (ZM (puAmalgam h.le) α : Set (puAmalgam h.le).Universal) :=
    stab_le_normalizer_zm _ α
  have hVs : Vv (puAmalgam h.le) α ≤ stab _ α := (vv_le_qv h hb hα).trans (qv_le_stab _ α)
  have hZ's : ZM (puAmalgam h.le) α' ≤ stab _ α := zm_le_stab_right _ h20 hb0 hC hc'
  have hRZ : critR (puAmalgam h.le) α α' ≤ ZM (puAmalgam h.le) α :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp (hZ's.trans hKn)
  have hR0V : critR0 (puAmalgam h.le) α α' ≤ Vv _ α :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp (hZ's.trans (stab_le_normalizer_vv h α))
  have hR0U : ⁅Vv (puAmalgam h.le) α, ZM (puAmalgam h.le) α'⁆ ≤ S46.vvPerp α (ZM _ α) := by
    intro r hr
    rw [S46.mem_vvPerp_iff (hVs.trans hKn)]
    refine ⟨hR0V hr, fun w hw => hRZ ?_⟩
    exact commutator_critR0_vv_le_flat h hU hC hcard hφs hφ hb hs
      (Subgroup.commutator_mem_commutator hr hw)
  have hVL := commutator_vv_ltil_le_of_gen h hα (adj_geo_one_of_isCritical _ hb0 hc)
    (zm_le_qv_geo_one _ h20 hb0 hc) hc'.2.2 (S4A.stab_le_normalizer_vvPerp h hb hα hKn) hR0U
  exact commutator_vv_le_of_ltil_gen h hb hα hKn hVL

end CFSG.Quasithin.MS93.S34G
