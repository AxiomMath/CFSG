module

public import CFSG.Quasithin.MS93.S46I464SD

public section

namespace CFSG.Quasithin.MS93.S46.I464

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S4A
open scoped commutatorElement

section Main

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
  {F : Type} [Field F] [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)} (hφ : IsSL3FullVia M T L φ)
  (hb4 : critDist (puAmalgam h.le) = 4)
include h hφ hb4

theorem exists_bad_of_not_le (h42 : S42) (hmin : PUMin M T L) {x r : Vtx (puAmalgam h.le)}
    (hx : IsMVtx _ x) (hxr : (puAmalgam h.le).treeGraph.Adj x r)
    (hfail : ¬ Usup (puAmalgam h.le) x r ≤ ZH _ r) :
    ∃ y, (puAmalgam h.le).treeGraph.Adj r y ∧ ¬ Usup (puAmalgam h.le) y r ≤ Bloc h.le L x := by
  have hb : 2 < critDist (puAmalgam h.le) := by omega
  by_contra hno
  refine hfail ((h42 G M T L h hmin hb F _ _ φ hφ x r hx hxr).1 (fun δ hδ => ?_)
    (card_usup_of_not_le h hφ hx hxr hfail))
  by_contra hδ'
  exact hno ⟨δ, hδ, hδ'⟩

theorem false_of_isOffenderOn (h42 : S42) (hmin : PUMin M T L)
    (h461 : ∀ x : Vtx (puAmalgam h.le), IsMVtx _ x → centerOf (Vv _ x) ≤ Bloc h.le L x)
    (h462 : ∀ (x : Vtx (puAmalgam h.le)) (As : Subgroup (puAmalgam h.le).Universal),
      IsMVtx _ x → IsOffenderOn (puAmalgam h.le) x (Bloc h.le L x) As →
        ⁅Vv (puAmalgam h.le) x, Vv _ x⁆ ≤ Uloc h.le L x)
    (h463 : ∀ x : Vtx (puAmalgam h.le), IsMVtx _ x →
      ⁅Vv (puAmalgam h.le) x, Qv _ x⁆ ≤ centerOf (Vv _ x))
    (hfail : ∀ x r : Vtx (puAmalgam h.le), IsMVtx _ x → (puAmalgam h.le).treeGraph.Adj x r →
      ¬ Usup (puAmalgam h.le) x r ≤ ZH _ r)
    {x : Vtx (puAmalgam h.le)} (hx : IsMVtx _ x) {As : Subgroup (puAmalgam h.le).Universal}
    (hA : IsOffenderOn (puAmalgam h.le) x (Bloc h.le L x) As) : False := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  have hC := centHyp_of_gen23 h hfull
  obtain ⟨r, hxr⟩ := exists_adj _ x
  obtain ⟨y, hry, hbad⟩ := exists_bad_of_not_le h hφ hb4 h42 hmin hx hxr (hfail x r hx hxr)
  obtain ⟨hcard, -⟩ := card_commutator_zm_qv_of_bad h hφ hb4 h461 h463 hx hxr hry hbad
  obtain ⟨l, hcl, hgeo, hR⟩ := exists_isCritical_of_bad h hφ hC hb4 h461 h463 hx hxr hry hbad
  have hcen := commutator_zm_qv_le_centralizer_stab h hφ hC hb4 h461 h463 hx hxr hry hbad
  have hy := isMVtx_of_adj_adj h hx hxr hry
  have hlx : (puAmalgam h.le).treeGraph.dist x l ≤ 2 := by
    rw [tdist_comm, ← hgeo, dist_geo_crit hb4 hcl (by omega)]
  have hXV : ⁅ZM (puAmalgam h.le) y, Qv _ x⁆ ≤ ⁅Vv (puAmalgam h.le) x, Vv _ x⁆ := by
    rw [← hR, critR]
    exact Subgroup.commutator_mono (zm_le_vv_of_dist h hcl.1 hlx)
      (zm_le_vv_of_dist h hy (dist_le_two_of_adj_adj h hxr hry))
  have hbot : ⁅ZM (puAmalgam h.le) y, Qv _ x⁆ = ⊥ := by
    rw [eq_bot_iff, ← uloc_inf_centralizer_stab h hφ hx]
    exact le_inf (hXV.trans (h462 x As hx hA)) hcen
  rw [hbot, Subgroup.card_bot] at hcard
  have hq : 2 ≤ Fintype.card F := by rw [← Nat.card_eq_fintype_card]; exact Finite.one_lt_card
  omega

theorem dloc_inf_le_centerOf {α β γ : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α)
    (hαβ : (puAmalgam h.le).treeGraph.Adj α β) (hβγ : (puAmalgam h.le).treeGraph.Adj β γ) :
    Dloc h.le L α ⊓ (ZM (puAmalgam h.le) α ⊔ ZM _ γ) ≤ centerOf (Vv _ α) := by
  have h20 := h.hyp20
  have hγ := isMVtx_of_adj_adj h hα hαβ hβγ
  have hDL : Dloc h.le L α ≤ Subgroup.centralizer (Ltil h.le L α : Set _) :=
    (le_of_eq (h.puTrans_Dq hα)).trans inf_le_right
  have hW : ∀ ρ, (puAmalgam h.le).treeGraph.Adj α ρ → ∀ y,
      (puAmalgam h.le).treeGraph.Adj ρ y →
        Dloc h.le L α ⊓ (ZM (puAmalgam h.le) α ⊔ ZM _ γ) ≤ Qv _ y := by
    intro ρ hαρ y hρy
    obtain ⟨g, hg, hgρ⟩ := exists_mem_stab_smul _ hαβ hαρ
    obtain ⟨l, hl, hlβ⟩ := exists_mem_ltil_smul_eq h hφ hα (qv_le_stab_of_adj _ hαβ) hg
    rw [hgρ] at hlβ
    have hlγ : (puAmalgam h.le).treeGraph.Adj ρ (l • γ) := by
      rw [← hlβ]
      exact (adj_smul _ l β γ).mpr hβγ
    have hlγM : IsMVtx _ (l • γ) := (isMVtx_smul _ l γ).mpr hγ
    have hαy : (puAmalgam h.le).treeGraph.dist α y ≤ 3 := by
      have := dist_triangle _ α ρ y
      rw [dist_eq_one_of_adj _ hαρ, dist_eq_one_of_adj _ hρy] at this
      omega
    have hly : (puAmalgam h.le).treeGraph.dist (l • γ) y ≤ 3 := by
      have := dist_triangle _ (l • γ) ρ y
      rw [dist_eq_one_of_adj _ hlγ.symm, dist_eq_one_of_adj _ hρy] at this
      omega
    intro w hw
    have hwc : l * w = w * l := Subgroup.mem_centralizer_iff.mp (hDL hw.1) l hl
    have hw' : w = l * w * l⁻¹ := by rw [hwc, mul_inv_cancel_right]
    have hmem : l * w * l⁻¹ ∈ (ZM (puAmalgam h.le) α ⊔ ZM _ γ).map
        (MulAut.conj l).toMonoidHom := conj_mem_map_conj hw.2
    rw [Subgroup.map_sup, map_conj_eq_of_mem_normalizer
      (stab_le_normalizer_zm _ α (ltil_le_stab h α hl)), ← zm_smul] at hmem
    rw [hw']
    exact (sup_le (zm_le_qv_of_dist_le_three hb4 hα hαy)
      (zm_le_qv_of_dist_le_three hb4 hlγM hly)) hmem
  refine le_inf (inf_le_right.trans (sup_le (zm_le_vv h hα)
    (zm_le_vv_of_dist h hγ (dist_le_two_of_adj_adj h hαβ hβγ)))) ?_
  rw [Subgroup.le_centralizer_iff, vv_eq_iSup_vv hα]
  refine iSup₂_le fun ρ hρ => ?_
  have hρH : ¬ IsMVtx (puAmalgam h.le) ρ := (isMVtx_iff_of_adj _ hρ).mp hα
  rw [vv_eq_iSup_of_not_isMVtx hρH]
  refine iSup₂_le fun y hy => ?_
  have hyM : IsMVtx (puAmalgam h.le) y := by have := isMVtx_iff_of_adj _ hy; tauto
  exact (zm_le_centralizer_qv _ h20 hyM).trans (Subgroup.centralizer_le (hW ρ hρ y hy))

theorem usup_le_centerOf_of_le_bloc (hC : CentHyp (puAmalgam h.le))
    {α β γ : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α)
    (hαβ : (puAmalgam h.le).treeGraph.Adj α β) (hβγ : (puAmalgam h.le).treeGraph.Adj β γ)
    (hU : Usup (puAmalgam h.le) γ β ≤ Bloc h.le L α)
    (hcard : Nat.card ↥(Usup (puAmalgam h.le) α β) = Fintype.card F ^ 2) :
    Usup (puAmalgam h.le) γ β ≤ centerOf (Vv _ α) := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  have : CharP F 2 := charP_two_of_isSL3FullVia hφ
  have hb : 2 < critDist (puAmalgam h.le) := by omega
  have hb0 : 0 < critDist (puAmalgam h.le) := by omega
  obtain ⟨ψ, hψs, hψ⟩ := exists_natural_Uloc h hφ hα
  have hG := S4A.usup_le_usup_sup_dloc h hfull hC hb hα hαβ hβγ hψs hψ hU
    (by rw [hcard, Nat.card_eq_fintype_card])
  have hγ := isMVtx_of_adj_adj h hα hαβ hβγ
  have hDn : Usup (puAmalgam h.le) α β ≤
      Subgroup.normalizer (Dloc h.le L α : Set (puAmalgam h.le).Universal) :=
    ((usup_le_zm h hα hαβ).trans ((zm_le_qv_self _ hα hb0).trans (qv_le_stab _ α))).trans
      (stab_le_normalizer_puTrans h.le (S4A.Dq_normal h) α)
  intro u hu
  have hu' : u ∈ ((Usup (puAmalgam h.le) α β ⊔ Dloc h.le L α : Subgroup _) : Set _) := hG hu
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hDn] at hu'
  obtain ⟨x, hx, w, hw, rfl⟩ := hu'
  have hxZ : x ∈ ZM (puAmalgam h.le) α := usup_le_zm h hα hαβ hx
  have hwZ : w ∈ ZM (puAmalgam h.le) α ⊔ ZM _ γ := by
    have e : w = x⁻¹ * (x * w) := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.inv_mem _ hxZ))
      (Subgroup.mem_sup_right (usup_le_zm h hγ hβγ.symm hu))
  exact (centerOf (Vv (puAmalgam h.le) α)).mul_mem (zm_le_centerOf_vv h hb hα hxZ)
    (dloc_inf_le_centerOf h hφ hb4 hα hαβ hβγ ⟨hw, hwZ⟩)

omit hφ hb4 in
theorem stab_le_normalizer_bloc' (δ : Vtx (puAmalgam h.le)) :
    stab _ δ ≤ Subgroup.normalizer (Bloc h.le L δ : Set _) :=
  le_normalizer_of_map_conj_le fun g hg => by rw [← bloc_smul h g δ, (mem_stab _).mp hg]

theorem lt_relIndex_of_not_isOffenderOn {α α' γ : Vtx (puAmalgam h.le)}
    (hc : IsCritical (puAmalgam h.le) α α')
    (hnooff : ∀ As : Subgroup (puAmalgam h.le).Universal,
      ¬ IsOffenderOn (puAmalgam h.le) α (Bloc h.le L α) As)
    (hR : ⁅ZM (puAmalgam h.le) α', Qv _ γ⁆ ≤ ZM _ α) :
    Fintype.card F < (Qv (puAmalgam h.le) γ).relIndex (Vv _ α) := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  have hC := centHyp_of_gen23 h hfull
  have hb : 2 < critDist (puAmalgam h.le) := by omega
  have hb0 : 0 < critDist (puAmalgam h.le) := by omega
  have h20 := h.hyp20
  have hα := hc.1
  have hc' := ms22_iii _ h20 hb0 hC hc
  have hαβ := adj_geo_one_of_isCritical _ hb0 hc
  have hVs : Vv (puAmalgam h.le) α ≤ stab _ α := (vv_le_qv h hb hα).trans (qv_le_stab _ α)
  have hBV : Bloc h.le L α ≤ Vv _ α := (Subgroup.closure_le _).mpr fun _ hx => hx.1
  have hBn := stab_le_normalizer_bloc' h α
  have hZ'a : ZM (puAmalgam h.le) α' ≤ stab _ α := zm_le_stab_of_isCritical _ h20 hb0 hc
  have hZab := (isElemAbelian_zm _ h20 hb0 hc'.1).1
  refine not_le.mp fun hle => hnooff (ZM (puAmalgam h.le) α') ⟨⟨_, hαβ,
    zm_le_qv_geo_one _ h20 hb0 hc⟩, hc'.2.2,
    fun z hz => by rw [(isElemAbelian_zm _ h20 hb0 hc'.1).2 z hz]; exact Subgroup.one_mem _,
    fun z hz z' hz' => ?_, (Vv (puAmalgam h.le) α ⊓ Qv _ γ) ⊔ Bloc h.le L α, le_sup_right,
    sup_le inf_le_left hBV, ?_, ?_⟩
  · have : z * z' = z' * z := by
      have := hZab.is_comm.comm ⟨z, hz⟩ ⟨z', hz'⟩
      simpa using congrArg Subtype.val this
    rw [commutatorElement_eq_one_iff_mul_comm.mpr this]
    exact Subgroup.one_mem _
  · refine S4A.commutator_sup_le_of ?_
      (Subgroup.le_normalizer_iff_commutator_le_left.mp (hZ'a.trans hBn))
      ((inf_le_left.trans hVs).trans hBn) ((hBV.trans hVs).trans hBn)
    exact (Subgroup.commutator_mono inf_le_right le_rfl).trans
      ((Subgroup.commutator_comm _ _).le.trans (hR.trans (zm_le_bloc h hb hα)))
  · have := finite_stab h hα
    have : Finite ↥(Vv (puAmalgam h.le) α) :=
      Finite.of_injective _ (Subgroup.inclusion_injective hVs)
    have h1 : ((Vv (puAmalgam h.le) α ⊓ Qv _ γ) ⊔ Bloc h.le L α).relIndex (Vv _ α) ≤
        (Vv (puAmalgam h.le) α ⊓ Qv _ γ).relIndex (Vv _ α) :=
      Subgroup.relIndex_le_of_le_left le_sup_left (by
        rw [Subgroup.relIndex]; exact Subgroup.index_ne_zero_of_finite)
    rw [Subgroup.inf_relIndex_left] at h1
    refine h1.trans (hle.trans ?_)
    rcases crit_type h hφ hC hc' with ⟨hq, -⟩ | ⟨hq, -⟩ | ⟨hq, -⟩ <;> rw [hq]
    exact Nat.le_self_pow two_ne_zero _

theorem usup_le_zm_of_le_centerOf {α β γ : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α)
    (hαβ : (puAmalgam h.le).treeGraph.Adj α β) (hβγ : (puAmalgam h.le).treeGraph.Adj β γ)
    (hVZ : ⁅Vv (puAmalgam h.le) α, Vv _ α⁆ ≤ ZM _ α)
    (hcard : Nat.card ↥(Usup (puAmalgam h.le) γ β) = Fintype.card F ^ 2)
    (hZV : Usup (puAmalgam h.le) γ β ≤ centerOf (Vv _ α))
    (hidx : Fintype.card F < (Qv (puAmalgam h.le) γ).relIndex (Vv _ α)) :
    Usup (puAmalgam h.le) γ β ≤ ZM _ α := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  have hb : 2 < critDist (puAmalgam h.le) := by omega
  have hγ := isMVtx_of_adj_adj h hα hαβ hβγ
  have hUγV : Uloc h.le L γ ≤ Vv _ α :=
    (uloc_le_zm h hfull hγ).trans (zm_le_vv_of_dist h hγ (dist_le_two_of_adj_adj h hαβ hβγ))
  have hB1 : ⁅Uloc h.le L γ, Vv (puAmalgam h.le) α⁆ ≤ ZM _ α :=
    (Subgroup.commutator_mono hUγV le_rfl).trans hVZ
  have hVβ : Vv (puAmalgam h.le) α ≤ Qv _ β :=
    (vv_le_qv h hb hα).trans (qv_le_qv _ h.hyp20 hα hαβ)
  have hUγβ : Usup (puAmalgam h.le) γ β = ⁅Uloc h.le L γ, Qv _ β⁆ :=
    S4A.usup_eq_commutator_uloc h hfull hγ hβγ.symm
  rw [hUγβ] at hcard hZV ⊢
  by_contra hnot
  refine absurd (relIndex_le_of_le_centralizer h hφ hγ hβγ.symm le_rfl hVβ hcard
    (hZV.trans inf_le_right) fun he => hnot ?_) (not_le.mpr hidx)
  rw [← he]
  exact hB1

omit hb4 in
theorem commutator_usup_qv_eq_bot {α β γ : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α)
    (hαβ : (puAmalgam h.le).treeGraph.Adj α β) (hβγ : (puAmalgam h.le).treeGraph.Adj β γ)
    (hfail : ¬ Usup (puAmalgam h.le) α β ≤ ZH _ β)
    (hUZ : Usup (puAmalgam h.le) γ β ≤ ZM _ α) {R : Subgroup (puAmalgam h.le).Universal}
    (hRU : R ≤ Uloc h.le L α ⊓ Subgroup.centralizer (Qv (puAmalgam h.le) β : Set _))
    (hRcard : Nat.card ↥R = Fintype.card F)
    (hRc : R ≤ Subgroup.centralizer (stab (puAmalgam h.le) γ : Set _)) :
    ⁅Usup (puAmalgam h.le) γ β, Qv _ β⁆ = ⊥ := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  have hγ := isMVtx_of_adj_adj h hα hαβ hβγ
  have hUn : Qv (puAmalgam h.le) β ≤
      Subgroup.normalizer (Uloc h.le L α : Set (puAmalgam h.le).Universal) :=
    (qv_le_stab_of_adj _ hαβ.symm).trans (stab_le_normalizer_puTrans h.le (S4A.Uq_normal h) α)
  have hUn' : Qv (puAmalgam h.le) β ≤
      Subgroup.normalizer (Uloc h.le L γ : Set (puAmalgam h.le).Universal) :=
    (qv_le_stab_of_adj _ hβγ).trans (stab_le_normalizer_puTrans h.le (S4A.Uq_normal h) γ)
  have hUγβ : Usup (puAmalgam h.le) γ β = ⁅Uloc h.le L γ, Qv _ β⁆ :=
    S4A.usup_eq_commutator_uloc h hfull hγ hβγ.symm
  have hT1 : ⁅Usup (puAmalgam h.le) γ β, Qv _ β⁆ ≤ Uloc h.le L α := by
    refine (Subgroup.commutator_mono hUZ le_rfl).trans ?_
    have := usup_le_uloc h hfull hα hαβ
    rwa [Usup, zv_of_isMVtx _ hα] at this
  have hT2 : ⁅Usup (puAmalgam h.le) γ β, Qv _ β⁆ ≤ Subgroup.centralizer (Qv _ β : Set _) := by
    rw [hUγβ]
    exact commutator_commutator_uloc_le h hφ hγ hβγ.symm le_rfl
  have hCU : Nat.card ↥(Uloc h.le L α ⊓
      Subgroup.centralizer (Qv (puAmalgam h.le) β : Set (puAmalgam h.le).Universal)) ≤
      Fintype.card F := by
    refine card_uloc_inf_centralizer_le h hφ hα hαβ le_rfl fun hle => hfail ?_
    rw [S4A.usup_eq_commutator_uloc h hfull hα hαβ]
    intro z hz
    exact mem_zh_of_mem_zm h hα hαβ (uloc_le_zm h hfull hα
      ((Subgroup.le_normalizer_iff_commutator_le_left.mp hUn) hz)) (hle hz)
  have hfinS := finite_stab h hα
  have hfinW : Finite ↥(Uloc h.le L α ⊓
      Subgroup.centralizer (Qv (puAmalgam h.le) β : Set (puAmalgam h.le).Universal)) :=
    Finite.of_injective _ (Subgroup.inclusion_injective (inf_le_left.trans
      (puTrans_le_stab h.le _ α)))
  have hReq : R = Uloc h.le L α ⊓ Subgroup.centralizer (Qv (puAmalgam h.le) β : Set _) :=
    Subgroup.eq_of_le_of_card_ge hRU (hCU.trans hRcard.ge)
  have hT3 : ⁅Usup (puAmalgam h.le) γ β, Qv _ β⁆ ≤ Uloc h.le L γ := by
    rw [hUγβ]
    exact (Subgroup.commutator_mono (Subgroup.le_normalizer_iff_commutator_le_left.mp hUn')
      le_rfl).trans (Subgroup.le_normalizer_iff_commutator_le_left.mp hUn')
  rw [eq_bot_iff, ← uloc_inf_centralizer_stab h hφ hγ]
  exact le_inf hT3 ((le_inf hT1 hT2).trans (hReq.ge.trans hRc))

theorem false_of_usup_le_bloc
    (h463 : ∀ x : Vtx (puAmalgam h.le), IsMVtx _ x → ⁅Vv (puAmalgam h.le) x, Vv _ x⁆ ≤ ZM _ x)
    (hfail : ∀ x r : Vtx (puAmalgam h.le), IsMVtx _ x → (puAmalgam h.le).treeGraph.Adj x r →
      ¬ Usup (puAmalgam h.le) x r ≤ ZH _ r)
    (hnooff : ∀ (x : Vtx (puAmalgam h.le)) (As : Subgroup (puAmalgam h.le).Universal),
      IsMVtx _ x → ¬ IsOffenderOn (puAmalgam h.le) x (Bloc h.le L x) As)
    {α α' : Vtx (puAmalgam h.le)} (hc : IsCritical (puAmalgam h.le) α α')
    (hR : ⁅ZM (puAmalgam h.le) α', Qv _ (geo (puAmalgam h.le) α α' 2)⁆ =
      critR (puAmalgam h.le) α α')
    (hRc : ⁅ZM (puAmalgam h.le) α', Qv _ (geo (puAmalgam h.le) α α' 2)⁆ ≤
      Subgroup.centralizer (stab (puAmalgam h.le) (geo (puAmalgam h.le) α α' 2) : Set _))
    (hRcard : Nat.card ↥⁅ZM (puAmalgam h.le) α', Qv _ (geo (puAmalgam h.le) α α' 2)⁆ =
      Fintype.card F)
    (hU : Usup (puAmalgam h.le) (geo (puAmalgam h.le) α α' 2) (geo (puAmalgam h.le) α α' 1) ≤
      Bloc h.le L α) : False := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  have hC := centHyp_of_gen23 h hfull
  have hb0 : 0 < critDist (puAmalgam h.le) := by omega
  have hα := hc.1
  have hαβ := adj_geo_one_of_isCritical _ hb0 hc
  have hβγ := adj_geo_crit hb4 hc (i := 1) (by omega)
  have hγ : IsMVtx _ (geo (puAmalgam h.le) α α' 2) := isMVtx_geo_two' hb4 hc
  have hRZ := hR.le.trans (critR_le_zm_left h hc)
  have hZV := usup_le_centerOf_of_le_bloc h hφ hb4 hC hα hαβ hβγ hU
    (card_usup_of_not_le h hφ hα hαβ (hfail _ _ hα hαβ))
  have hidx := lt_relIndex_of_not_isOffenderOn h hφ hb4 hc (fun As => hnooff α As hα) hRZ
  have hUZ := usup_le_zm_of_le_centerOf h hφ hb4 hα hαβ hβγ (h463 α hα)
    (card_usup_of_not_le h hφ hγ hβγ.symm (hfail _ _ hγ hβγ.symm)) hZV hidx
  have hRU : ⁅ZM (puAmalgam h.le) α', Qv _ (geo (puAmalgam h.le) α α' 2)⁆ ≤
      Uloc h.le L α ⊓ Subgroup.centralizer (Qv (puAmalgam h.le) (geo _ α α' 1) : Set _) := by
    refine le_inf ?_ (hRc.trans (Subgroup.centralizer_le (qv_le_stab_of_adj _ hβγ)))
    rw [hR, (critR_eq_commutator_uloc h hφ hc).1]
    exact (critR_eq_commutator_uloc h hφ hc).2
  have hbot := commutator_usup_qv_eq_bot h hφ hα hαβ hβγ (hfail _ _ hα hαβ) hUZ hRU
    hRcard hRc
  apply hfail _ _ hγ hβγ.symm
  intro z hz
  exact mem_zh_of_mem_zm h hγ hβγ.symm (usup_le_zm h hγ hβγ.symm hz)
    ((Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot) hz)

theorem usup_le_zh_of_items (h14 : MS14AS) (hSQ : SQTKQuot) (h42 : S42) (hmin : PUMin M T L)
    (h461 : ∀ x : Vtx (puAmalgam h.le), IsMVtx _ x → centerOf (Vv _ x) ≤ Bloc h.le L x)
    (h462 : ∀ (x : Vtx (puAmalgam h.le)) (As : Subgroup (puAmalgam h.le).Universal),
      IsMVtx _ x → IsOffenderOn (puAmalgam h.le) x (Bloc h.le L x) As →
        ⁅Vv (puAmalgam h.le) x, Vv _ x⁆ ≤ Uloc h.le L x)
    (h463 : ∀ x : Vtx (puAmalgam h.le), IsMVtx _ x →
      ⁅Vv (puAmalgam h.le) x, Qv _ x⁆ ≤ centerOf (Vv _ x) ∧
        ⁅Vv (puAmalgam h.le) x, Vv _ x⁆ ≤ ZM _ x)
    {α β : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α) (hαβ : (puAmalgam h.le).treeGraph.Adj α β) :
    Usup (puAmalgam h.le) α β ≤ ZH _ β := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  have hC := centHyp_of_gen23 h hfull
  have h463a := fun x hx => (h463 x hx).1
  have h463b := fun x hx => (h463 x hx).2
  by_contra hfail0
  have hfail : ∀ x r : Vtx (puAmalgam h.le), IsMVtx _ x → (puAmalgam h.le).treeGraph.Adj x r →
      ¬ Usup (puAmalgam h.le) x r ≤ ZH _ r := fun x r hx hxr =>
    not_usup_le_zh_of_edge h hα hαβ hx hxr hfail0
  have hnooff : ∀ (x : Vtx (puAmalgam h.le)) (As : Subgroup (puAmalgam h.le).Universal),
      IsMVtx _ x → ¬ IsOffenderOn (puAmalgam h.le) x (Bloc h.le L x) As := fun x As hx hA =>
    false_of_isOffenderOn h hφ hb4 h42 hmin h461 h462 h463a hfail hx hA
  obtain ⟨y, hβy, hbad⟩ := exists_bad_of_not_le h hφ hb4 h42 hmin hα hαβ hfail0
  obtain ⟨α', hc, hR, hRc, hRcard⟩ := exists_special h hφ hC hb4 h461 h463a hα hαβ hβy hbad
  by_cases hU : Usup (puAmalgam h.le) (geo (puAmalgam h.le) α α' 2)
      (geo (puAmalgam h.le) α α' 1) ≤ Bloc h.le L α
  · exact false_of_usup_le_bloc h hφ hb4 h463b hfail hnooff hc hR hRc hRcard hU
  ·
    have hb0 : 0 < critDist (puAmalgam h.le) := by omega
    have h20 := h.hyp20
    have hαβ₁ := adj_geo_one_of_isCritical _ hb0 hc
    have hβ₁γ := adj_geo_crit hb4 hc (i := 1) (by omega)
    have hRZ := hR.le.trans (critR_le_zm_left h hc)
    have hab := commutator_conjCl_eq_bot_of_bad h hφ hb4 h14 hSQ hC h461 h463a hc.1 hαβ₁ hβ₁γ hU
    apply conjCl_not_le_qv h hC hb4 hc.1 hαβ₁ hβ₁γ hU hfull hc hRZ
    have hγ : IsMVtx _ (geo (puAmalgam h.le) α α' 2) := isMVtx_geo_two' hb4 hc
    rw [← hC _ _ hγ hβ₁γ.symm]
    refine le_inf ((conjCl_le_of_le_normalizer (zm_le_qv_of_adj_adj h hb4 hc.1 hαβ₁ hβ₁γ)
      (stab_le_normalizer_qv _ α)).trans (qv_le_qv _ h20 hc.1 hαβ₁)) ?_
    have hcen := (Subgroup.commutator_eq_bot_iff_le_centralizer).mp hab
    exact hcen.trans (Subgroup.centralizer_le (le_conjCl _ _))

end Main

end CFSG.Quasithin.MS93.S46.I464

namespace CFSG.Quasithin.MS93.S46

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible

theorem i464_of (h42 : S42) (h461 : I461) (h462 : I462) (h463 : I463) (h14 : MS14AS)
    (hSQ : SQTKQuot) : I464 := by
  intro G _ _ M T L F _ _ φ c α β hα hαβ
  exact I464.usup_le_zh_of_items c.pu c.via c.b4 h14 hSQ h42 c.min
    (fun x hx => h461 G M T L F φ c x hx) (fun x As hx hA => h462 G M T L F φ c x As hx hA)
    (fun x hx => h463 G M T L F φ c x hx) hα hαβ

end CFSG.Quasithin.MS93.S46
