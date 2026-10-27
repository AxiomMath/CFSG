module

public import CFSG.Quasithin.MS93.S4A43XA

public section

namespace CFSG.Quasithin.MS93.S4A

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

section General

variable {G : Type*} [Group G]

theorem map_conj_eq_of_le_centralizer {K S : Subgroup G} (hK : K ≤ Subgroup.centralizer (S : Set G))
    {g : G} (hg : g ∈ S) : K.map (MulAut.conj g).toMonoidHom = K := by
  ext x
  rw [mem_map_conj]
  have hc : ∀ y ∈ K, g * y = y * g := fun y hy => Subgroup.mem_centralizer_iff.mp (hK hy) g hg
  constructor
  · intro hx
    have hy := hc _ hx
    have e : x = g⁻¹ * x * g := by
      calc x = g * (g⁻¹ * x * g) * g⁻¹ := by group
        _ = (g⁻¹ * x * g) * g * g⁻¹ := by rw [hy]
        _ = g⁻¹ * x * g := by group
    rw [e]
    exact hx
  · intro hx
    have e : g⁻¹ * x * g = x := by
      calc g⁻¹ * x * g = g⁻¹ * (x * g) := by group
        _ = g⁻¹ * (g * x) := by rw [hc x hx]
        _ = x := by group
    rw [e]
    exact hx

end General

section StarBasic

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)

theorem zm_le_qv_geo_one_of_star {α α' : Vtx (puAmalgam h.le)}
    (hs : Star (puAmalgam h.le) α α') :
    ZM (puAmalgam h.le) α' ≤ Qv (puAmalgam h.le) (geo (puAmalgam h.le) α α' 1) :=
  MS93.zm_le_qv_geo_one _ h.hyp20 h.critDist_pos hs.1

theorem zm_le_stab_of_star {α α' : Vtx (puAmalgam h.le)} (hs : Star (puAmalgam h.le) α α') :
    ZM (puAmalgam h.le) α' ≤ stab (puAmalgam h.le) α :=
  zm_le_stab_of_isCritical _ h.hyp20 h.critDist_pos hs.1

theorem critR0_le_vv {α α' : Vtx (puAmalgam h.le)} (hs : Star (puAmalgam h.le) α α') :
    critR0 (puAmalgam h.le) α α' ≤ Vv (puAmalgam h.le) α :=
  Subgroup.le_normalizer_iff_commutator_le_left.mp
    ((zm_le_stab_of_star h hs).trans (stab_le_normalizer_vv h α))

theorem critR_le_critR0 {α α' : Vtx (puAmalgam h.le)} (hs : Star (puAmalgam h.le) α α') :
    critR (puAmalgam h.le) α α' ≤ critR0 (puAmalgam h.le) α α' :=
  Subgroup.commutator_mono (zm_le_vv h hs.1.1) le_rfl

theorem critR_le_zm {α α' : Vtx (puAmalgam h.le)} (hs : Star (puAmalgam h.le) α α') :
    critR (puAmalgam h.le) α α' ≤ ZM (puAmalgam h.le) α :=
  Subgroup.le_normalizer_iff_commutator_le_left.mp
    ((zm_le_stab_of_star h hs).trans (stab_le_normalizer_zm _ α))

theorem vv_le_stab_of_star {α α' : Vtx (puAmalgam h.le)} (hs : Star (puAmalgam h.le) α α') :
    Vv (puAmalgam h.le) α ≤ stab (puAmalgam h.le) α' := by
  have hα' : IsMVtx (puAmalgam h.le) α' := hs.1.isMVtx_right _ h.hyp20
  have hb2 := two_le_critDist _ h.hyp20 h.critDist_pos
  have hd : (puAmalgam h.le).treeGraph.dist α' α = critDist (puAmalgam h.le) := by
    rw [tdist_comm]; exact hs.1.2.1
  have h1 : (puAmalgam h.le).treeGraph.Adj α' (geo (puAmalgam h.le) α' α 1) :=
    adj_geo_one _ (by omega)
  have h12 : (puAmalgam h.le).treeGraph.Adj (geo (puAmalgam h.le) α' α 1)
      (geo (puAmalgam h.le) α' α 2) := adj_geo _ (i := 1) (by omega)
  have h2M : IsMVtx (puAmalgam h.le) (geo (puAmalgam h.le) α' α 2) := by
    rw [isMVtx_geo _ (by omega)]
    exact ⟨fun _ => even_two, fun _ => hα'⟩
  exact hs.2.trans ((qv_le_qv _ h.hyp20 h2M h12.symm).trans (qv_le_stab_of_adj _ h1.symm))

theorem critR0_le_zm' {α α' : Vtx (puAmalgam h.le)} (hs : Star (puAmalgam h.le) α α') :
    critR0 (puAmalgam h.le) α α' ≤ ZM (puAmalgam h.le) α' := by
  rw [critR0, Subgroup.commutator_comm]
  exact Subgroup.le_normalizer_iff_commutator_le_left.mp
    ((vv_le_stab_of_star h hs).trans (stab_le_normalizer_zm _ α'))

end StarBasic

namespace Ctx43

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} {h : PUHyp M T L}
  {F : Type} [Field F] [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)} (c : Ctx43 h φ)
include c

local notation "𝔛" => puAmalgam h.le
local notation "𝔘" => GoldAmalgam.Universal (puAmalgam h.le)
local notation "𝔄" => SimpleGraph.Adj (GoldAmalgam.treeGraph (puAmalgam h.le))

theorem critR0_eq {α α' : Vtx 𝔛} (hs : Star 𝔛 α α') :
    critR0 𝔛 α α' = Usup 𝔛 α' (geo 𝔛 α' α 1) := (c.c431A α α' hs).1

theorem card_critR0 {α α' : Vtx 𝔛} (hs : Star 𝔛 α α') :
    Nat.card ↥(critR0 𝔛 α α') = Fintype.card F ^ 2 := (c.c431A α α' hs).2.1

theorem card_critR {α α' : Vtx 𝔛} (hs : Star 𝔛 α α') :
    Nat.card ↥(critR 𝔛 α α') = Fintype.card F := (c.c431A α α' hs).2.2.1

theorem crit_symm {α α' : Vtx 𝔛} (hs : Star 𝔛 α α') : IsCritical 𝔛 α' α :=
  ms22_iii _ h.hyp20 h.critDist_pos c.cent hs.1

theorem isMVtx_geo_two' {α α' : Vtx 𝔛} (hs : Star 𝔛 α α') : IsMVtx 𝔛 (geo 𝔛 α' α 2) :=
  isMVtx_geo_two _ h.hyp20 h.critDist_pos (c.crit_symm hs)

theorem zm_le_vv_geo_two {α α' : Vtx 𝔛} (hs : Star 𝔛 α α') :
    ZM 𝔛 α' ≤ Vv 𝔛 (geo 𝔛 α' α 2) := by
  have hb6 := c.b6
  have hd : (puAmalgam h.le).treeGraph.dist α' α = critDist 𝔛 := (c.crit_symm hs).2.1
  rw [← zv_of_isMVtx _ (c.crit_symm hs).1]
  exact zv_le_vv h (by rw [tdist_comm, dist_geo _ (by omega)])

theorem critR0_le_zloc {α α' : Vtx 𝔛} (hs : Star 𝔛 α α') :
    critR0 𝔛 α α' ≤ Zloc h.le L (geo 𝔛 α' α 2) := by
  rw [critR0, Subgroup.commutator_comm]
  exact (Subgroup.commutator_mono (c.zm_le_vv_geo_two hs) hs.2).trans
    (c.commutator_vv_qv_le_zloc (c.isMVtx_geo_two' hs))

theorem critR0_le_stabCenter {α α' : Vtx 𝔛} (hs : Star 𝔛 α α') :
    critR0 𝔛 α α' ≤ stabCenter 𝔛 (geo 𝔛 α' α 2) :=
  (c.critR0_le_zloc hs).trans (c.zloc_le_stabCenter (c.isMVtx_geo_two' hs))

theorem critR0_le_centralizer {α α' : Vtx 𝔛} (hs : Star 𝔛 α α') :
    critR0 𝔛 α α' ≤ Subgroup.centralizer (stab 𝔛 (geo 𝔛 α' α 2) : Set 𝔘) :=
  (c.critR0_le_zloc hs).trans (zloc_le_centralizer_stab h c.full (c.isMVtx_geo_two' hs))

theorem not_zm_le_qv {α α' : Vtx 𝔛} (hs : Star 𝔛 α α') : ¬ ZM 𝔛 α' ≤ Qv 𝔛 α :=
  (c.crit_symm hs).2.2

theorem critR_le_uloc {α α' : Vtx 𝔛} (hs : Star 𝔛 α α') : critR 𝔛 α α' ≤ Uloc h.le L α := by
  rw [critR, commutator_zm_eq_uloc h c.full hs.1.1 (zm_le_stab_of_star h hs)]
  exact Subgroup.le_normalizer_iff_commutator_le_left.mp ((zm_le_stab_of_star h hs).trans
    (stab_le_normalizer_puTrans h.le (S4A.Uq_normal h) α))

theorem not_critR0_le_zm {α α' : Vtx 𝔛} (hs : Star 𝔛 α α') : ¬ critR0 𝔛 α α' ≤ ZM 𝔛 α := by
  intro hle
  have hq : 1 < Fintype.card F := Fintype.one_lt_card
  have := le_relIndex_vv_of_isC1 h c.full c.hb hs.1.1
    (adj_geo_one_of_isCritical _ h.critDist_pos hs.1) (c.isC1 hs.1.1)
    (zm_le_qv_geo_one_of_star h hs) (c.not_zm_le_qv hs) (D := Vv 𝔛 α) hle
  rw [Subgroup.relIndex_self] at this
  omega

theorem le_relIndex_critR0 {α α' : Vtx 𝔛} (hs : Star 𝔛 α α') :
    Fintype.card F ≤ (ZM 𝔛 α).relIndex (critR0 𝔛 α α') := by
  have hα := hs.1.1
  obtain ⟨x, hxZ, hxQ⟩ := IsConcreteLE.not_le_iff_exists.mp (c.not_zm_le_qv hs)
  have hxs : x ∈ stab 𝔛 α := zm_le_stab_of_star h hs hxZ
  have hVn := stab_le_normalizer_vv h α
  have hab : ⁅Vv 𝔛 α, Vv 𝔛 α⁆ = ⊥ := vv_comm_eq_bot h (by have := c.b6; omega) hα
  have hval : ∀ v ∈ Vv 𝔛 α, ⁅x, v⁆ ∈ Vv 𝔛 α := fun v hv => by
    have := Subgroup.le_normalizer_iff_commutator_le_left.mp
      (((Subgroup.zpowers_le).mpr hxs).trans hVn)
      (Subgroup.commutator_mem_commutator hv (Subgroup.mem_zpowers x))
    rw [← commutatorElement_inv]
    exact Subgroup.inv_mem _ this
  have hcomm : Vv 𝔛 α ≤ Subgroup.centralizer (Vv 𝔛 α : Set 𝔘) := by
    rwa [← Subgroup.commutator_eq_bot_iff_le_centralizer]
  set g := subCommHom (Vv 𝔛 α) (Vv 𝔛 α) x hval hcomm with hg
  set D : Subgroup 𝔘 := ((ZM 𝔛 α).comap g).map (Vv 𝔛 α).subtype with hD
  have hDX : ⁅D, Subgroup.zpowers x⁆ ≤ ZM 𝔛 α := by
    rw [Subgroup.commutator_comm, Subgroup.zpowers_eq_closure]
    refine commutator_closure_le_of (fun s hs' d hd => ?_) ?_
    · rw [Set.mem_singleton_iff] at hs'
      subst hs'
      obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hd
      exact hv
    · rw [← Subgroup.zpowers_eq_closure]
      exact ((Subgroup.zpowers_le).mpr hxs).trans (stab_le_normalizer_zm _ α)
  have hβ := adj_geo_one_of_isCritical _ h.critDist_pos hs.1
  have hq := le_relIndex_vv_of_isC1 h c.full c.hb hα hβ (c.isC1 hα)
    ((Subgroup.zpowers_le).mpr (zm_le_qv_geo_one_of_star h hs hxZ))
    (fun hle => hxQ (hle (Subgroup.mem_zpowers x))) hDX
  have hDsub : D.subgroupOf (Vv 𝔛 α) = (ZM 𝔛 α).comap g := by
    rw [hD, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective (Vv 𝔛 α).subtype_injective]
  rw [Subgroup.relIndex, hDsub, Subgroup.index_comap] at hq
  have hrange : g.range ≤ critR0 𝔛 α α' := by
    rintro _ ⟨v, rfl⟩
    rw [hg, subCommHom_apply, ← commutatorElement_inv]
    exact Subgroup.inv_mem _ (Subgroup.commutator_mem_commutator v.2 hxZ)
  have hfin : Finite ↥(critR0 𝔛 α α') := by
    have := finite_qv _ h.hyp20 (by rw [← isMVtx_iff_of_adj _ hβ]; exact hα)
    exact Finite.of_injective _ (Subgroup.inclusion_injective
      ((critR0_le_vv h hs).trans ((vv_le_qv h c.hb hα).trans (qv_le_qv _ h.hyp20 hα hβ))))
  exact hq.trans (Subgroup.relIndex_le_of_le_right hrange Subgroup.index_ne_zero_of_finite)

theorem critR0_inf_zm {α α' : Vtx 𝔛} (hs : Star 𝔛 α α') :
    critR0 𝔛 α α' ⊓ ZM 𝔛 α = critR 𝔛 α α' := by
  have hle : critR 𝔛 α α' ≤ critR0 𝔛 α α' ⊓ ZM 𝔛 α :=
    le_inf (critR_le_critR0 h hs) (critR_le_zm h hs)
  have hβ := adj_geo_one_of_isCritical _ h.critDist_pos hs.1
  have hfin : Finite ↥(critR0 𝔛 α α' ⊓ ZM 𝔛 α) := by
    have := finite_qv _ h.hyp20 (by rw [← isMVtx_iff_of_adj _ hβ]; exact hs.1.1)
    exact Finite.of_injective _ (Subgroup.inclusion_injective
      (inf_le_left.trans ((critR0_le_vv h hs).trans ((vv_le_qv h c.hb hs.1.1).trans
        (qv_le_qv _ h.hyp20 hs.1.1 hβ)))))
  symm
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  have hmul := relIndex_mul_card_inf (ZM 𝔛 α) (critR0 𝔛 α α')
  rw [c.card_critR0 hs, inf_comm] at hmul
  rw [c.card_critR hs]
  have hq := c.le_relIndex_critR0 hs
  have hqpos : 0 < Fintype.card F := Fintype.card_pos
  by_contra hlt
  push Not at hlt
  have : Fintype.card F * (Fintype.card F + 1) ≤
      (ZM 𝔛 α).relIndex (critR0 𝔛 α α') * Nat.card ↥(critR0 𝔛 α α' ⊓ ZM 𝔛 α) :=
    Nat.mul_le_mul hq hlt
  rw [hmul] at this
  nlinarith

theorem critR0_inf_stabCenter {α α' : Vtx 𝔛} (hs : Star 𝔛 α α') :
    critR0 𝔛 α α' ⊓ stabCenter 𝔛 α = ⊥ := by
  have hα := hs.1.1
  rw [eq_bot_iff]
  rintro r ⟨hr, hrC⟩
  have hrQ : r ∈ Qv 𝔛 α := vv_le_qv h c.hb hα (critR0_le_vv h hs hr)
  have hr2 : r ^ 2 = 1 :=
    (isElemAbelian_zm _ h.hyp20 h.critDist_pos (c.crit_symm hs).1).2 r (critR0_le_zm' h hs hr)
  have hrc : r ∈ Subgroup.centralizer (Qv 𝔛 α : Set 𝔘) :=
    Subgroup.mem_centralizer_iff.mpr fun y hy =>
      (((mem_stabCenter_iff_comm _).mp hrC).2 y (qv_le_stab _ α hy))
  have hrZ : r ∈ ZM 𝔛 α := by
    rw [← xm_eq_zm h c.full hα]
    exact Subgroup.subset_closure ⟨⟨hrQ, hrc⟩, hr2⟩
  have hrR : r ∈ critR 𝔛 α α' := by
    rw [← c.critR0_inf_zm hs]
    exact ⟨hr, hrZ⟩
  have := c.uloc_inf_stabCenter hα
  rw [eq_bot_iff] at this
  exact this ⟨c.critR_le_uloc hs hrR, hrC⟩

theorem six_lt_critDist : 6 < critDist 𝔛 := by
  by_contra hle
  have hb6 := c.b6
  have hb : critDist 𝔛 = 6 := by omega
  obtain ⟨α, α', hs⟩ := c.ex
  have hα := hs.1.1
  have hα'M : IsMVtx 𝔛 α' := (c.crit_symm hs).1
  have hd : (puAmalgam h.le).treeGraph.dist α α' = 6 := hs.1.2.1.trans hb
  have hd' : (puAmalgam h.le).treeGraph.dist α' α = 6 := by rw [tdist_comm]; exact hd
  have hηeq : geo 𝔛 α' α 4 = geo 𝔛 α α' 2 := by
    rw [← geo_symm _ (show 2 ≤ (puAmalgam h.le).treeGraph.dist α α' by omega), hd]
  have hα'ε : 𝔄 α' (geo 𝔛 α' α 1) := adj_geo_one _ (by omega)
  have hεγ : 𝔄 (geo 𝔛 α' α 1) (geo 𝔛 α' α 2) := adj_geo _ (i := 1) (by omega)
  have hγζ : 𝔄 (geo 𝔛 α' α 2) (geo 𝔛 α' α 3) := adj_geo _ (i := 2) (by omega)
  have hζη : 𝔄 (geo 𝔛 α' α 3) (geo 𝔛 α' α 4) := adj_geo _ (i := 3) (by omega)
  have hγM : IsMVtx 𝔛 (geo 𝔛 α' α 2) := c.isMVtx_geo_two' hs
  have hζH : ¬ IsMVtx 𝔛 (geo 𝔛 α' α 3) := by rw [← isMVtx_iff_of_adj _ hγζ]; exact hγM
  have hηM : IsMVtx 𝔛 (geo 𝔛 α' α 4) := by have := isMVtx_iff_of_adj _ hζη; tauto
  obtain ⟨g, hg, hgε⟩ := exists_mem_stab_smul _ hεγ.symm hγζ
  have hδ₀M : IsMVtx 𝔛 (g • α') := (isMVtx_smul _ g α').mpr hα'M
  have hδ₀ζ : 𝔄 (geo 𝔛 α' α 3) (g • α') := by
    have := (adj_smul _ g _ _).mpr hα'ε.symm
    rwa [hgε] at this
  have hR0 : critR0 𝔛 α α' = Usup 𝔛 (g • α') (geo 𝔛 α' α 3) := by
    rw [← hgε, usup_smul, ← c.critR0_eq hs, map_conj_eq_of_le_centralizer
      (c.critR0_le_centralizer hs) hg]
  have hR0U : critR0 𝔛 α α' ≤ Uloc h.le L (g • α') :=
    hR0 ▸ c.usup_le_uloc hδ₀M hδ₀ζ.symm
  have hR0Z : critR0 𝔛 α α' ≤ ZM 𝔛 (geo 𝔛 α' α 4) :=
    hR0 ▸ (c.usup_le_zh hδ₀M hδ₀ζ.symm).trans (zh_le_zm _ hζη.symm)
  have hβ : 𝔄 α (geo 𝔛 α α' 1) := adj_geo_one _ (by omega)
  have hβη : 𝔄 (geo 𝔛 α α' 1) (geo 𝔛 α α' 2) := adj_geo _ (i := 1) (by omega)
  have hnC : ¬ critR0 𝔛 α α' ≤ stabCenter 𝔛 (geo 𝔛 α' α 4) := by
    intro hC
    have h1 : critR0 𝔛 α α' ≤ Zloc h.le L (geo 𝔛 α' α 4) :=
      (le_inf hR0Z hC).trans (c.zm_inf_stabCenter_le_zloc hηM)
    rw [hηeq] at h1 hηM
    exact c.not_critR0_le_zm hs (h1.trans ((zloc_le_zh h c.full hηM hβη.symm).trans
      (zh_le_zm _ hβ)))
  have hZ := c.concl434 _ _ _ hζH hδ₀ζ hζη fun hle => hnC ((le_inf hR0U hR0Z).trans hle)
  have hR0Uη : critR0 𝔛 α α' ≤ Uloc h.le L (geo 𝔛 α' α 4) := by
    rw [hR0, Usup, zv_of_isMVtx _ hδ₀M, hZ, ← zv_of_isMVtx _ hηM]
    exact c.usup_le_uloc hηM hζη.symm
  have hRZ : critR 𝔛 α α' ≤ Zloc h.le L (geo 𝔛 α' α 4) := by
    have hZαV : ZM 𝔛 α ≤ Vv 𝔛 (geo 𝔛 α' α 4) := by
      rw [← zv_of_isMVtx _ hα]
      refine zv_le_vv h ?_
      rw [hηeq, tdist_comm, dist_geo _ (by omega)]
    have hZα'Q : ZM 𝔛 α' ≤ Qv 𝔛 (geo 𝔛 α' α 4) :=
      zm_le_qv_of_dist_lt _ hα'M (by rw [dist_geo _ (by omega)]; omega)
    exact (Subgroup.commutator_mono hZαV hZα'Q).trans (c.commutator_vv_qv_le_zloc hηM)
  have hbot : critR 𝔛 α α' = ⊥ := by
    rw [eq_bot_iff, ← uloc_inf_zloc h c.full (geo 𝔛 α' α 4)]
    exact le_inf ((critR_le_critR0 h hs).trans hR0Uη) hRZ
  exact ms22_ii _ h.hyp20 h.critDist_pos c.cent hs.1 hbot

end Ctx43

end CFSG.Quasithin.MS93.S4A
