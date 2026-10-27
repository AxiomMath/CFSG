module

public import CFSG.Quasithin.MS93.S4ABasic

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Pointwise

section Counting

variable {G : Type*} [Group G]

theorem relIndex_mul_card_inf (H K : Subgroup G) :
    H.relIndex K * Nat.card ↥(H ⊓ K) = Nat.card ↥K := by
  rw [← Subgroup.subgroupOf_map_subtype, Subgroup.card_map_of_injective K.subtype_injective,
    mul_comm]
  exact (H.subgroupOf K).card_mul_index

theorem le_normalizer_of_le_centralizer {H N : Subgroup G}
    (h : H ≤ Subgroup.centralizer (N : Set G)) : H ≤ Subgroup.normalizer (N : Set G) :=
  h.trans (Subgroup.centralizer_le_normalizer _)

theorem mem_centralizer_sup_iff {H K : Subgroup G} {x : G} :
    x ∈ Subgroup.centralizer ((H ⊔ K : Subgroup G) : Set G) ↔
      x ∈ Subgroup.centralizer (H : Set G) ∧ x ∈ Subgroup.centralizer (K : Set G) := by
  constructor
  · intro hx
    exact ⟨Subgroup.centralizer_le (fun y hy => le_sup_left (a := H) hy) hx,
      Subgroup.centralizer_le (fun y hy => le_sup_right (b := K) hy) hx⟩
  · rintro ⟨hH, hK⟩
    have hle : H ⊔ K ≤ Subgroup.centralizer ({x} : Set G) := by
      refine sup_le (fun y hy => ?_) (fun y hy => ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_iff.mp hH y hy)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_iff.mp hK y hy)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hy))

theorem card_sup_of_commute {H K : Subgroup G} (hc : K ≤ Subgroup.centralizer (H : Set G))
    (hHK : H ⊓ K = ⊥) : Nat.card ↥(H ⊔ K) = Nat.card ↥H * Nat.card ↥K := by
  have hHN : H ≤ Subgroup.normalizer (K : Set G) :=
    le_normalizer_of_le_centralizer (Subgroup.le_centralizer_iff.mp hc)
  have hset : ((H ⊔ K : Subgroup G) : Set G) = (H : Set G) * (K : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right H K hHN
  let f : ↥H × ↥K → ↥(H ⊔ K) := fun p => ⟨(p.1 : G) * p.2,
    Subgroup.mul_mem _ (le_sup_left (a := H) p.1.2) (le_sup_right (b := K) p.2.2)⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨a, b⟩ ⟨a', b'⟩ hab
      have hab' : (a : G) * b = a' * b' := congrArg Subtype.val hab
      have h1 : (a' : G)⁻¹ * a = b' * (b : G)⁻¹ := by
        calc (a' : G)⁻¹ * a = (a' : G)⁻¹ * (a * b) * (b : G)⁻¹ := by group
          _ = (a' : G)⁻¹ * (a' * b') * (b : G)⁻¹ := by rw [hab']
          _ = b' * (b : G)⁻¹ := by group
      have hmem : (a' : G)⁻¹ * a ∈ H ⊓ K :=
        ⟨H.mul_mem (H.inv_mem a'.2) a.2, h1 ▸ K.mul_mem b'.2 (K.inv_mem b.2)⟩
      rw [hHK, Subgroup.mem_bot] at hmem
      have ha : a = a' := Subtype.ext (by
        have := congrArg (fun y => (a' : G) * y) hmem
        simpa using this)
      have hb : b = b' := Subtype.ext (by
        rw [ha] at hab'
        exact mul_left_cancel hab')
      rw [ha, hb]
    · rintro ⟨x, hx⟩
      have hx' : x ∈ (H : Set G) * (K : Set G) := hset ▸ hx
      obtain ⟨a, ha, b, hb, rfl⟩ := hx'
      exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
  rw [← Nat.card_prod, Nat.card_congr (Equiv.ofBijective f hf)]

theorem relIndex_sup_eq_of_le {U W Q : Subgroup G} [Finite ↥U] [Finite ↥W] (hWQ : W ≤ Q)
    (hc : W ≤ Subgroup.centralizer (U : Set G)) (hUW : U ⊓ W = ⊥) :
    Q.relIndex (U ⊔ W) = Q.relIndex U := by
  have hUN : U ≤ Subgroup.normalizer (W : Set G) :=
    le_normalizer_of_le_centralizer (Subgroup.le_centralizer_iff.mp hc)
  have hset : ((U ⊔ W : Subgroup G) : Set G) = (U : Set G) * (W : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right U W hUN
  have hinf : Q ⊓ (U ⊔ W) = (Q ⊓ U) ⊔ W := by
    apply le_antisymm
    · rintro x ⟨hxQ, hxUW⟩
      have hx' : x ∈ (U : Set G) * (W : Set G) := hset ▸ hxUW
      obtain ⟨u, hu, w, hw, rfl⟩ := hx'
      have huQ : u ∈ Q := by
        have := Q.mul_mem hxQ (Q.inv_mem (hWQ hw))
        simpa using this
      exact Subgroup.mul_mem _ (le_sup_left (a := Q ⊓ U) ⟨huQ, hu⟩) (le_sup_right (b := W) hw)
    · exact sup_le (inf_le_inf_left _ le_sup_left) (le_inf hWQ le_sup_right)
  have h1 := relIndex_mul_card_inf Q (U ⊔ W)
  have h2 := relIndex_mul_card_inf Q U
  rw [hinf, card_sup_of_commute (hc.trans (Subgroup.centralizer_le inf_le_right))
    (by rw [eq_bot_iff]; exact (inf_le_inf_right _ inf_le_right).trans hUW.le),
    card_sup_of_commute hc hUW] at h1
  have : Finite ↥(Q ⊓ U) := Finite.of_injective _ (Subgroup.inclusion_injective inf_le_right)
  have hpos : 0 < Nat.card ↥(Q ⊓ U) * Nat.card ↥W := Nat.mul_pos Nat.card_pos Nat.card_pos
  rw [← h2] at h1
  exact Nat.eq_of_mul_eq_mul_right hpos (by simpa only [mul_assoc] using h1)

end Counting

section CritGeneral

universe u v

variable {A B : Type u} {C : Type v} [Group A] [Group C] [Group B] (X : GoldAmalgam A C B)

theorem zm_le_qv_geo_one_left (h : Hyp20 X) (hb : 0 < critDist X) (hC : CentHyp X)
    {α α' : Vtx X} (hc : IsCritical X α α') : ZM X α ≤ Qv X (geo X α' α 1) :=
  zm_le_qv_geo_one X h hb (ms22_iii X h hb hC hc)

theorem zm_le_stab_right (h : Hyp20 X) (hb : 0 < critDist X) (hC : CentHyp X)
    {α α' : Vtx X} (hc : IsCritical X α α') : ZM X α ≤ stab X α' :=
  (zm_le_qv_geo_one_left X h hb hC hc).trans
    (qv_le_stab_of_adj X (adj_geo_one_of_isCritical X hb (ms22_iii X h hb hC hc)).symm)

theorem zm_inf_centralizer_eq_inf_qv (h : Hyp20 X) (hb : 0 < critDist X) (hC : CentHyp X)
    {α α' : Vtx X} (hc : IsCritical X α α') :
    ZM X α ⊓ Subgroup.centralizer (ZM X α' : Set X.Universal) = ZM X α ⊓ Qv X α' := by
  have hc' := ms22_iii X h hb hC hc
  have hα' : IsMVtx X α' := hc'.1
  apply le_antisymm
  · intro x ⟨hxZ, hxC⟩
    refine ⟨hxZ, ?_⟩
    have hadj := adj_geo_one_of_isCritical X hb hc'
    rw [← hC α' _ hα' hadj]
    exact ⟨zm_le_qv_geo_one_left X h hb hC hc hxZ, hxC⟩
  · exact inf_le_inf_left _ (Subgroup.le_centralizer_iff.mp (zm_le_centralizer_qv X h hα'))

end CritGeneral

section CritSL3

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
  (hfull : IsSL3Full M T L)
include h hfull

theorem mem_centralizer_zm_iff {δ : Vtx (puAmalgam h.le)} (hδ : IsMVtx _ δ)
    {x : (puAmalgam h.le).Universal} (hx : x ∈ stab _ δ) :
    x ∈ Subgroup.centralizer (ZM _ δ : Set (puAmalgam h.le).Universal) ↔
      x ∈ Subgroup.centralizer (Uloc h.le L δ : Set (puAmalgam h.le).Universal) := by
  constructor
  · exact fun hxc => Subgroup.centralizer_le (uloc_le_zm h hfull hδ) hxc
  · intro hxc
    rw [zm_eq_uloc_sup_zloc h hfull hδ, mem_centralizer_sup_iff]
    refine ⟨hxc, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact (Subgroup.mem_centralizer_iff.mp (zloc_le_centralizer_stab h hfull hδ hz) x hx).symm

theorem commutator_zm_eq_uloc {δ : Vtx (puAmalgam h.le)} (hδ : IsMVtx _ δ)
    {K : Subgroup (puAmalgam h.le).Universal} (hK : K ≤ stab _ δ) :
    ⁅ZM _ δ, K⁆ = ⁅Uloc h.le L δ, K⁆ := by
  apply le_antisymm
  · rw [zm_eq_uloc_sup_zloc h hfull hδ]
    have hUK : ⁅Uloc h.le L δ, K⁆ ≤ Uloc h.le L δ :=
      Subgroup.le_normalizer_iff_commutator_le_left.mp
        (hK.trans (stab_le_normalizer_puTrans h.le (S4A.Uq_normal h) δ))
    have hZab : ZM _ δ ≤ Subgroup.centralizer (ZM (puAmalgam h.le) δ : Set _) :=
      (Subgroup.le_centralizer_iff_isMulCommutative).mpr
        (isElemAbelian_zm _ h.hyp20 h.critDist_pos hδ).1
    have hUab : Uloc h.le L δ ≤ Subgroup.centralizer (Uloc h.le L δ : Set _) :=
      (uloc_le_zm h hfull hδ).trans (hZab.trans (Subgroup.centralizer_le
        (uloc_le_zm h hfull hδ)))
    have hZc : Zloc h.le L δ ≤ Subgroup.centralizer (stab (puAmalgam h.le) δ : Set _) :=
      zloc_le_centralizer_stab h hfull hδ
    refine S4A.commutator_sup_le_of le_rfl ?_ ?_ ?_
    · rw [(Subgroup.commutator_eq_bot_iff_le_centralizer).mpr
        (hZc.trans (Subgroup.centralizer_le hK))]
      exact bot_le
    · exact le_normalizer_of_le_centralizer (Subgroup.le_centralizer_iff.mp
        (hUK.trans hUab))
    · exact le_normalizer_of_le_centralizer (hZc.trans (Subgroup.centralizer_le
        (fun x hx => (hUK.trans (puTrans_le_stab h.le _ δ)) hx)))
  · exact Subgroup.commutator_mono (uloc_le_zm h hfull hδ) le_rfl

theorem zloc_le_zh {α β : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α)
    (hαβ : (puAmalgam h.le).treeGraph.Adj α β) : Zloc h.le L α ≤ ZH _ β := by
  intro x hx
  have hxZ := zloc_le_zm h hfull hα hx
  have hxQ : x ∈ Qv _ β :=
    qv_le_qv _ h.hyp20 hα hαβ (zm_le_qv_self _ hα h.critDist_pos hxZ)
  have hxc : x ∈ Subgroup.centralizer (Qv (puAmalgam h.le) β : Set _) :=
    Subgroup.centralizer_le (qv_le_stab_of_adj _ hαβ.symm)
      (zloc_le_centralizer_stab h hfull hα hx)
  have hx2 : x ^ 2 = 1 :=
    (isElemAbelian_zm _ h.hyp20 h.critDist_pos hα).2 x hxZ
  exact Subgroup.subset_closure ⟨⟨hxQ, hxc⟩, hx2⟩

theorem zloc_le_qv_of_isCritical {α α' : Vtx (puAmalgam h.le)}
    (hc : IsCritical (puAmalgam h.le) α α') : Zloc h.le L α ≤ Qv _ α' := by
  have hb := h.critDist_pos
  have hd : (puAmalgam h.le).treeGraph.dist α α' = critDist _ := hc.2.1
  have hb2 := two_le_critDist _ h.hyp20 hb
  have h12 : (puAmalgam h.le).treeGraph.Adj (geo _ α α' 1) (geo _ α α' 2) :=
    adj_geo _ (i := 1) (by omega)
  refine (zloc_le_zh h hfull hc.1 (adj_geo_one_of_isCritical _ hb hc)).trans
    ((zh_le_zm _ h12.symm).trans ?_)
  refine zm_le_qv_of_dist_lt _ (isMVtx_geo_two _ h.hyp20 hb hc) ?_
  rw [dist_geo_right _ (by omega)]
  omega

theorem relIndex_zm_eq_uloc {α α' : Vtx (puAmalgam h.le)}
    (hc : IsCritical (puAmalgam h.le) α α') :
    (Qv _ α').relIndex (ZM _ α) = (Qv _ α').relIndex (Uloc h.le L α) := by
  have hβ := adj_geo_one_of_isCritical _ h.critDist_pos hc
  have hfin : Finite ↥(Qv (puAmalgam h.le) (geo _ α α' 1)) :=
    finite_qv _ h.hyp20 (by rw [← isMVtx_iff_of_adj _ hβ]; exact hc.1)
  have hZQ : ZM (puAmalgam h.le) α ≤ Qv _ (geo _ α α' 1) :=
    qv_le_qv _ h.hyp20 hc.1 hβ |>.trans' (zm_le_qv_self _ hc.1 h.critDist_pos)
  have hfU : Finite ↥(Uloc h.le L α) :=
    Finite.of_injective _ (Subgroup.inclusion_injective ((uloc_le_zm h hfull hc.1).trans hZQ))
  have hfW : Finite ↥(Zloc h.le L α) :=
    Finite.of_injective _ (Subgroup.inclusion_injective ((zloc_le_zm h hfull hc.1).trans hZQ))
  rw [zm_eq_uloc_sup_zloc h hfull hc.1]
  refine relIndex_sup_eq_of_le (zloc_le_qv_of_isCritical h hfull hc) ?_
    (uloc_inf_zloc h hfull α)
  exact (zloc_le_centralizer_stab h hfull hc.1).trans
    (Subgroup.centralizer_le (puTrans_le_stab h.le _ α))

end CritSL3

end CFSG.Quasithin.MS93
