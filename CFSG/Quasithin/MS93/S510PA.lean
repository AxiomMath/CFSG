module

public import CFSG.Quasithin.MS93.S510Chain
public import CFSG.Quasithin.MS93.S510Tv

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible

namespace S510

section General

universe u v

variable {A B : Type u} {C : Type v} [Group A] [Group C] [Group B] {X : GoldAmalgam A C B}

theorem zm_le_centralizer_zm (hyp : Hyp20 X) (hb : 0 < critDist X) {α : Vtx X}
    (hα : IsMVtx X α) : ZM X α ≤ Subgroup.centralizer (ZM X α : Set X.Universal) :=
  (zm_le_qv_self X hα hb).trans ((qv_le_centralizer_xm X α).trans
    (Subgroup.centralizer_le (zm_le_xm X hyp hb hα)))

theorem commutator_le_zm_of_le_stab {α' : Vtx X} {Y : Subgroup X.Universal}
    (hY : Y ≤ stab X α') : ⁅Y, ZM X α'⁆ ≤ ZM X α' := by
  rw [Subgroup.commutator_comm]
  exact Subgroup.le_normalizer_iff_commutator_le_left.1 (hY.trans (stab_le_normalizer_zm X α'))

end General

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
  {k : ℕ} {F : Type} [Field F] {a : ↥M →* ↥(StatedSp 2 F)}

theorem stab_le_normalizer_uSub (h : PUHyp M T L) (δ : Vtx (puAmalgam h.le)) :
    stab _ δ ≤ Subgroup.normalizer (S5.uSub h.le L δ : Set (puAmalgam h.le).Universal) := by
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  exact stab_le_normalizer_of_smul _ (F := fun ρ => S5.uSub h.le L ρ)
    (fun g ρ => S5B.uSub_smul h.le hLn g ρ) δ

namespace IsChain

variable {h : PUHyp M T L} {q : ℕ} {s t : Vtx (puAmalgam h.le)} {N : ℕ}

theorem p2 (hch : IsChain h q a s t N) (hb : 4 < critDist (puAmalgam h.le))
    (hcase : ∀ j ≤ N, S5.jOff h.le L q (geo _ s t (2 * j + 2)) (geo _ s t (2 * j + 1)) ≠
        S5.jOff h.le L q (geo _ s t (2 * j)) (geo _ s t (2 * j + 1)) ∨ ¬ LineCase h q a)
    {j : ℕ} (hj : j + 2 ≤ N) :
    ⁅S5.uSub h.le L (geo _ s t (2 * j)), ZM _ (geo _ s t (2 * j + critDist (puAmalgam h.le)))⁆ ⊓
        Subgroup.centralizer (Qv _ (geo _ s t (2 * j + 1)) : Set (puAmalgam h.le).Universal) ≤
      stabCenter _ (geo _ s t (2 * j)) := by
  have hd := hch.dist_eq
  have hyp := h.hyp20
  have hb0 := h.critDist_pos
  set b := critDist (puAmalgam h.le) with hbdef
  set P := geo _ s t with hP
  have hγM : IsMVtx _ (P (2 * j)) := hch.isMVtx_P (by omega)
  have hg1 := (hch.facts55 (j := j + 1) (by omega) (by omega) (hcase (j + 1) (by omega))).1
  have hg2 := (hch.facts55 (j := j + 2) (by omega) (by omega) (hcase (j + 2) (by omega))).1
  rw [show 2 * (j + 1) - 1 = 2 * j + 1 by omega, show 2 * (j + 1) = 2 * j + 2 by ring,
    show 2 * j + 2 + b = (2 * j + b) + 2 by ring] at hg1
  rw [show 2 * (j + 2) - 1 = 2 * j + 3 by omega, show 2 * (j + 2) = 2 * j + 4 by ring,
    show 2 * j + 4 + b = (2 * j + b) + 4 by ring] at hg2
  have hγ'M : IsMVtx _ (P (2 * j + b)) := (hch.crit j (by omega)).isMVtx_right _ hyp
  have hUγ' : S5.uSub h.le L (P (2 * j)) ≤ stab _ (P (2 * j + b)) :=
    (S5B.uSub_le_zm h.le _).trans (zm_le_stab_of_isCritical _ hyp hb0
      (ms22_iii _ hyp hb0 h.centHyp (hch.crit j (by omega))))
  have hRZ : ⁅S5.uSub h.le L (P (2 * j)), ZM _ (P (2 * j + b))⁆ ≤ ZM _ (P (2 * j + b)) :=
    commutator_le_zm_of_le_stab hUγ'
  have hZcen : ∀ i, 1 ≤ i → i ≤ 2 → ZM _ (P (2 * j + b + 2 * i)) ≤
      Subgroup.centralizer (ZM _ (P (2 * j + b)) : Set (puAmalgam h.le).Universal) := by
    intro i hi1 hi2
    have hMi : IsMVtx _ (P (2 * (j + i) + b)) := by
      have := (hch.crit (j + i) (by omega)).isMVtx_right _ hyp
      exact this
    refine (zm_le_qv_of_dist_lt _ (by rwa [show 2 * j + b + 2 * i = 2 * (j + i) + b by ring])
      ?_).trans ((qv_le_centralizer_xm _ _).trans (Subgroup.centralizer_le
        (zm_le_xm _ hyp hb0 hγ'M)))
    rw [tdist_comm, hch.dist_P (by omega) (by omega)]
    omega
  intro w ⟨hwR, hwT⟩
  have hwZ' : w ∈ ZM _ (P (2 * j + b)) := hRZ hwR
  have hwU : w ∈ S5.uSub h.le L (P (2 * j)) :=
    commutator_le_left_of_le_normalizer ((zm_le_stab_of_isCritical _ hyp hb0
      (hch.crit j (by omega))).trans (stab_le_normalizer_uSub h _)) hwR
  have hwZγ : w ∈ ZM _ (P (2 * j)) := S5B.uSub_le_zm h.le _ hwU
  have hZγ1 : ZM _ (P (2 * j)) ≤ Qv _ (P (2 * j + 1)) :=
    zm_le_qv_of_dist_lt _ hγM (by rw [hch.dist_P (by omega) (by omega)]; omega)
  have hZγ3 : ZM _ (P (2 * j)) ≤ Qv _ (P (2 * j + 3)) :=
    zm_le_qv_of_dist_lt _ hγM (by rw [hch.dist_P (by omega) (by omega)]; omega)
  have hst1 : Qv _ (P (2 * j + 1)) ≤ stab _ (P (2 * j + 2)) :=
    qv_le_stab_of_adj _ (hch.adj_P (i := 2 * j + 1) (by omega))
  have hst3 : Qv _ (P (2 * j + 3)) ≤ stab _ (P (2 * j + 2)) :=
    qv_le_stab_of_adj _ (hch.adj_P (i := 2 * j + 2) (by omega)).symm
  have hst3' : Qv _ (P (2 * j + 3)) ≤ stab _ (P (2 * j + 4)) :=
    qv_le_stab_of_adj _ (hch.adj_P (i := 2 * j + 3) (by omega))
  have hc2 : stab _ (P (2 * j + 2)) ≤
      Subgroup.centralizer ({w} : Set (puAmalgam h.le).Universal) := by
    rw [← hg1]
    refine sup_le (fun y hy => ?_) (fun y hy => ?_)
    · exact Subgroup.mem_centralizer_singleton_iff.2 ((Subgroup.mem_centralizer_iff.1 hwT) y hy)
    · have := (Subgroup.mem_centralizer_iff.1 (hZcen 1 le_rfl (by norm_num) hy)) w hwZ'
      exact Subgroup.mem_centralizer_singleton_iff.2 this.symm
  have hc4 : stab _ (P (2 * j + 4)) ≤
      Subgroup.centralizer ({w} : Set (puAmalgam h.le).Universal) := by
    rw [← hg2]
    refine sup_le (hst3.trans hc2) (fun y hy => ?_)
    have := (Subgroup.mem_centralizer_iff.1 (hZcen 2 (by norm_num) le_rfl
      (by rwa [show 2 * j + b + 2 * 2 = 2 * j + b + 4 by ring]))) w hwZ'
    exact Subgroup.mem_centralizer_singleton_iff.2 this.symm
  obtain ⟨c, hc, hc4j⟩ := hch.straight (j + 1) (by omega) (by omega)
  rw [show 2 * (j + 1) = 2 * j + 2 by ring, show 2 * j + 2 + 2 = 2 * j + 4 by ring,
    show 2 * j + 2 - 2 = 2 * j by omega] at hc4j
  rw [show 2 * (j + 1) = 2 * j + 2 by ring] at hc
  rw [← hP] at hc hc4j
  have hwst : w ∈ stab _ (P (2 * j)) :=
    (zm_le_qv_self _ hγM hb0).trans (qv_le_stab _ _) hwZγ
  rw [mem_stabCenter_iff]
  refine ⟨hwst, fun y hy => ?_⟩
  have hy' : c⁻¹ * y * c ∈ stab _ (P (2 * j + 4)) := by
    rw [← hc4j, mem_stab_smul] at hy
    exact hy
  have h1 : c⁻¹ * y * c * w = w * (c⁻¹ * y * c) :=
    (Subgroup.mem_centralizer_singleton_iff.1 (hc4 hy'))
  have h2 : c * w = w * c := Subgroup.mem_centralizer_singleton_iff.1 (hc2 hc)
  calc y * w = c * (c⁻¹ * y * c * w) * c⁻¹ := by
        rw [show c⁻¹ * y * c * w = c⁻¹ * y * (c * w) by group, h2]; group
    _ = c * (w * (c⁻¹ * y * c)) * c⁻¹ := by rw [h1]
    _ = w * y := by
        rw [show c * (w * (c⁻¹ * y * c)) * c⁻¹ = c * w * c⁻¹ * y by group, h2]; group

theorem partA [Fintype F] (hd : S5.IsSp4Data M T L k F a) (hch : IsChain h (2 ^ k) a s t N)
    (hb : 4 < critDist (puAmalgam h.le))
    (hcase : ∀ j ≤ N, S5.jOff h.le L (2 ^ k) (geo _ s t (2 * j + 2)) (geo _ s t (2 * j + 1)) ≠
        S5.jOff h.le L (2 ^ k) (geo _ s t (2 * j)) (geo _ s t (2 * j + 1)) ∨
          ¬ LineCase h (2 ^ k) a)
    {j : ℕ} (hj : j + 2 ≤ N) :
    (Subgroup.centralizer (ZM _ (geo _ s t (2 * j + critDist (puAmalgam h.le))) :
        Set (puAmalgam h.le).Universal)).relIndex (S5.uSub h.le L (geo _ s t (2 * j))) = 2 ^ k := by
  have hdd := hch.dist_eq
  have hyp := h.hyp20
  have hb0 := h.critDist_pos
  have hcr := hch.crit j (by omega)
  have hcr' := ms22_iii _ hyp hb0 h.centHyp hcr
  have hγM : IsMVtx _ (geo _ s t (2 * j)) := hch.isMVtx_P (by omega)
  have hγ'M : IsMVtx _ (geo _ s t (2 * j + critDist (puAmalgam h.le))) := hcr.isMVtx_right _ hyp
  have hE : ZM _ (geo _ s t (2 * j + critDist (puAmalgam h.le))) ≤ Qv _ (geo _ s t (2 * j + 1)) :=
    zm_le_qv_of_dist_lt _ hγ'M (by rw [tdist_comm, hch.dist_P (by omega) (by omega)]; omega)
  have hUγ' : S5.uSub h.le L (geo _ s t (2 * j)) ≤
      stab _ (geo _ s t (2 * j + critDist (puAmalgam h.le))) :=
    (S5B.uSub_le_zm h.le _).trans (zm_le_stab_of_isCritical _ hyp hb0 hcr')
  refine relIndex_eq_of_comm h hd hγM (hch.adj_P (by omega)) hE hcr'.2.2 ?_ ?_
  · exact (commutator_le_zm_of_le_stab hUγ').trans (zm_le_centralizer_zm hyp hb0 hγ'M)
  · refine (hch.p2 hb hcase hj).trans ?_
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact commute_of_mem_stabCenter hz (puTrans_le_stab h.le L _ hy)

end IsChain

end S510

end CFSG.Quasithin.MS93
