module

public import CFSG.Quasithin.MS93.S510S2E
public import CFSG.Quasithin.MS93.S511B6

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

namespace S511S

@[expose] def CruxNXZ : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L),
    PUMin M T L → 4 < critDist (puAmalgam h.le) →
    ∀ (k : ℕ) (F : Type) (_ : Field F) (_ : Fintype F) (a : ↥M →* ↥(StatedSp 2 F)),
      S5.IsSp4Data M T L k F a → Xq M ≠ Uq M T L ⊔ Zq M L → S510.LineCase h (2 ^ k) a →
      (2 ^ k) ^ 2 ≤ (Qv _ (baseA (puAmalgam h.le))).relIndex
        (S5.jOff h.le L (2 ^ k) (baseA _) (baseB _)) →
      ∀ α' : Vtx (puAmalgam h.le), IsCritical _ (baseA _) α' → geo _ (baseA _) α' 1 = baseB _ →
      ∀ (N : ℕ) (s : Vtx (puAmalgam h.le)), geo _ s α' (2 * N) = baseA (puAmalgam h.le) →
        S510.IsChain h (2 ^ k) a s α' N →
        (∀ j ≤ N, S5.jOff h.le L (2 ^ k) (geo _ s α' (2 * j + 2)) (geo _ s α' (2 * j + 1)) ≠
          S5.jOff h.le L (2 ^ k) (geo _ s α' (2 * j)) (geo _ s α' (2 * j + 1))) →
        (∀ i, 1 ≤ i → i + 1 ≤ N →
          S5.zHat _ (geo _ s α' (2 * i)) (geo _ s α' (2 * i + critDist (puAmalgam h.le))) ≤
            Subgroup.normalizer ((S5.uSub h.le L (geo _ s α' (2 * i - 2)) ⊓
                Subgroup.centralizer
                  (ZM _ (geo _ s α' (2 * i - 2 + critDist (puAmalgam h.le))) : Set _) ⊔
              XM _ (geo _ s α' (2 * i)) : Subgroup _) : Set (puAmalgam h.le).Universal) ∧
          Qv _ (geo _ s α' (2 * i)) ≤
            S5.jOff h.le L (2 ^ k) (geo _ s α' (2 * i + 2)) (geo _ s α' (2 * i + 1)) ∧
          (Qv _ (geo _ s α' (2 * i))).relIndex
              (S5.jOff h.le L (2 ^ k) (geo _ s α' (2 * i + 2)) (geo _ s α' (2 * i + 1)) ⊓
                S5.jOff h.le L (2 ^ k) (geo _ s α' (2 * i)) (geo _ s α' (2 * i + 1))) ≤
            (2 ^ k) ^ 2) →
        (∀ i, 1 ≤ i → i + 2 ≤ N →
          Qv _ (geo _ s α' (2 * i + 2)) ≤
            S5.jOff h.le L (2 ^ k) (geo _ s α' (2 * i)) (geo _ s α' (2 * i + 1)) ∧
          critR _ (geo _ s α' (2 * i)) (geo _ s α' (2 * i + critDist (puAmalgam h.le))) ≤
            XM _ (geo _ s α' (2 * i + 2))) →
        ∀ i, 1 ≤ i → i + 3 ≤ N →
          ⁅ZM _ (geo _ s α' (2 * i)), Qv _ (geo _ s α' (2 * i + 2))⁆ ≤ Subgroup.centralizer
            (ZM _ (geo _ s α' (2 * i + 2 + critDist (puAmalgam h.le))) : Set _)

namespace IsChain

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
  {k : ℕ} {F : Type} [Field F] [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}
  {h : PUHyp M T L} {s t : Vtx (puAmalgam h.le)} {N : ℕ}

theorem false_of_crux (hd : S5.IsSp4Data M T L k F a) (hch : S510.IsChain h (2 ^ k) a s t N)
    (hb : 4 < critDist (puAmalgam h.le))
    (hcase : ∀ j ≤ N, S5.jOff h.le L (2 ^ k) (geo _ s t (2 * j + 2)) (geo _ s t (2 * j + 1)) ≠
        S5.jOff h.le L (2 ^ k) (geo _ s t (2 * j)) (geo _ s t (2 * j + 1)) ∨
          ¬ S510.LineCase h (2 ^ k) a)
    {i : ℕ} (hi1 : 1 ≤ i) (hiN : i + 3 ≤ N)
    (hRX : critR _ (geo _ s t (2 * i)) (geo _ s t (2 * i + critDist (puAmalgam h.le))) ≤
      XM _ (geo _ s t (2 * i + 2)))
    (hW : ⁅ZM _ (geo _ s t (2 * i)), Qv _ (geo _ s t (2 * i + 2))⁆ ≤ Subgroup.centralizer
      (ZM _ (geo _ s t (2 * i + 2 + critDist (puAmalgam h.le))) : Set (puAmalgam h.le).Universal)) :
    False := by
  have hyp := h.hyp20
  have hb0 := h.critDist_pos
  have hdd := hch.dist_eq
  set b := critDist (puAmalgam h.le) with hbdef
  set P := geo _ s t with hP
  have hγM : IsMVtx _ (P (2 * i)) := hch.isMVtx_P (by omega)
  have hγ2M : IsMVtx _ (P (2 * i + 2)) := by
    have := hch.isMVtx_P (j := i + 1) (by omega)
    rwa [show 2 * (i + 1) = 2 * i + 2 by ring] at this
  have hε : ¬ IsMVtx _ (P (2 * i + 1)) := hch.not_isMVtx_P (by omega)
  have hγε : (puAmalgam h.le).treeGraph.Adj (P (2 * i)) (P (2 * i + 1)) := hch.adj_P (by omega)
  have hεγ2 : (puAmalgam h.le).treeGraph.Adj (P (2 * i + 1)) (P (2 * i + 2)) :=
    hch.adj_P (i := 2 * i + 1) (by omega)
  have hcr := hch.crit i (by omega)
  have hcr2 : IsCritical _ (P (2 * i + 2)) (P (2 * i + 2 + b)) := by
    have := hch.crit (i + 1) (by omega)
    rwa [show 2 * (i + 1) = 2 * i + 2 by ring] at this
  have hγ'M : IsMVtx _ (P (2 * i + b)) := hcr.isMVtx_right _ hyp
  have hgen := (hch.facts55 (j := i + 1) (by omega) (by omega) (hcase (i + 1) (by omega))).1
  rw [show 2 * (i + 1) - 1 = 2 * i + 1 by omega, show 2 * (i + 1) = 2 * i + 2 by ring] at hgen
  set W := ⁅ZM _ (P (2 * i)), Qv _ (P (2 * i + 2))⁆ with hWdef
  have hTst : Qv _ (P (2 * i + 1)) ≤ stab _ (P (2 * i)) := qv_le_stab_of_adj _ hγε.symm
  have hTst2 : Qv _ (P (2 * i + 1)) ≤ stab _ (P (2 * i + 2)) := qv_le_stab_of_adj _ hεγ2
  have hWn : Qv _ (P (2 * i + 1)) ≤ Subgroup.normalizer (W : Set (puAmalgam h.le).Universal) :=
    le_normalizer_commutator (hTst.trans (stab_le_normalizer_zm _ _))
      (hTst2.trans (stab_le_normalizer_qv _ _))
  have hCn : Qv _ (P (2 * i + 1)) ≤ Subgroup.normalizer
      (Subgroup.centralizer (W : Set (puAmalgam h.le).Universal) : Set _) :=
    le_normalizer_centralizer hWn
  have hZC : ZM _ (P (2 * i + 2 + b)) ≤
      Subgroup.centralizer (W : Set (puAmalgam h.le).Universal) := by
    rw [Subgroup.le_centralizer_iff]
    exact hW
  have hLle : puTrans h.le L (P (2 * i + 2)) ≤
      Subgroup.centralizer (W : Set (puAmalgam h.le).Universal) ⊔ Qv _ (P (2 * i + 1)) := by
    refine (puTrans_le_stab h.le L _).trans ?_
    rw [← hgen]
    exact sup_le le_sup_right (hZC.trans le_sup_left)
  have := S510S2.finite_puTrans h hγ2M
  have hLC : puTrans h.le L (P (2 * i + 2)) ≤
      Subgroup.centralizer (W : Set (puAmalgam h.le).Universal) :=
    S5.le_of_le_sup_of_isPGroup (S510S2.puTrans_perfect h hγ2M) (isPGroup_qv _ hyp hε) hCn hLle
  have hZ'Q : ZM _ (P (2 * i + b)) ≤ Qv _ (P (2 * i + 2)) := by
    refine zm_le_qv_of_dist_lt _ hγ'M ?_
    rw [tdist_comm, hch.dist_P (by omega) (by omega)]
    omega
  have hRW : critR _ (P (2 * i)) (P (2 * i + b)) ≤ W := Subgroup.commutator_mono le_rfl hZ'Q
  have hRZ : critR _ (P (2 * i)) (P (2 * i + b)) ≤ ZM _ (P (2 * i)) :=
    commutator_le_left_of_le_normalizer
      ((zm_le_stab_of_isCritical _ hyp hb0 hcr).trans (stab_le_normalizer_zm _ _))
  have hRQ : critR _ (P (2 * i)) (P (2 * i + b)) ≤ Qv _ (P (2 * i + 2)) := by
    refine hRZ.trans (zm_le_qv_of_dist_lt _ hγM ?_)
    rw [hch.dist_P (by omega) (by omega)]
    omega
  have hRL : critR _ (P (2 * i)) (P (2 * i + b)) ≤
      Subgroup.centralizer (puTrans h.le L (P (2 * i + 2)) : Set (puAmalgam h.le).Universal) :=
    hRW.trans (Subgroup.le_centralizer_iff.1 hLC)
  have hRZ' : critR _ (P (2 * i)) (P (2 * i + b)) ≤
      Subgroup.centralizer (ZM _ (P (2 * i + 2 + b)) : Set (puAmalgam h.le).Universal) :=
    hRW.trans hW
  have hRD : critR _ (P (2 * i)) (P (2 * i + b)) ≤ S5.dSub h.le L (P (2 * i + 2)) :=
    le_inf hRQ hRL
  have hRc : critR _ (P (2 * i)) (P (2 * i + b)) ≤ stabCenter _ (P (2 * i + 2)) := by
    rcases Nat.lt_or_ge k 2 with hk | hk
    · have hk1 : k = 1 := by have := hd.1; omega
      have hd1 : S5.IsSp4Data M T L 1 F a := hk1 ▸ hd
      have hcr' := ms22_iii _ hyp hb0 h.centHyp hcr2
      obtain ⟨z, hzZ, hzQ⟩ := Set.not_subset.1 hcr'.2.2
      have hz2 : z ^ 2 = 1 := sq_eq_one_of_mem_omegaOneCenterOf
        (zm_le_xm _ hyp hb0 (hcr2.isMVtx_right _ hyp) hzZ)
      have hzst : z ∈ stab _ (P (2 * i + 2)) := zm_le_stab_of_isCritical _ hyp hb0 hcr2 hzZ
      have hpA := hch.partA hd hb hcase (j := i + 1) (by omega)
      rw [show 2 * (i + 1) = 2 * i + 2 by ring, hk1, pow_one] at hpA
      have hCz : Subgroup.centralizer (ZM _ (P (2 * i + 2 + b)) : Set (puAmalgam h.le).Universal) ≤
          Subgroup.centralizer ({z} : Set (puAmalgam h.le).Universal) :=
        Subgroup.centralizer_le (Set.singleton_subset_iff.2 hzZ)
      have hne : (Subgroup.centralizer (ZM _ (P (2 * i + 2 + b)) :
          Set (puAmalgam h.le).Universal)).relIndex (S5.uSub h.le L (P (2 * i + 2))) ≠ 0 := by
        rw [hpA]; norm_num
      have hrel := Subgroup.relIndex_le_of_le_left hCz hne
      rw [hpA] at hrel
      have hR3 : critR _ (P (2 * i)) (P (2 * i + b)) ≤ XM _ (P (2 * i + 2)) ⊓
          S5.dSub h.le L (P (2 * i + 2)) ⊓
            Subgroup.centralizer ({z} : Set (puAmalgam h.le).Universal) :=
        le_inf (le_inf hRX hRD) (hRZ'.trans hCz)
      exact hR3.trans (S5Q2.xm_inf_dSub_inf_centralizer_le_of_mem h hd1 hγ2M hzst hz2 hzQ hrel)
    · have hR2 : critR _ (P (2 * i)) (P (2 * i + b)) ≤ XM _ (P (2 * i + 2)) ⊓
          Subgroup.centralizer (puTrans h.le L (P (2 * i + 2)) : Set (puAmalgam h.le).Universal) :=
        le_inf hRX hRL
      exact hR2.trans
        (S5Q2.xm_inf_centralizer_le_stabCenter h (S5Q2.zq_le_centralizer_of_two_le h hd hk) hγ2M)
  have hRT : critR _ (P (2 * i)) (P (2 * i + b)) ≤
      Subgroup.centralizer (Qv _ (P (2 * i + 1)) : Set (puAmalgam h.le).Universal) := by
    intro r hr
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact S510.commute_of_mem_stabCenter (hRc hr) (hTst2 hy)
  have hp2 := hch.p2 hb hcase (j := i) (by omega)
  have hR0 : critR _ (P (2 * i)) (P (2 * i + b)) ≤ stabCenter _ (P (2 * i)) :=
    (le_inf (S510S2.critR_le_commutator_uSub_gp h (by omega) hcr) hRT).trans hp2
  exact S511.critR_not_le_stabCenter h hd hcr hR0

end IsChain

theorem s510NXZ'_of_crux (hcr : CruxNXZ) : S5B.S510NXZ' := by
  intro G _ _ M T L h hmin hb k F _ _ a hd hXU hlc hJq α' hc hαβ hchain
  obtain ⟨s, hsα, hch, hcase, h2, h3⟩ := hchain 4
  exact IsChain.false_of_crux hd hch hb (fun j hj => Or.inl (hcase j hj)) le_rfl le_rfl
    (h3 1 le_rfl (by omega)).2
    (hcr G M T L h hmin hb k F _ _ a hd hXU hlc hJq α' hc hαβ 4 s hsα hch hcase h2 h3 1 le_rfl
      le_rfl)

end S511S

end CFSG.Quasithin.MS93
