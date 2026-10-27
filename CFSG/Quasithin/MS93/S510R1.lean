module

public import CFSG.Quasithin.MS93.S510Ctr
public import CFSG.Quasithin.MS93.S510Gp
public import CFSG.Quasithin.MS93.S510PA

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

namespace S510

theorem le_normalizer_sup_of_commutator_le {Γ : Type*} [Group Γ] {Z Y X : Subgroup Γ}
    (hZX : Z ≤ Subgroup.normalizer (X : Set Γ)) (hZY : ⁅Z, Y⁆ ≤ Y ⊔ X) :
    Z ≤ Subgroup.normalizer ((Y ⊔ X : Subgroup Γ) : Set Γ) := by
  refine le_normalizer_of_map_conj_le fun z hz => ?_
  rw [Subgroup.map_sup, map_conj_eq_of_mem_normalizer (hZX hz)]
  refine sup_le ?_ le_sup_right
  rintro _ ⟨y, hy, rfl⟩
  have hc : z * y * z⁻¹ * y⁻¹ ∈ Y ⊔ X := hZY (by
    have := Subgroup.commutator_mem_commutator hz hy
    rwa [commutatorElement_def] at this)
  have e : (MulAut.conj z).toMonoidHom y = (z * y * z⁻¹ * y⁻¹) * y := by
    simp [MulAut.conj_apply]
  rw [e]
  exact mul_mem hc (Subgroup.mem_sup_left hy)

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
  {k : ℕ} {F : Type} [Field F] {a : ↥M →* ↥(StatedSp 2 F)}

theorem xm_eq_uSub_sup_centralizer (h : PUHyp M T L) (hXU : Xq M = Uq M T L ⊔ Zq M L)
    {γ : Vtx (puAmalgam h.le)} (hγ : IsMVtx _ γ) :
    XM _ γ = S5.uSub h.le L γ ⊔ XM _ γ ⊓
      Subgroup.centralizer (puTrans h.le L γ : Set (puAmalgam h.le).Universal) := by
  have hn : ∀ {N : Subgroup G}, N ≤ M → M ≤ Subgroup.normalizer (N : Set G) →
      (N.subgroupOf M).Normal := fun hN hNn =>
    (Subgroup.normal_subgroupOf_iff_le_normalizer hN).2 hNn
  have hU := le_normalizer_Uq (T := T) h.le_normalizer
  have hZ := le_normalizer_Zq h.le_normalizer
  have hsup : puTrans h.le (Uq M T L ⊔ Zq M L) γ =
      puTrans h.le (Uq M T L) γ ⊔ puTrans h.le (Zq M L) γ := by
    obtain ⟨g, rfl⟩ := exists_eq_smul_baseA _ hγ
    rw [puTrans_smul_baseA (hn (sup_le (Uq_le h.L_le) Zq_le) (le_normalizer_sup hU hZ)),
      puTrans_smul_baseA (hn (Uq_le h.L_le) hU), puTrans_smul_baseA (hn Zq_le hZ),
      S5B.imM_sup_of_le h.le (Uq_le h.L_le) Zq_le, Subgroup.map_sup]
  rw [← h.puTrans_Zq hγ, S5.uSub, ← h.puTrans_Uq hγ, ← hsup, ← hXU, h.xm_eq hγ]

namespace IsChain

variable {h : PUHyp M T L} {s t : Vtx (puAmalgam h.le)} {N : ℕ}

theorem not_le_normalizer_of_first (h32 : S32) (h54 : S54) (h59 : S5B.S59)
    (hmin : PUMin M T L) [Fintype F] (hd : S5.IsSp4Data M T L k F a)
    (hch : IsChain h (2 ^ k) a s t N) (hb : 4 < critDist (puAmalgam h.le))
    (hcase : ∀ j ≤ N, S5.jOff h.le L (2 ^ k) (geo _ s t (2 * j + 2)) (geo _ s t (2 * j + 1)) ≠
        S5.jOff h.le L (2 ^ k) (geo _ s t (2 * j)) (geo _ s t (2 * j + 1)) ∨
          ¬ LineCase h (2 ^ k) a)
    {i : ℕ} (hi1 : 1 ≤ i) (hiN : i + 1 ≤ N)
    (hL : puTrans h.le L (geo _ s t (2 * i)) ≤
        S5.jOff h.le L (2 ^ k) (geo _ s t (2 * i - 2)) (geo _ s t (2 * i - 1)) ⊔
          S5.zHat _ (geo _ s t (2 * i)) (geo _ s t (2 * i + critDist (puAmalgam h.le)))) :
    ¬ S5.zHat _ (geo _ s t (2 * i)) (geo _ s t (2 * i + critDist (puAmalgam h.le))) ≤
      Subgroup.normalizer ((S5.uSub h.le L (geo _ s t (2 * i - 2)) ⊓
          Subgroup.centralizer
            (ZM _ (geo _ s t (2 * i - 2 + critDist (puAmalgam h.le))) : Set _) ⊔
        XM _ (geo _ s t (2 * i)) : Subgroup _) : Set (puAmalgam h.le).Universal) := by
  have hdd := hch.dist_eq
  have hyp := h.hyp20
  have hb0 := h.critDist_pos
  set b := critDist (puAmalgam h.le) with hbdef
  set P := geo _ s t with hP
  have hb2 : 2 < b := by omega
  have h32' := (h32 G M T L h).2.1
  have hγM : IsMVtx _ (P (2 * i)) := hch.isMVtx_P (by omega)
  have hμM : IsMVtx _ (P (2 * i - 2)) := by
    have := hch.isMVtx_P (j := i - 1) (by omega)
    rwa [show 2 * (i - 1) = 2 * i - 2 by omega] at this
  have hcr : IsCritical _ (P (2 * i)) (P (2 * i + b)) := hch.crit i (by omega)
  have hcr0 : IsCritical _ (P (2 * i - 2)) (P (2 * i - 2 + b)) := by
    have := hch.crit (i - 1) (by omega)
    rwa [show 2 * (i - 1) = 2 * i - 2 by omega] at this
  have hμ'M : IsMVtx _ (P (2 * i - 2 + b)) := hcr0.isMVtx_right _ hyp
  have hrel := hch.partA hd hb hcase (j := i - 1) (by omega)
  rw [show 2 * (i - 1) = 2 * i - 2 by omega] at hrel
  set Y := S5.uSub h.le L (P (2 * i - 2)) ⊓
    Subgroup.centralizer (ZM _ (P (2 * i - 2 + b)) : Set (puAmalgam h.le).Universal) with hY
  have hadjμ : (puAmalgam h.le).treeGraph.Adj (P (2 * i - 2)) (P (2 * i - 1)) := by
    have := hch.adj_P (i := 2 * i - 2) (by omega)
    rwa [show 2 * i - 2 + 1 = 2 * i - 1 by omega] at this
  have hadjγ : (puAmalgam h.le).treeGraph.Adj (P (2 * i - 1)) (P (2 * i)) := by
    have := hch.adj_P (i := 2 * i - 1) (by omega)
    rwa [show 2 * i - 1 + 1 = 2 * i by omega] at this
  have hEμ : ZM _ (P (2 * i - 2 + b)) ≤ Qv _ (P (2 * i - 1)) :=
    zm_le_qv_of_dist_lt _ hμ'M (by rw [tdist_comm, hch.dist_P (by omega) (by omega)]; omega)
  have hdγμ : (puAmalgam h.le).treeGraph.dist (P (2 * i)) (P (2 * i - 2)) = 2 := by
    rw [tdist_comm, hch.dist_P (by omega) (by omega)]
    omega
  have hJY := jOff_le_normalizer_of_relIndex h hmin hb2 hd h54 hμM hadjμ hEμ hrel
  have hJX : S5.jOff h.le L (2 ^ k) (P (2 * i - 2)) (P (2 * i - 1)) ≤
      Subgroup.normalizer (XM _ (P (2 * i)) : Set (puAmalgam h.le).Universal) :=
    (S5B.jOff_le_qv h.le L _ _ _).trans ((qv_le_stab_of_adj _ hadjγ).trans
      (stab_le_normalizer_xm _ _))
  have hJ := le_normalizer_sup hJY hJX
  have hB : 2 ^ k < (S5.bSub h.le L (P (2 * i))).relIndex (S5.uSub h.le L (P (2 * i - 2))) := by
    have h1 := s59_gp h59 h hmin hb hd hcr
    have hg2 : geo _ (P (2 * i)) (P (2 * i + b)) 2 = P (2 * i + 2) :=
      hch.geo_eq (by omega) (by omega) (by omega)
    obtain ⟨c, hc, hcs⟩ := hch.straight i hi1 (by omega)
    rw [hg2, ← relIndex_bSub_uSub_conj h hc, ← hP, hcs] at h1
    exact h1
  intro hZ
  have hn := hL.trans (sup_le hJ hZ)
  have hYZ : Y ≤ ZM _ (P (2 * i - 2)) := inf_le_left.trans (S5B.uSub_le_zm h.le _)
  have hYB := S5B.le_bSub_of_xm h hb2 h32' hγM hdγμ (hYZ.trans (zm_le_xm _ hyp hb0 hμM))
    (hYZ.trans (S5B.zm_le_vv_of_dist hμM hdγμ.le)) hn
  have hle : (S5.bSub h.le L (P (2 * i))).relIndex (S5.uSub h.le L (P (2 * i - 2))) ≤ 2 ^ k := by
    rw [← hrel, ← Subgroup.inf_relIndex_right, ← Subgroup.inf_relIndex_right
      (Subgroup.centralizer _), inf_comm (Subgroup.centralizer _)]
    refine Subgroup.relIndex_le_of_le_left (le_inf hYB inf_le_left) ?_
    rw [inf_comm, Subgroup.inf_relIndex_right, hrel]
    positivity
  omega

theorem s33_of_not_le_normalizer (h32 : S32) (hX2 : S33.S33X52) [Fintype F]
    (hd : S5.IsSp4Data M T L k F a)
    (hch : IsChain h (2 ^ k) a s t N) (hb : 4 < critDist (puAmalgam h.le))
    {i : ℕ} (hi1 : 1 ≤ i) (hiN : i + 1 ≤ N)
    (hnorm : ¬ S5.zHat _ (geo _ s t (2 * i)) (geo _ s t (2 * i + critDist (puAmalgam h.le))) ≤
      Subgroup.normalizer ((S5.uSub h.le L (geo _ s t (2 * i - 2)) ⊓
          Subgroup.centralizer
            (ZM _ (geo _ s t (2 * i - 2 + critDist (puAmalgam h.le))) : Set _) ⊔
        XM _ (geo _ s t (2 * i)) : Subgroup _) : Set (puAmalgam h.le).Universal)) :
    (Qv _ (geo _ s t (2 * i + critDist (puAmalgam h.le)))).relIndex
        (ZM _ (geo _ s t (2 * i))) = 2 ^ k ∧
      Xq M = Uq M T L ⊔ Zq M L ∧
      Nat.card ↥⁅S5.uSub h.le L (geo _ s t (2 * i - 2)) ⊓
          Subgroup.centralizer
            (ZM _ (geo _ s t (2 * i - 2 + critDist (puAmalgam h.le))) : Set _),
          critA _ (geo _ s t (2 * i)) (geo _ s t (2 * i + critDist (puAmalgam h.le)))⁆ = 2 ^ k ∧
      ⁅S5.uSub h.le L (geo _ s t (2 * i - 2)) ⊓
          Subgroup.centralizer
            (ZM _ (geo _ s t (2 * i - 2 + critDist (puAmalgam h.le))) : Set _),
          critA _ (geo _ s t (2 * i)) (geo _ s t (2 * i + critDist (puAmalgam h.le)))⁆ ≤
        critR _ (geo _ s t (2 * i)) (geo _ s t (2 * i + critDist (puAmalgam h.le))) ⊔
          stabCenter _ (geo _ s t (2 * i + critDist (puAmalgam h.le))) := by
  have hdd := hch.dist_eq
  have hyp := h.hyp20
  have hb0 := h.critDist_pos
  have hC := h.centHyp
  set b := critDist (puAmalgam h.le) with hbdef
  set P := geo _ s t with hP
  have hb2 : 2 < b := by omega
  have hγM : IsMVtx _ (P (2 * i)) := hch.isMVtx_P (by omega)
  have hμM : IsMVtx _ (P (2 * i - 2)) := by
    have := hch.isMVtx_P (j := i - 1) (by omega)
    rwa [show 2 * (i - 1) = 2 * i - 2 by omega] at this
  have hcr : IsCritical _ (P (2 * i)) (P (2 * i + b)) := hch.crit i (by omega)
  have hcr0 : IsCritical _ (P (2 * i - 2)) (P (2 * i - 2 + b)) := by
    have := hch.crit (i - 1) (by omega)
    rwa [show 2 * (i - 1) = 2 * i - 2 by omega] at this
  have hγ'M : IsMVtx _ (P (2 * i + b)) := hcr.isMVtx_right _ hyp
  have hμ'M : IsMVtx _ (P (2 * i - 2 + b)) := hcr0.isMVtx_right _ hyp
  have hcr' := ms22_iii _ hyp hb0 hC hcr
  set Y := S5.uSub h.le L (P (2 * i - 2)) ⊓
    Subgroup.centralizer (ZM _ (P (2 * i - 2 + b)) : Set (puAmalgam h.le).Universal) with hY
  set A := critA _ (P (2 * i)) (P (2 * i + b)) with hA
  have hadjμ : (puAmalgam h.le).treeGraph.Adj (P (2 * i - 2)) (P (2 * i - 1)) := by
    have := hch.adj_P (i := 2 * i - 2) (by omega)
    rwa [show 2 * i - 2 + 1 = 2 * i - 1 by omega] at this
  have hadjγ : (puAmalgam h.le).treeGraph.Adj (P (2 * i - 1)) (P (2 * i)) := by
    have := hch.adj_P (i := 2 * i - 1) (by omega)
    rwa [show 2 * i - 1 + 1 = 2 * i by omega] at this
  have hdγμ : (puAmalgam h.le).treeGraph.dist (P (2 * i)) (P (2 * i - 2)) = 2 := by
    rw [tdist_comm, hch.dist_P (by omega) (by omega)]
    omega
  have hX'st : XM _ (P (2 * i + b)) ≤ stab _ (P (2 * i)) :=
    xm_le_stab_of_isCritical _ hyp hb0 hC hcr'
  have hZγ'st : ZM _ (P (2 * i + b)) ≤ stab _ (P (2 * i)) :=
    (zm_le_xm _ hyp hb0 hγ'M).trans hX'st
  have hYT : Y ≤ Qv _ (geo _ (P (2 * i + b)) (P (2 * i)) 1) := by
    have hg : geo _ (P (2 * i + b)) (P (2 * i)) 1 = P (2 * i + b - 1) := by
      rw [hch.geo_eq' (by omega) (by omega) (by omega)]
    rw [hg]
    have hadj' : (puAmalgam h.le).treeGraph.Adj (P (2 * i - 2 + b)) (P (2 * i + b - 1)) := by
      have := hch.adj_P (i := 2 * i - 2 + b) (by omega)
      rwa [show 2 * i - 2 + b + 1 = 2 * i + b - 1 by omega] at this
    have hadj'' : (puAmalgam h.le).treeGraph.Adj (P (2 * i - 2 + b)) (P (2 * i + b - 3)) := by
      have := hch.adj_P (i := 2 * i + b - 3) (by omega)
      rw [show 2 * i + b - 3 + 1 = 2 * i - 2 + b by omega] at this
      exact this.symm
    have hZμ : ZM _ (P (2 * i - 2)) ≤ Qv _ (P (2 * i + b - 3)) :=
      zm_le_qv_of_dist_lt _ hμM (by rw [hch.dist_P (by omega) (by omega)]; omega)
    have hYQ : Y ≤ Qv _ (P (2 * i - 2 + b)) :=
      le_qv_of_le_centralizer _ hC hμ'M hadj''
        (inf_le_left.trans ((S5B.uSub_le_zm h.le _).trans hZμ)) inf_le_right
    exact hYQ.trans (qv_le_qv _ hyp hμ'M hadj')
  have hRZ : critR _ (P (2 * i)) (P (2 * i + b)) ≤ ZM _ (P (2 * i)) :=
    commutator_le_left_of_le_normalizer (hZγ'st.trans (stab_le_normalizer_zm _ _))
  have hYZγ : Y ≤ Subgroup.centralizer (ZM _ (P (2 * i)) : Set (puAmalgam h.le).Universal) :=
    inf_le_left.trans ((S5B.uSub_le_zm h.le _).trans
      (zm_le_centralizer_zm_of_dist hyp hb0 hμM hγM (by rw [tdist_comm, hdγμ]; omega)))
  have hYR : Y ≤ Subgroup.centralizer (critR _ (P (2 * i)) (P (2 * i + b)) :
      Set (puAmalgam h.le).Universal) := hYZγ.trans (Subgroup.centralizer_le hRZ)
  have hAQ : A ≤ Qv _ (P (2 * i - 1)) :=
    inf_le_right.trans (qv_le_qv _ hyp hγM hadjγ.symm)
  have hAZ : A ≤ Subgroup.centralizer
      (ZM _ (P (2 * i - 2 + b)) : Set (puAmalgam h.le).Universal) := by
    have hZQ : ZM _ (P (2 * i - 2 + b)) ≤ Qv _ (P (2 * i + b)) :=
      zm_le_qv_of_dist_lt _ hμ'M (by rw [hch.dist_P (by omega) (by omega)]; omega)
    rw [Subgroup.le_centralizer_iff]
    exact hZQ.trans ((qv_le_centralizer_xm _ _).trans (Subgroup.centralizer_le inf_le_left))
  have hAU : A ≤ Subgroup.normalizer (S5.uSub h.le L (P (2 * i - 2)) :
      Set (puAmalgam h.le).Universal) :=
    hAQ.trans ((qv_le_stab_of_adj _ hadjμ.symm).trans (stab_le_normalizer_uSub h _))
  have hAY : A ≤ Subgroup.normalizer (Y : Set (puAmalgam h.le).Universal) := by
    refine le_normalizer_of_map_conj_le fun x hx => ?_
    rw [Subgroup.map_inf _ _ _ (MulAut.conj x).injective, map_conj_eq_of_mem_normalizer (hAU hx),
      map_conj_eq_of_mem_normalizer (Subgroup.le_normalizer (hAZ hx))]
  have hAYle : ⁅A, Y⁆ ≤ Y := by
    rw [Subgroup.commutator_comm]
    exact commutator_le_left_of_le_normalizer hAY
  have hXX : ⁅XM (puAmalgam h.le) (P (2 * i)), XM (puAmalgam h.le) (P (2 * i + b))⁆ ≤
      XM _ (P (2 * i)) :=
    commutator_le_left_of_le_normalizer (hX'st.trans (stab_le_normalizer_xm _ _))
  have hZXst : ZM _ (P (2 * i + b)) ≤
      Subgroup.normalizer (XM _ (P (2 * i)) : Set (puAmalgam h.le).Universal) :=
    hZγ'st.trans (stab_le_normalizer_xm _ _)
  have hZh : S5.zHat _ (P (2 * i)) (P (2 * i + b)) ≤ ZM _ (P (2 * i + b)) := inf_le_left
  have hY3 : ¬ ⁅ZM (puAmalgam h.le) (P (2 * i + b)), Y⁆ ≤
      ⁅XM (puAmalgam h.le) (P (2 * i)), XM (puAmalgam h.le) (P (2 * i + b))⁆ ⊔ ⁅A, Y⁆ := by
    intro hle
    refine hnorm (hZh.trans (le_normalizer_sup_of_commutator_le hZXst ?_))
    exact hle.trans (sup_le (hXX.trans le_sup_right) (hAYle.trans le_sup_left))
  have hYZh : ¬ ⁅Y, S5.zHat _ (P (2 * i)) (P (2 * i + b))⁆ ≤
      critR _ (P (2 * i)) (P (2 * i + b)) := by
    intro hle
    refine hnorm (le_normalizer_sup_of_commutator_le (hZh.trans hZXst) ?_)
    rw [Subgroup.commutator_comm]
    exact hle.trans ((hRZ.trans (zm_le_xm _ hyp hb0 hγM)).trans le_sup_right)
  have hYX : Y ≤ Subgroup.centralizer (XM _ (P (2 * i)) : Set (puAmalgam h.le).Universal) :=
    inf_le_left.trans ((S5B.uSub_le_zm h.le _).trans ((zm_le_qv_of_dist_lt _ hμM
      (by rw [hch.dist_P (by omega) (by omega)]; omega)).trans (qv_le_centralizer_xm _ _)))
  obtain ⟨hidx, hXU, h4⟩ := s33ii2_gp hX2 h hd (h32 G M T L h).2.1 hcr hYT hYR hYX hY3 hYZh
  have hYab : ⁅⁅A, Y⁆, Y⁆ = ⊥ := by
    rw [← le_bot_iff]
    refine (Subgroup.commutator_mono hAYle le_rfl).trans (le_of_eq ?_)
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact inf_le_left.trans ((S5B.uSub_le_zm h.le _).trans
      ((zm_le_centralizer_zm hyp hb0 hμM).trans (Subgroup.centralizer_le
        (inf_le_left.trans (S5B.uSub_le_zm h.le _)))))
  exact ⟨hidx, hXU, h4 hYab⟩

theorem r1_facts (h32 : S32) (hX2 : S33.S33X52) (h54 : S54) (h59 : S5B.S59)
    (hmin : PUMin M T L) [Fintype F] (hd : S5.IsSp4Data M T L k F a)
    (hch : IsChain h (2 ^ k) a s t N) (hb : 4 < critDist (puAmalgam h.le))
    (hcase : ∀ j ≤ N, S5.jOff h.le L (2 ^ k) (geo _ s t (2 * j + 2)) (geo _ s t (2 * j + 1)) ≠
        S5.jOff h.le L (2 ^ k) (geo _ s t (2 * j)) (geo _ s t (2 * j + 1)) ∨
          ¬ LineCase h (2 ^ k) a)
    (hXU : Xq M = Uq M T L ⊔ Zq M L) {i : ℕ} (hi1 : 1 ≤ i) (hiN : i + 1 ≤ N) :
    puTrans h.le L (geo _ s t (2 * i)) ≤
        S5.jOff h.le L (2 ^ k) (geo _ s t (2 * i - 2)) (geo _ s t (2 * i - 1)) ⊔
          S5.zHat _ (geo _ s t (2 * i)) (geo _ s t (2 * i + critDist (puAmalgam h.le))) ∧
      (Qv _ (geo _ s t (2 * i + critDist (puAmalgam h.le)))).relIndex
          (ZM _ (geo _ s t (2 * i))) = 2 ^ k ∧
      Nat.card ↥⁅S5.uSub h.le L (geo _ s t (2 * i - 2)) ⊓
          Subgroup.centralizer
            (ZM _ (geo _ s t (2 * i - 2 + critDist (puAmalgam h.le))) : Set _),
          critA _ (geo _ s t (2 * i)) (geo _ s t (2 * i + critDist (puAmalgam h.le)))⁆ = 2 ^ k ∧
      ⁅S5.uSub h.le L (geo _ s t (2 * i - 2)) ⊓
          Subgroup.centralizer
            (ZM _ (geo _ s t (2 * i - 2 + critDist (puAmalgam h.le))) : Set _),
          critA _ (geo _ s t (2 * i)) (geo _ s t (2 * i + critDist (puAmalgam h.le)))⁆ ≤
        critR _ (geo _ s t (2 * i)) (geo _ s t (2 * i + critDist (puAmalgam h.le))) ⊔
          stabCenter _ (geo _ s t (2 * i + critDist (puAmalgam h.le))) := by
  have hγM : IsMVtx _ (geo _ s t (2 * i)) := hch.isMVtx_P (by omega)
  have hL : puTrans h.le L (geo _ s t (2 * i)) ≤
      S5.jOff h.le L (2 ^ k) (geo _ s t (2 * i - 2)) (geo _ s t (2 * i - 1)) ⊔
        S5.zHat _ (geo _ s t (2 * i)) (geo _ s t (2 * i + critDist (puAmalgam h.le))) := by
    rcases (hch.facts55 hi1 (by omega) (hcase i (by omega))).2.2 with h1 | ⟨-, -, h3⟩
    · exact h1
    · exact absurd (xm_eq_uSub_sup_centralizer h hXU hγM) h3
  obtain ⟨hidx, -, h4⟩ := hch.s33_of_not_le_normalizer h32 hX2 hd hb hi1 hiN
    (hch.not_le_normalizer_of_first h32 h54 h59 hmin hd hb hcase hi1 hiN hL)
  exact ⟨hL, hidx, h4⟩

theorem second_alt (h32 : S32) (hX2 : S33.S33X52) (h54 : S54) (h59 : S5B.S59)
    (hmin : PUMin M T L) [Fintype F] (hd : S5.IsSp4Data M T L k F a)
    (hch : IsChain h (2 ^ k) a s t N) (hb : 4 < critDist (puAmalgam h.le))
    (hcase : ∀ j ≤ N, S5.jOff h.le L (2 ^ k) (geo _ s t (2 * j + 2)) (geo _ s t (2 * j + 1)) ≠
        S5.jOff h.le L (2 ^ k) (geo _ s t (2 * j)) (geo _ s t (2 * j + 1)) ∨
          ¬ LineCase h (2 ^ k) a)
    (hXU : Xq M ≠ Uq M T L ⊔ Zq M L) {i : ℕ} (hi1 : 1 ≤ i) (hiN : i + 1 ≤ N) :
    S5.zHat _ (geo _ s t (2 * i)) (geo _ s t (2 * i + critDist (puAmalgam h.le))) ≤
        Subgroup.normalizer ((S5.uSub h.le L (geo _ s t (2 * i - 2)) ⊓
            Subgroup.centralizer
              (ZM _ (geo _ s t (2 * i - 2 + critDist (puAmalgam h.le))) : Set _) ⊔
          XM _ (geo _ s t (2 * i)) : Subgroup _) : Set (puAmalgam h.le).Universal) ∧
      Qv _ (geo _ s t (2 * i)) ≤
        S5.jOff h.le L (2 ^ k) (geo _ s t (2 * i + 2)) (geo _ s t (2 * i + 1)) ∧
      (Qv _ (geo _ s t (2 * i))).relIndex
          (S5.jOff h.le L (2 ^ k) (geo _ s t (2 * i + 2)) (geo _ s t (2 * i + 1)) ⊓
            S5.jOff h.le L (2 ^ k) (geo _ s t (2 * i)) (geo _ s t (2 * i + 1))) ≤ (2 ^ k) ^ 2 := by
  have hn : S5.zHat _ (geo _ s t (2 * i)) (geo _ s t (2 * i + critDist (puAmalgam h.le))) ≤
      Subgroup.normalizer ((S5.uSub h.le L (geo _ s t (2 * i - 2)) ⊓
          Subgroup.centralizer
            (ZM _ (geo _ s t (2 * i - 2 + critDist (puAmalgam h.le))) : Set _) ⊔
        XM _ (geo _ s t (2 * i)) : Subgroup _) : Set (puAmalgam h.le).Universal) := by
    by_contra hnorm
    exact hXU (hch.s33_of_not_le_normalizer h32 hX2 hd hb hi1 hiN hnorm).2.1
  refine ⟨hn, ?_⟩
  rcases (hch.facts55 hi1 (by omega) (hcase i (by omega))).2.2 with h1 | ⟨h2, h3, -⟩
  · exact absurd hn (hch.not_le_normalizer_of_first h32 h54 h59 hmin hd hb hcase hi1 hiN h1)
  · exact ⟨h2, h3⟩

end IsChain

end S510

end CFSG.Quasithin.MS93
