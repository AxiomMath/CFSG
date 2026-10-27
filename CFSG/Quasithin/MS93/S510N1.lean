module

public import CFSG.Quasithin.MS93.S510Stmt
public import CFSG.Quasithin.MS93.S5B512O5
public import CFSG.Quasithin.MS93.S510LX
public import CFSG.Quasithin.MS93.S510R1

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible

namespace S510

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
  {k : ℕ} {F : Type} [Field F] [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

theorem critR_le_xm_of_le_vPre (h : PUHyp M T L) (hb : 2 < critDist (puAmalgam h.le))
    (hd : S5.IsSp4Data M T L k F a) {α' : Vtx (puAmalgam h.le)}
    (hc : IsCritical _ (baseA (puAmalgam h.le)) α')
    (hαβ : geo _ (baseA (puAmalgam h.le)) α' 1 = baseB _) {l : Submodule F (MSP.V4 F)}
    (hl : MSP.IsLine l)
    (hQ : Qv _ (geo _ (baseA (puAmalgam h.le)) α' 2) ≤ S5.vPre h.le a (MSP.qLine l)) :
    critR _ (baseA (puAmalgam h.le)) α' ≤ XM _ (geo _ (baseA (puAmalgam h.le)) α' 2) := by
  have hyp := h.hyp20
  have hb0 := h.critDist_pos
  have hd2 : (puAmalgam h.le).treeGraph.dist (baseA _) α' = critDist (puAmalgam h.le) := hc.2.1
  set γ := geo _ (baseA (puAmalgam h.le)) α' 2 with hγ
  have hα := isMVtx_baseA (puAmalgam h.le)
  have hα' : IsMVtx _ α' := hc.isMVtx_right _ hyp
  have hZγ : ZM _ α' ≤ Qv _ γ := by
    refine zm_le_qv_of_dist_lt _ hα' ?_
    rw [tdist_comm, hγ, dist_geo_right _ (by omega), hd2]
    omega
  have hK := S5B.commutator_uSub_le_centralizer_baseA h hd hl
    (le_rfl : S5.vPre h.le a (MSP.qLine l) ≤ S5.vPre h.le a (MSP.qLine l))
  have hRC : critR _ (baseA (puAmalgam h.le)) α' ≤
      Subgroup.centralizer (Qv _ γ : Set (puAmalgam h.le).Universal) :=
    (S5B.critR_le_commutator_uSub h hb hc hαβ).trans
      ((Subgroup.commutator_mono le_rfl (hZγ.trans hQ)).trans
        (hK.trans (Subgroup.centralizer_le hQ)))
  have hRZ : critR _ (baseA (puAmalgam h.le)) α' ≤ ZM _ (baseA (puAmalgam h.le)) :=
    commutator_le_left_of_le_normalizer
      ((zm_le_stab_of_isCritical _ hyp hb0 hc).trans (stab_le_normalizer_zm _ _))
  have hZQ : ZM _ (baseA (puAmalgam h.le)) ≤ Qv _ γ := by
    refine zm_le_qv_of_dist_lt _ hα ?_
    rw [hγ, dist_geo _ (by omega)]
    omega
  intro r hr
  refine mem_omegaOneCenterOf (hZQ (hRZ hr)) (fun y hy => ?_) ?_
  · exact Subgroup.mem_centralizer_iff.1 (hRC hr) y hy
  · exact sq_eq_one_of_mem_omegaOneCenterOf (zm_le_xm _ hyp hb0 hα (hRZ hr))

namespace IsChain

variable {h : PUHyp M T L} {s t : Vtx (puAmalgam h.le)} {N : ℕ}

theorem qv_le_jOff_prev (h32 : S32) (hX2 : S33.S33X52) (h54 : S54) (h59 : S5B.S59)
    (hmin : PUMin M T L) (hd : S5.IsSp4Data M T L k F a)
    (hch : IsChain h (2 ^ k) a s t N) (hb : 4 < critDist (puAmalgam h.le))
    (hcase : ∀ j ≤ N, S5.jOff h.le L (2 ^ k) (geo _ s t (2 * j + 2)) (geo _ s t (2 * j + 1)) ≠
        S5.jOff h.le L (2 ^ k) (geo _ s t (2 * j)) (geo _ s t (2 * j + 1)) ∨
          ¬ LineCase h (2 ^ k) a)
    (hXU : Xq M ≠ Uq M T L ⊔ Zq M L) {i : ℕ} (hi1 : 1 ≤ i) (hiN : i + 2 ≤ N) :
    Qv _ (geo _ s t (2 * i + 2)) ≤
      S5.jOff h.le L (2 ^ k) (geo _ s t (2 * i)) (geo _ s t (2 * i + 1)) := by
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  have h1 := (hch.second_alt h32 hX2 h54 h59 hmin hd hb hcase hXU (i := i + 1) (by omega)
    (by omega)).2.1
  obtain ⟨c, hc, hcs⟩ := hch.straight (i + 1) (by omega) (by omega)
  have hodd := hch.straight_odd (j := i + 1) (by omega) (by omega) hc hcs
  have e := S5B.jOff_smul h.le hLn (2 ^ k) c (geo _ s t (2 * (i + 1) + 2))
    (geo _ s t (2 * (i + 1) + 1))
  rw [hcs, hodd] at e
  have hq : Qv _ (geo _ s t (2 * (i + 1))) =
      (Qv _ (geo _ s t (2 * (i + 1)))).map (MulAut.conj c).toMonoidHom := by
    rw [← qv_smul, (mem_stab _).1 hc]
  rw [show 2 * (i + 1) - 2 = 2 * i by omega, show 2 * (i + 1) - 1 = 2 * i + 1 by omega] at e
  rw [show 2 * i + 2 = 2 * (i + 1) by ring, hq, e, map_conj_le_map_conj_iff]
  exact h1

theorem critR_le_xm (h32 : S32) (hX2 : S33.S33X52) (h54 : S54) (h59 : S5B.S59)
    (hmin : PUMin M T L) (hd : S5.IsSp4Data M T L k F a)
    (hch : IsChain h (2 ^ k) a s t N) (hb : 4 < critDist (puAmalgam h.le))
    (hcase : ∀ j ≤ N, S5.jOff h.le L (2 ^ k) (geo _ s t (2 * j + 2)) (geo _ s t (2 * j + 1)) ≠
        S5.jOff h.le L (2 ^ k) (geo _ s t (2 * j)) (geo _ s t (2 * j + 1)) ∨
          ¬ LineCase h (2 ^ k) a)
    (hXU : Xq M ≠ Uq M T L ⊔ Zq M L) (hlc : LineCase h (2 ^ k) a) {i : ℕ} (hi1 : 1 ≤ i)
    (hiN : i + 2 ≤ N) :
    critR _ (geo _ s t (2 * i)) (geo _ s t (2 * i + critDist (puAmalgam h.le))) ≤
      XM _ (geo _ s t (2 * i + 2)) := by
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  have hdd := hch.dist_eq
  have hQJ := hch.qv_le_jOff_prev h32 hX2 h54 h59 hmin hd hb hcase hXU hi1 hiN
  obtain ⟨l, hl, -, hJl⟩ := hlc
  obtain ⟨g, hg0, hg1, -⟩ := hch.lam i hi1 (by omega)
  have hcr := hch.crit i (by omega)
  have hg2 := hch.geo_eq (i := 2 * i) (j := 2 * i + critDist (puAmalgam h.le)) (m := 2)
    (by omega) (by omega) (by omega)
  have hg1' := hch.geo_eq (i := 2 * i) (j := 2 * i + critDist (puAmalgam h.le)) (m := 1)
    (by omega) (by omega) (by omega)
  set b := critDist (puAmalgam h.le) with hbdef
  set P := geo _ s t with hP
  have e0 : baseA (puAmalgam h.le) = g⁻¹ • P (2 * i) := by rw [hg0, inv_smul_smul]
  have hc' : IsCritical _ (baseA (puAmalgam h.le)) (g⁻¹ • P (2 * i + b)) := by
    have := (isCritical_smul _ g⁻¹ _ _).2 hcr
    rwa [← e0] at this
  have hgeo : ∀ j, geo _ (baseA (puAmalgam h.le)) (g⁻¹ • P (2 * i + b)) j =
      g⁻¹ • geo _ (P (2 * i)) (P (2 * i + b)) j := by
    intro j
    rw [e0, geo_smul]
  have hβ' : geo _ (baseA (puAmalgam h.le)) (g⁻¹ • P (2 * i + b)) 1 = baseB _ := by
    rw [hgeo, hg1', hg1, inv_smul_smul]
  have hδ : geo _ (baseA (puAmalgam h.le)) (g⁻¹ • P (2 * i + b)) 2 = g⁻¹ • P (2 * i + 2) := by
    rw [hgeo, hg2]
  have hJ : S5.jOff h.le L (2 ^ k) (P (2 * i)) (P (2 * i + 1)) =
      (S5.jOff h.le L (2 ^ k) (baseA _) (baseB _)).map (MulAut.conj g).toMonoidHom := by
    rw [hg0, hg1, S5B.jOff_smul h.le hLn]
  have hQ : Qv _ (geo _ (baseA (puAmalgam h.le)) (g⁻¹ • P (2 * i + b)) 2) ≤
      S5.vPre h.le a (MSP.qLine l) := by
    refine le_trans ?_ hJl
    have e2 : P (2 * i + 2) = g • (g⁻¹ • P (2 * i + 2)) := (smul_inv_smul g _).symm
    rw [hJ, e2, qv_smul, map_conj_le_map_conj_iff] at hQJ
    rw [hδ]
    exact hQJ
  have key := critR_le_xm_of_le_vPre h (by omega) hd hc' hβ' hl hQ
  rw [hδ] at key
  have e1 : P (2 * i + b) = g • (g⁻¹ • P (2 * i + b)) := (smul_inv_smul g _).symm
  have e2 : P (2 * i + 2) = g • (g⁻¹ • P (2 * i + 2)) := (smul_inv_smul g _).symm
  rw [e1, e2, hg0, critR_smul, xm_smul, map_conj_le_map_conj_iff]
  exact key

end IsChain

end S510

namespace S5B

@[expose] def S510NXZ' : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L),
    PUMin M T L → 4 < critDist (puAmalgam h.le) →
    ∀ (k : ℕ) (F : Type) (_ : Field F) (_ : Fintype F) (a : ↥M →* ↥(StatedSp 2 F)),
      S5.IsSp4Data M T L k F a → Xq M ≠ Uq M T L ⊔ Zq M L → S510.LineCase h (2 ^ k) a →
      (2 ^ k) ^ 2 ≤ (Qv _ (baseA (puAmalgam h.le))).relIndex
        (S5.jOff h.le L (2 ^ k) (baseA _) (baseB _)) →
      ∀ α' : Vtx (puAmalgam h.le), IsCritical _ (baseA _) α' → geo _ (baseA _) α' 1 = baseB _ →
      (∀ N : ℕ, ∃ s, geo _ s α' (2 * N) = baseA (puAmalgam h.le) ∧
        S510.IsChain h (2 ^ k) a s α' N ∧
        (∀ j ≤ N, S5.jOff h.le L (2 ^ k) (geo _ s α' (2 * j + 2)) (geo _ s α' (2 * j + 1)) ≠
          S5.jOff h.le L (2 ^ k) (geo _ s α' (2 * j)) (geo _ s α' (2 * j + 1))) ∧
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
            (2 ^ k) ^ 2) ∧
        (∀ i, 1 ≤ i → i + 2 ≤ N →
          Qv _ (geo _ s α' (2 * i + 2)) ≤
            S5.jOff h.le L (2 ^ k) (geo _ s α' (2 * i)) (geo _ s α' (2 * i + 1)) ∧
          critR _ (geo _ s α' (2 * i)) (geo _ s α' (2 * i + critDist (puAmalgam h.le))) ≤
            XM _ (geo _ s α' (2 * i + 2)))) →
      False

theorem s510nxz_of (h32 : S32) (hX2 : S33.S33X52) (h52 : S52) (h54 : S54) (h55 : S55) (h56 : S56)
    (h59 : S59) (h' : S510NXZ') : S510NXZ := by
  intro G _ _ M T L h hmin hb k F _ _ a hd hXU α' hc hαβ
  by_contra hno
  push Not at hno
  have hyp := h.hyp20
  have hb0 := h.critDist_pos
  have hcc : S5.jOff h.le L (2 ^ k) (geo _ (baseA (puAmalgam h.le)) α' 2) (baseB _) ≠
      S5.jOff h.le L (2 ^ k) (baseA (puAmalgam h.le)) (baseB _) ∨
        ¬ S510.LineCase h (2 ^ k) a := by
    by_contra hcon
    push Not at hcon
    obtain ⟨l, hl⟩ := (S510.exists_case56_iff h (2 ^ k) a _).2 hcon
    exact hno l hl
  have hchain : ∀ N : ℕ, ∃ s, geo _ s α' (2 * N) = baseA (puAmalgam h.le) ∧
      S510.IsChain h (2 ^ k) a s α' N ∧
      ∀ j ≤ N, S5.jOff h.le L (2 ^ k) (geo _ s α' (2 * j + 2)) (geo _ s α' (2 * j + 1)) ≠
          S5.jOff h.le L (2 ^ k) (geo _ s α' (2 * j)) (geo _ s α' (2 * j + 1)) ∨
        ¬ S510.LineCase h (2 ^ k) a := by
    intro N
    obtain ⟨s, hsα, hch⟩ := S510.exists_isChain h32 hX2 h52 h54 h55 h56 h59 h hmin hb hd hc N
    have hdd := hch.dist_eq
    have htop : ∀ i ≤ critDist (puAmalgam h.le),
        geo _ s α' (2 * N + i) = geo _ (baseA (puAmalgam h.le)) α' i := by
      intro i hi
      have h1 := hch.geo_eq (i := 2 * N) (j := critDist (puAmalgam h.le) + 2 * N) (m := i)
        (by omega) le_rfl (by omega)
      rw [hsα, ← hdd, geo_dist] at h1
      exact h1.symm
    have hN : S5.jOff h.le L (2 ^ k) (geo _ s α' (2 * N + 2)) (geo _ s α' (2 * N + 1)) ≠
        S5.jOff h.le L (2 ^ k) (geo _ s α' (2 * N)) (geo _ s α' (2 * N + 1)) ∨
          ¬ S510.LineCase h (2 ^ k) a := by
      rw [htop 2 (by omega), htop 1 (by omega), hsα, hαβ]
      exact hcc
    exact ⟨s, hsα, hch, hch.case_prop hN⟩
  obtain ⟨hlc, hJq⟩ : S510.LineCase h (2 ^ k) a ∧ (2 ^ k) ^ 2 ≤
      (Qv _ (baseA (puAmalgam h.le))).relIndex (S5.jOff h.le L (2 ^ k) (baseA _) (baseB _)) := by
    obtain ⟨s, -, hch, hcase⟩ := hchain 2
    have hdd := hch.dist_eq
    have hρ0 : IsMVtx _ (geo _ s α' (2 * 0)) := hch.isMVtx_P (by omega)
    have hadj0 : (puAmalgam h.le).treeGraph.Adj (geo _ s α' (2 * 0)) (geo _ s α' (2 * 0 + 1)) :=
      hch.adj_P (by omega)
    have hE0 : ZM _ (geo _ s α' (2 * 0 + critDist (puAmalgam h.le))) ≤
        Qv _ (geo _ s α' (2 * 0 + 1)) :=
      zm_le_qv_of_dist_lt _ ((hch.crit 0 (by omega)).isMVtx_right _ hyp)
        (by rw [tdist_comm, hch.dist_P (by omega) (by omega)]; omega)
    have hrel0 := hch.partA hd hb hcase (j := 0) (by omega)
    have hRT0 : ⁅S5.uSub h.le L (geo _ s α' (2 * 0)),
          ZM _ (geo _ s α' (2 * 0 + critDist (puAmalgam h.le)))⁆ ⊓
        Subgroup.centralizer (Qv _ (geo _ s α' (2 * 0 + 1)) : Set (puAmalgam h.le).Universal) ≤
        Subgroup.centralizer
          (puTrans h.le L (geo _ s α' (2 * 0)) : Set (puAmalgam h.le).Universal) := by
      refine (hch.p2 hb hcase (j := 0) (by omega)).trans fun z hz => ?_
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact S510.commute_of_mem_stabCenter hz (puTrans_le_stab h.le L _ hy)
    exact S510.line54_of h54 h hmin (by omega) hd hρ0 hadj0 hE0 hrel0 hRT0
  refine h' G M T L h hmin hb k F _ _ a hd hXU hlc hJq α' hc hαβ fun N => ?_
  obtain ⟨s, hsα, hch, hcase⟩ := hchain N
  refine ⟨s, hsα, hch, fun j hj => (hcase j hj).resolve_right (not_not.2 hlc),
    fun i hi1 hiN => hch.second_alt h32 hX2 h54 h59 hmin hd hb hcase hXU hi1 hiN,
    fun i hi1 hiN => ⟨hch.qv_le_jOff_prev h32 hX2 h54 h59 hmin hd hb hcase hXU hi1 hiN,
      hch.critR_le_xm h32 hX2 h54 h59 hmin hd hb hcase hXU hlc hi1 hiN⟩⟩

end S5B

end CFSG.Quasithin.MS93
