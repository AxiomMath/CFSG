module

public import CFSG.Quasithin.MS93.S5CPath
public import CFSG.Quasithin.MS93.S511SNXZ
public import CFSG.Quasithin.MS93.S511SSt1

public section

namespace CFSG.Quasithin.MS93.S5C

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

namespace IsChain

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
  {k : ℕ} {F : Type} [Field F] [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}
  {h : PUHyp M T L} {s t : Vtx (puAmalgam h.le)} {N : ℕ}

theorem false_of_conf (h32 : S32) (hd : S5.IsSp4Data M T L k F a)
    (hch : S510.IsChain h (2 ^ k) a s t N) (hb : 4 < critDist (puAmalgam h.le))
    (hcase : ∀ j ≤ N, S5.jOff h.le L (2 ^ k) (geo _ s t (2 * j + 2)) (geo _ s t (2 * j + 1)) ≠
      S5.jOff h.le L (2 ^ k) (geo _ s t (2 * j)) (geo _ s t (2 * j + 1)))
    (hlc : S510.LineCase h (2 ^ k) a)
    (hJq : (2 ^ k) ^ 2 ≤ (Qv _ (baseA (puAmalgam h.le))).relIndex
      (S5.jOff h.le L (2 ^ k) (baseA _) (baseB _)))
    {i : ℕ} (hi1 : 1 ≤ i) (hiN : i + 3 ≤ N)
    (hQJ : Qv _ (geo _ s t (2 * i)) ≤
      S5.jOff h.le L (2 ^ k) (geo _ s t (2 * i + 2)) (geo _ s t (2 * i + 1)))
    (hQJ' : Qv _ (geo _ s t (2 * i + 2)) ≤
      S5.jOff h.le L (2 ^ k) (geo _ s t (2 * i)) (geo _ s t (2 * i + 1)))
    (hRX : critR _ (geo _ s t (2 * i)) (geo _ s t (2 * i + critDist (puAmalgam h.le))) ≤
      XM _ (geo _ s t (2 * i + 2)))
    (hR : 2 ≤ k ∨ critR _ (geo _ s t (2 * i)) (geo _ s t (2 * i + critDist (puAmalgam h.le))) ≤
      S5.uSub h.le L (geo _ s t (2 * i + 2)) ⊔ (XM _ (geo _ s t (2 * i + 2)) ⊓
        Subgroup.centralizer (puTrans h.le L (geo _ s t (2 * i + 2)) :
          Set (puAmalgam h.le).Universal))) : False := by
  have hyp := h.hyp20
  have hb0 := h.critDist_pos
  have hdd := hch.dist_eq
  have hLn := h.L_subgroupOf_normal
  have hcase' : ∀ j ≤ N,
      S5.jOff h.le L (2 ^ k) (geo _ s t (2 * j + 2)) (geo _ s t (2 * j + 1)) ≠
        S5.jOff h.le L (2 ^ k) (geo _ s t (2 * j)) (geo _ s t (2 * j + 1)) ∨
          ¬ S510.LineCase h (2 ^ k) a := fun j hj => Or.inl (hcase j hj)
  set b := critDist (puAmalgam h.le) with hbdef
  set P := geo _ s t with hP
  obtain ⟨l, hl, hTl, hJl⟩ := hlc
  have hγM : IsMVtx _ (P (2 * i)) := hch.isMVtx_P (by omega)
  have hγ2M : IsMVtx _ (P (2 * i + 2)) := by
    have := hch.isMVtx_P (j := i + 1) (by omega)
    rwa [show 2 * (i + 1) = 2 * i + 2 by ring] at this
  have hγ4M : IsMVtx _ (P (2 * i + 4)) := by
    have := hch.isMVtx_P (j := i + 2) (by omega)
    rwa [show 2 * (i + 2) = 2 * i + 4 by ring] at this
  have hε : ¬ IsMVtx _ (P (2 * i + 1)) := hch.not_isMVtx_P (by omega)
  have hε3 : ¬ IsMVtx _ (P (2 * i + 3)) := by
    have := hch.not_isMVtx_P (j := i + 1) (by omega)
    rwa [show 2 * (i + 1) + 1 = 2 * i + 3 by ring] at this
  have hγε : (puAmalgam h.le).treeGraph.Adj (P (2 * i)) (P (2 * i + 1)) := hch.adj_P (by omega)
  have hεγ2 : (puAmalgam h.le).treeGraph.Adj (P (2 * i + 1)) (P (2 * i + 2)) :=
    hch.adj_P (i := 2 * i + 1) (by omega)
  have hγ2ε3 : (puAmalgam h.le).treeGraph.Adj (P (2 * i + 2)) (P (2 * i + 3)) :=
    hch.adj_P (i := 2 * i + 2) (by omega)
  have hε3γ4 : (puAmalgam h.le).treeGraph.Adj (P (2 * i + 3)) (P (2 * i + 4)) :=
    hch.adj_P (i := 2 * i + 3) (by omega)
  have hcr := hch.crit i (by omega)
  have hcr2 : IsCritical _ (P (2 * i + 2)) (P (2 * i + 2 + b)) := by
    have := hch.crit (i + 1) (by omega)
    rwa [show 2 * (i + 1) = 2 * i + 2 by ring] at this
  have hγ'M : IsMVtx _ (P (2 * i + b)) := hcr.isMVtx_right _ hyp
  have hγ2'M : IsMVtx _ (P (2 * i + 2 + b)) := hcr2.isMVtx_right _ hyp
  obtain ⟨g, hg0, hg1, -⟩ := hch.lam i hi1 (by omega)
  obtain ⟨g₂, hg₂0, hg₂1, -⟩ := hch.lam (i + 1) (by omega) (by omega)
  rw [show 2 * (i + 1) = 2 * i + 2 by ring] at hg₂0
  rw [show 2 * (i + 1) + 1 = 2 * i + 3 by ring] at hg₂1
  obtain ⟨c, hc, hcs⟩ := hch.straight (i + 1) (by omega) (by omega)
  have hodd := hch.straight_odd (j := i + 1) (by omega) (by omega) hc hcs
  rw [show 2 * (i + 1) = 2 * i + 2 by ring] at hc
  rw [show 2 * (i + 1) + 2 = 2 * i + 4 by ring, show 2 * (i + 1) - 2 = 2 * i by omega] at hcs
  rw [show 2 * (i + 1) + 1 = 2 * i + 3 by ring, show 2 * (i + 1) - 1 = 2 * i + 1 by omega]
    at hodd
  rw [← hP] at hg0 hg1 hg₂0 hg₂1 hc hcs hodd
  set g' := c * g₂ with hg'
  have hg'0 : P (2 * i + 2) = g' • baseA (puAmalgam h.le) := by
    rw [hg', mul_smul, ← hg₂0, (mem_stab _).1 hc]
  have hg'1 : P (2 * i + 1) = g' • baseB (puAmalgam h.le) := by
    rw [hg', mul_smul, ← hg₂1, hodd]
  have hJγ : S5.jOff h.le L (2 ^ k) (P (2 * i)) (P (2 * i + 1)) =
      (S5.jOff h.le L (2 ^ k) (baseA _) (baseB _)).map (MulAut.conj g).toMonoidHom := by
    rw [hg0, hg1, S5B.jOff_smul h.le hLn]
  have hJγ2 : S5.jOff h.le L (2 ^ k) (P (2 * i + 2)) (P (2 * i + 1)) =
      (S5.jOff h.le L (2 ^ k) (baseA _) (baseB _)).map (MulAut.conj g').toMonoidHom := by
    rw [hg'0, hg'1, S5B.jOff_smul h.le hLn]
  have hJγl : S5.jOff h.le L (2 ^ k) (P (2 * i)) (P (2 * i + 1)) ≤
      (S5.vPre h.le a (MSP.qLine l)).map (MulAut.conj g).toMonoidHom := by
    rw [hJγ]
    exact Subgroup.map_mono hJl
  have hJγ2l : S5.jOff h.le L (2 ^ k) (P (2 * i + 2)) (P (2 * i + 1)) ≤
      (S5.vPre h.le a (MSP.qLine l)).map (MulAut.conj g').toMonoidHom := by
    rw [hJγ2]
    exact Subgroup.map_mono hJl
  have hRZ : critR _ (P (2 * i)) (P (2 * i + b)) ≤ ZM _ (P (2 * i)) :=
    commutator_le_left_of_le_normalizer
      ((zm_le_stab_of_isCritical _ hyp hb0 hcr).trans (stab_le_normalizer_zm _ _))
  have hUR : ⁅S5.uSub h.le L (P (2 * i)), ZM _ (P (2 * i + b))⁆ ≤
      critR _ (P (2 * i)) (P (2 * i + b)) :=
    Subgroup.commutator_mono (S5B.uSub_le_zm h.le _) le_rfl
  have hRU : critR _ (P (2 * i)) (P (2 * i + b)) ≤
      ⁅S5.uSub h.le L (P (2 * i)), ZM _ (P (2 * i + b))⁆ :=
    S510S2.critR_le_commutator_uSub_gp h (by omega) hcr
  have hrel1 : (Subgroup.centralizer (ZM _ (P (2 * i + 2 + b)) :
      Set (puAmalgam h.le).Universal)).relIndex (S5.uSub h.le L (P (2 * i + 2))) = 2 ^ k := by
    have := hch.partA hd hb hcase' (j := i + 1) (by omega)
    rwa [show 2 * (i + 1) = 2 * i + 2 by ring] at this
  have hEQ1 : ZM _ (P (2 * i + 2 + b)) ≤ Qv _ (P (2 * i + 4)) := by
    refine zm_le_qv_of_dist_lt _ hγ2'M ?_
    rw [tdist_comm, hch.dist_P (by omega) (by omega)]
    omega
  have hstep1 : (2 ^ k) ^ 2 ≤ (Qv _ (P (2 * i + 2))).relIndex (Qv _ (P (2 * i + 4))) := by
    have hrel := hrel1
    have hcr2' := ms22_iii _ hyp hb0 h.centHyp hcr2
    have hEc : 2 ^ k ≤ (Qv _ (P (2 * i + 2))).relIndex (ZM _ (P (2 * i + 2 + b))) :=
      S511S.le_relIndex_zm_gp h hd hcr2'
    have hRT : ¬ ⁅S5.uSub h.le L (P (2 * i + 2)), ZM _ (P (2 * i + 2 + b))⁆ ≤
        Subgroup.centralizer (Qv _ (P (2 * i + 3)) : Set (puAmalgam h.le).Universal) := by
      intro hle
      have hp2 : ⁅S5.uSub h.le L (P (2 * i + 2)), ZM _ (P (2 * i + 2 + b))⁆ ⊓
          Subgroup.centralizer (Qv _ (P (2 * i + 3)) : Set (puAmalgam h.le).Universal) ≤
            stabCenter _ (P (2 * i + 2)) := by
        have := hch.p2 hb hcase' (j := i + 1) (by omega)
        rwa [show 2 * (i + 1) + 1 = 2 * i + 3 by ring, show 2 * (i + 1) = 2 * i + 2 by ring]
          at this
      refine S511.critR_not_le_stabCenter h hd hcr2 ?_
      exact (S510S2.critR_le_commutator_uSub_gp h (by omega) hcr2).trans
        ((le_inf le_rfl hle).trans hp2)
    have hE : ZM _ (P (2 * i + 2 + b)) ≤ Qv _ (P (2 * i + 3)) := by
      refine zm_le_qv_of_dist_lt _ hγ2'M ?_
      rw [tdist_comm, hch.dist_P (by omega) (by omega)]
      omega
    have hQ : Qv _ (P (2 * i + 4)) ≤ Qv _ (P (2 * i + 3)) := qv_le_qv _ hyp hγ4M hε3γ4.symm
    have hEQ := hEQ1
    have hTQ : Qv _ (P (2 * i + 3)) ≤
        Subgroup.normalizer (Qv _ (P (2 * i + 4)) : Set (puAmalgam h.le).Universal) :=
      (qv_le_stab_of_adj _ hε3γ4).trans (stab_le_normalizer_qv _ _)
    rw [hg₂0] at hrel hEc hRT ⊢
    rw [hg₂1] at hE hQ hTQ hRT
    exact le_relIndex_of_transv_gp h hd g₂ hE hQ hEQ hTQ hrel hEc hRT
  have hqq : (2 ^ k) ^ 2 ≤ (Qv _ (P (2 * i + 2))).relIndex (Qv _ (P (2 * i))) := by
    have e1 : Qv _ (P (2 * i)) = (Qv _ (P (2 * i + 4))).map (MulAut.conj c).toMonoidHom := by
      rw [← hcs, PU.qv_smul]
    have e2 : Qv _ (P (2 * i + 2)) = (Qv _ (P (2 * i + 2))).map (MulAut.conj c).toMonoidHom := by
      rw [← PU.qv_smul, (mem_stab _).1 hc]
    rw [e1, e2, Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj c).injective]
    exact hstep1
  have hRJ : critR _ (P (2 * i)) (P (2 * i + b)) ≤ Subgroup.centralizer
      (S5.jOff h.le L (2 ^ k) (P (2 * i + 2)) (P (2 * i + 1)) :
        Set (puAmalgam h.le).Universal) := by
    have hE : Qv _ (P (2 * i)) ≤ Qv _ (P (2 * i + 1)) := qv_le_qv _ hyp hγM hγε
    have hTE : Qv _ (P (2 * i + 1)) ≤
        Subgroup.normalizer (Qv _ (P (2 * i)) : Set (puAmalgam h.le).Universal) :=
      (qv_le_stab_of_adj _ hγε.symm).trans (stab_le_normalizer_qv _ _)
    have hEl : Qv _ (P (2 * i)) ≤
        (S5.vPre h.le a (MSP.qLine l)).map (MulAut.conj g').toMonoidHom := hQJ.trans hJγ2l
    have hRQ : critR _ (P (2 * i)) (P (2 * i + b)) ≤
        Subgroup.centralizer (Qv _ (P (2 * i)) : Set (puAmalgam h.le).Universal) := by
      rw [← Subgroup.le_centralizer_iff]
      exact (qv_le_centralizer_xm _ _).trans (Subgroup.centralizer_le
        (hRZ.trans (zm_le_xm _ hyp hb0 hγM)))
    rcases Nat.lt_or_ge k 2 with hk1 | hk
    ·
      have hk1' : k = 1 := by
        have := hd.1
        omega
      have hRN := hR.resolve_left (by omega)
      have hodd : ¬ S5.vIm h.le a ((Qv _ (P (2 * i))).map (MulAut.conj g'⁻¹).toMonoidHom) ≤
          commutator (MSP.Sp4 F) := by
        subst hk1'
        have hEst : ZM _ (P (2 * i + 2 + b)) ≤ stab _ (g₂ • baseA (puAmalgam h.le)) := by
          rw [← hg₂0]
          exact zm_le_stab_of_isCritical _ hyp hb0 hcr2
        have hrel2 : (Subgroup.centralizer (ZM _ (P (2 * i + 2 + b)) :
            Set (puAmalgam h.le).Universal)).relIndex
              (S5.uSub h.le L (g₂ • baseA (puAmalgam h.le))) = 2 := by
          rw [← hg₂0, hrel1, pow_one]
        have hZodd := not_vIm_le_commutator_gp h hd g₂ hEst hrel2
        intro hle
        apply hZodd
        refine le_trans (Subgroup.map_mono (Subgroup.comap_mono ?_)) hle
        have e1 : (Qv _ (P (2 * i))).map (MulAut.conj c⁻¹).toMonoidHom = Qv _ (P (2 * i + 4)) := by
          rw [← PU.qv_smul, ← hcs, inv_smul_smul]
        rw [hg', mul_inv_rev, PU.map_conj_mul, e1]
        exact Subgroup.map_mono hEQ1
      have hcard : 2 ^ k < (Qv _ (P (2 * i + 2))).relIndex (Qv _ (P (2 * i))) := by
        have h2 : 2 ≤ 2 ^ k := by
          calc 2 = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hd.1
        nlinarith
      rw [hg'1] at hE
      rw [hg'0] at hcard hRX hRN
      have key := uSub_sup_inf_centralizer_le_gp h hd g' hE hl hEl hcard (Or.inr hodd)
      exact (le_inf hRN hRQ).trans (key.trans (Subgroup.centralizer_le hJγ2l))
    · rw [hg'1] at hE hTE
      rw [hg'0] at hqq hRX
      have key := xm_inf_centralizer_le_centralizer_vPre_gp h h32 hd hk g' hE hTE hl hEl hqq
      exact (le_inf hRX hRQ).trans (key.trans (Subgroup.centralizer_le hJγ2l))
  have hnot : ¬ S5.jOff h.le L (2 ^ k) (P (2 * i + 2)) (P (2 * i + 1)) ≤
      (S5.vPre h.le a (MSP.qLine l)).map (MulAut.conj g).toMonoidHom := by
    intro hle
    have hq1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    have hQJγ : Qv _ (P (2 * i)) ≤ S5.jOff h.le L (2 ^ k) (P (2 * i)) (P (2 * i + 1)) :=
      S5B.qv_le_jOff h hq1 hγM hγε
    have hJq' : (2 ^ k) ^ 2 ≤ (Qv _ (P (2 * i))).relIndex
        (S5.jOff h.le L (2 ^ k) (P (2 * i)) (P (2 * i + 1))) := by
      rw [hJγ, hg0, PU.qv_smul,
        Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective]
      exact hJq
    have hcardJ : Nat.card (S5.jOff h.le L (2 ^ k) (P (2 * i + 2)) (P (2 * i + 1))) =
        Nat.card (S5.jOff h.le L (2 ^ k) (P (2 * i)) (P (2 * i + 1))) := by
      rw [hJγ, hJγ2, Subgroup.card_map_of_injective (MulAut.conj g').injective,
        Subgroup.card_map_of_injective (MulAut.conj g).injective]
    have hrelEq : (Qv _ (P (2 * i))).relIndex
        (S5.jOff h.le L (2 ^ k) (P (2 * i + 2)) (P (2 * i + 1))) =
        (Qv _ (P (2 * i))).relIndex (S5.jOff h.le L (2 ^ k) (P (2 * i)) (P (2 * i + 1))) := by
      have h1 := Subgroup.relIndex_mul_card (Qv _ (P (2 * i)))
        (S5.jOff h.le L (2 ^ k) (P (2 * i + 2)) (P (2 * i + 1)))
      have h2 := Subgroup.relIndex_mul_card (Qv _ (P (2 * i)))
        (S5.jOff h.le L (2 ^ k) (P (2 * i)) (P (2 * i + 1)))
      rw [inf_eq_left.2 hQJ] at h1
      rw [inf_eq_left.2 hQJγ] at h2
      have : Finite ↥(Qv _ (P (2 * i + 1))) := finite_qv _ hyp hε
      have : Finite ↥(Qv _ (P (2 * i))) :=
        Finite.of_injective _ (Subgroup.inclusion_injective (qv_le_qv _ hyp hγM hγε))
      have hpos : 0 < Nat.card ↥(Qv _ (P (2 * i))) := Nat.card_pos
      rw [hcardJ] at h1
      exact Nat.eq_of_mul_eq_mul_right hpos (h1.trans h2.symm)
    have hU : (Subgroup.centralizer (S5.jOff h.le L (2 ^ k) (P (2 * i + 2)) (P (2 * i + 1)) :
        Set (puAmalgam h.le).Universal)).relIndex (S5.uSub h.le L (P (2 * i))) ≤ (2 ^ k) ^ 2 := by
      rw [hg0]
      exact relIndex_centralizer_le_of_le_qLine_gp h hd g hl hle
    have hcand : S5.IsOffCand h.le L (2 ^ k) (P (2 * i)) (P (2 * i + 1))
        (S5.jOff h.le L (2 ^ k) (P (2 * i + 2)) (P (2 * i + 1))) :=
      ⟨S5B.jOff_le_qv h.le L _ _ _, hU.trans (hrelEq ▸ hJq'), hU⟩
    have hJn : ¬ S5.jOff h.le L (2 ^ k) (P (2 * i)) (P (2 * i + 1)) ≤ Qv _ (P (2 * i)) := by
      intro hle'
      rw [Subgroup.relIndex_eq_one.2 hle'] at hJq'
      have : 4 ≤ (2 ^ k) ^ 2 := by
        have : 2 ≤ 2 ^ k := by
          calc 2 = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hd.1
        nlinarith
      omega
    exact hcase i (by omega) (eq_jOff_of_isOffCand h hε hcand hcardJ hJn)
  obtain ⟨t₀, ht₀J, ht₀l⟩ := Set.not_subset.1 hnot
  have hZl : ZM _ (P (2 * i + b)) ≤
      (S5.vPre h.le a (MSP.qLine l)).map (MulAut.conj g).toMonoidHom := by
    refine (zm_le_qv_of_dist_lt _ hγ'M ?_).trans (hQJ'.trans hJγl)
    rw [tdist_comm, hch.dist_P (by omega) (by omega)]
    omega
  have ht₀T : t₀ ∈ Qv _ (P (2 * i + 1)) := S5B.jOff_le_qv h.le L _ _ _ ht₀J
  have hRt : ⁅S5.uSub h.le L (P (2 * i)), ZM _ (P (2 * i + b))⁆ ≤
      Subgroup.centralizer ({t₀} : Set (puAmalgam h.le).Universal) :=
    (hUR.trans hRJ).trans (Subgroup.centralizer_le (Set.singleton_subset_iff.2 ht₀J))
  rw [hg1] at ht₀T
  rw [hg0] at hRt
  have key := commutator_le_centralizer_of_not_mem_gp h hd g hl hTl hZl ht₀T ht₀l hRt
  rw [← hg0, ← hg1] at key
  have hp2 : ⁅S5.uSub h.le L (P (2 * i)), ZM _ (P (2 * i + b))⁆ ⊓
      Subgroup.centralizer (Qv _ (P (2 * i + 1)) : Set (puAmalgam h.le).Universal) ≤
        stabCenter _ (P (2 * i)) := hch.p2 hb hcase' (j := i) (by omega)
  exact S511.critR_not_le_stabCenter h hd hcr (hRU.trans ((le_inf le_rfl key).trans hp2))

theorem false_of_two_le (h32 : S32) (hd : S5.IsSp4Data M T L k F a) (hk : 2 ≤ k)
    (hch : S510.IsChain h (2 ^ k) a s t N) (hb : 4 < critDist (puAmalgam h.le))
    (hcase : ∀ j ≤ N, S5.jOff h.le L (2 ^ k) (geo _ s t (2 * j + 2)) (geo _ s t (2 * j + 1)) ≠
      S5.jOff h.le L (2 ^ k) (geo _ s t (2 * j)) (geo _ s t (2 * j + 1)))
    (hlc : S510.LineCase h (2 ^ k) a)
    (hJq : (2 ^ k) ^ 2 ≤ (Qv _ (baseA (puAmalgam h.le))).relIndex
      (S5.jOff h.le L (2 ^ k) (baseA _) (baseB _)))
    {i : ℕ} (hi1 : 1 ≤ i) (hiN : i + 3 ≤ N)
    (hQJ : Qv _ (geo _ s t (2 * i)) ≤
      S5.jOff h.le L (2 ^ k) (geo _ s t (2 * i + 2)) (geo _ s t (2 * i + 1)))
    (hQJ' : Qv _ (geo _ s t (2 * i + 2)) ≤
      S5.jOff h.le L (2 ^ k) (geo _ s t (2 * i)) (geo _ s t (2 * i + 1)))
    (hRX : critR _ (geo _ s t (2 * i)) (geo _ s t (2 * i + critDist (puAmalgam h.le))) ≤
      XM _ (geo _ s t (2 * i + 2))) : False :=
  false_of_conf h32 hd hch hb hcase hlc hJq hi1 hiN hQJ hQJ' hRX (Or.inl hk)

end IsChain

@[expose] def CruxNXZ2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L),
    PUMin M T L → 4 < critDist (puAmalgam h.le) →
    ∀ (k : ℕ) (F : Type) (_ : Field F) (_ : Fintype F) (a : ↥M →* ↥(StatedSp 2 F)), k = 1 →
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

theorem cruxNXZ_of_cruxNXZ2 (h32 : S32) (hcr : CruxNXZ2) : S511S.CruxNXZ := by
  intro G _ _ M T L h hmin hb k F _ _ a hd hXU hlc hJq α' hc hαβ N s hsα hch hcase h2 h3 i hi1
    hiN
  rcases Nat.lt_or_ge k 2 with hk | hk
  · have hk1 : k = 1 := by have := hd.1; omega
    exact hcr G M T L h hmin hb k F _ _ a hk1 hd hXU hlc hJq α' hc hαβ N s hsα hch hcase h2 h3 i
      hi1 hiN
  · exact (IsChain.false_of_two_le h32 hd hk hch hb hcase hlc hJq hi1 hiN
      (h2 i hi1 (by omega)).2.1 (h3 i hi1 (by omega)).1 (h3 i hi1 (by omega)).2).elim

theorem s510NXZ'_of_cruxNXZ2 (h32 : S32) (hcr : CruxNXZ2) : S5B.S510NXZ' :=
  S511S.s510NXZ'_of_crux (cruxNXZ_of_cruxNXZ2 h32 hcr)

end CFSG.Quasithin.MS93.S5C
