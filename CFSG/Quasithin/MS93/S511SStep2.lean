module

public import CFSG.Quasithin.MS93.S511SPath
public import CFSG.Quasithin.MS93.S510S2E

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Pointwise

namespace S511S

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
  {k : ℕ} {F : Type} [Field F] [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

namespace IsChain

variable {h : PUHyp M T L} {s t : Vtx (puAmalgam h.le)} {N : ℕ}

theorem alt (h32 : S32) (hX2 : S33.S33X52) (h52 : S52) (h53 : S53) (h54 : S54)
    (h56f : S5.S56f) (hZ : S5Q2.Q2EvenZ) (h59 : S5B.S59) (hmin : PUMin M T L)
    (hb : 4 < critDist (puAmalgam h.le)) (hd : S5.IsSp4Data M T L k F a)
    (h56all : ∀ α' : Vtx (puAmalgam h.le), IsCritical _ (baseA _) α' →
      geo _ (baseA _) α' 1 = baseB _ →
      ∃ l : Submodule F (MSP.V4 F), S5.Case56 h (2 ^ k) a (geo _ (baseA (puAmalgam h.le)) α' 2) l)
    (hch : S510.IsChain h (2 ^ k) a s t N) {j : ℕ} (hjN : j ≤ N) :
    2 ^ k < (Qv _ (geo _ s t (2 * j + 2))).relIndex
        (Vv _ (geo _ s t (2 * j + critDist (puAmalgam h.le)))) ∨
      2 ^ k < (Qv _ (geo _ s t (2 * j))).relIndex
        (Vv _ (geo _ s t (2 * j + critDist (puAmalgam h.le))) ⊓ Qv _ (geo _ s t (2 * j + 2))) := by
  have hyp := h.hyp20
  have hb0 := h.critDist_pos
  have hdd := hch.dist_eq
  have hcr := hch.crit j hjN
  have hrev := ms22_iii _ hyp hb0 h.centHyp hcr
  have key := step1_gp h32 hX2 h52 h53 h54 h56f hZ h59 h hmin hb hd h56all hrev
  rw [hch.geo_eq (i := 2 * j) (j := 2 * j + critDist (puAmalgam h.le)) (m := 2) (by omega)
    (by omega) (by omega)] at key
  set V := Vv _ (geo _ s t (2 * j + critDist (puAmalgam h.le))) with hV
  set A := V ⊓ Qv _ (geo _ s t (2 * j + 2)) with hA
  have hmul : (A ⊓ Qv _ (geo _ s t (2 * j))).relIndex A * A.relIndex V =
      (A ⊓ Qv _ (geo _ s t (2 * j))).relIndex V :=
    Subgroup.relIndex_mul_relIndex _ _ _ inf_le_left inf_le_left
  rw [Subgroup.inf_relIndex_left, Subgroup.inf_relIndex_left] at hmul
  by_contra hno
  push Not at hno
  obtain ⟨h1, h2⟩ := hno
  have h3 : (Qv _ (geo _ s t (2 * j))).relIndex A * (Qv _ (geo _ s t (2 * j + 2))).relIndex V ≤
      2 ^ k * 2 ^ k := Nat.mul_le_mul h2 h1
  rw [hmul, ← pow_two] at h3
  omega

theorem step2 (h32 : S32) (hX2 : S33.S33X52) (h52 : S52) (h53 : S53) (h54 : S54)
    (h56f : S5.S56f) (hZ : S5Q2.Q2EvenZ) (h59 : S5B.S59) (hmin : PUMin M T L)
    (hb : 6 < critDist (puAmalgam h.le)) (hd : S5.IsSp4Data M T L k F a)
    (h56all : ∀ α' : Vtx (puAmalgam h.le), IsCritical _ (baseA _) α' →
      geo _ (baseA _) α' 1 = baseB _ →
      ∃ l : Submodule F (MSP.V4 F), S5.Case56 h (2 ^ k) a (geo _ (baseA (puAmalgam h.le)) α' 2) l)
    (hch : S510.IsChain h (2 ^ k) a s t N)
    (hgood : ∀ j, 1 ≤ j → j ≤ N → ∃ g : (puAmalgam h.le).Universal,
      geo _ s t (2 * j) = g • baseA (puAmalgam h.le) ∧ geo _ s t (2 * j + 1) = g • baseB _ ∧
      GoodLamF h (2 ^ k) a (g⁻¹ • geo _ s t (2 * j + critDist (puAmalgam h.le)))
        (g⁻¹ • geo _ s t (2 * j - 2)))
    {j : ℕ} (hj : j + 3 ≤ N) :
    ¬ critR _ (geo _ s t (2 * j)) (geo _ s t (2 * j + critDist (puAmalgam h.le))) ≤
      stabCenter _ (geo _ s t (2 * j + 2)) := by
  have hyp := h.hyp20
  have hb0 := h.critDist_pos
  have hC := h.centHyp
  have hb4 : 4 < critDist (puAmalgam h.le) := by omega
  have hb2 : 2 < critDist (puAmalgam h.le) := by omega
  have hdd := hch.dist_eq
  set b := critDist (puAmalgam h.le) with hbdef
  set P := geo _ s t with hP
  have hdist : ∀ {i i' : ℕ}, i ≤ i' → i' ≤ b + 2 * N →
      (puAmalgam h.le).treeGraph.dist (P i') (P i) = i' - i := fun h1 h2 => by
    rw [tdist_comm]
    exact hch.dist_P h1 h2
  have hadj : ∀ {i i' : ℕ}, i' = i + 1 → i < b + 2 * N →
      (puAmalgam h.le).treeGraph.Adj (P i) (P i') := fun e h1 => by
    rw [e]
    exact hch.adj_P h1
  have hc0 : IsCritical _ (P (2 * j)) (P (2 * j + b)) := hch.crit j (by omega)
  have hc1 : IsCritical _ (P (2 * j + 2)) (P (2 * j + 2 + b)) := by
    have := hch.crit (j + 1) (by omega)
    rwa [show 2 * (j + 1) = 2 * j + 2 by ring] at this
  have hc2 : IsCritical _ (P (2 * j + 4)) (P (2 * j + 4 + b)) := by
    have := hch.crit (j + 2) (by omega)
    rwa [show 2 * (j + 2) = 2 * j + 4 by ring] at this
  have hr2 := ms22_iii _ hyp hb0 hC hc2
  have hM2 := hc1.1
  have hM4 := hc2.1
  have hMb0 := hc0.isMVtx_right _ hyp
  have hMb2 := hc1.isMVtx_right _ hyp
  have hMb4 := hc2.isMVtx_right _ hyp
  have hadj23 : (puAmalgam h.le).treeGraph.Adj (P (2 * j + 2)) (P (2 * j + 3)) :=
    hadj (by ring) (by omega)
  have hadj43 : (puAmalgam h.le).treeGraph.Adj (P (2 * j + 4)) (P (2 * j + 3)) :=
    (hadj (by ring) (by omega)).symm
  have hadj45 : (puAmalgam h.le).treeGraph.Adj (P (2 * j + 4)) (P (2 * j + 5)) :=
    hadj (by ring) (by omega)
  have hadj65 : (puAmalgam h.le).treeGraph.Adj (P (2 * j + 6)) (P (2 * j + 5)) :=
    (hadj (by ring) (by omega)).symm
  set R := critR _ (P (2 * j)) (P (2 * j + b)) with hR
  have hR2 : R ≤ ZM _ (P (2 * j + 2)) := by
    have := critR_le_zm_gp h32 h53 hZ h hmin hb2 hd h56all hc0
    rwa [hch.geo_eq (i := 2 * j) (j := 2 * j + b) (m := 2) (by omega) (by omega) (by omega)] at this
  have hRb : R ≤ ZM _ (P (2 * j + b)) := by
    rw [hR, critR, Subgroup.commutator_comm]
    exact commutator_le_left_of_le_normalizer ((zm_le_stab_of_isCritical _ hyp hb0
      (ms22_iii _ hyp hb0 hC hc0)).trans (stab_le_normalizer_zm _ _))
  have hRn : ¬ R ≤ stabCenter _ (P (2 * j)) := S511.critR_not_le_stabCenter h hd hc0
  intro hRc
  have hR4 : R ≤ ZM _ (P (2 * j + 4)) :=
    (le_inf hRc (hR2.trans (zm_le_xm _ hyp hb0 hM2))).trans
      ((S5B.stabCenter_inf_xm_le_zh h hM2 hadj23).trans (zh_le_zm _ hadj43))
  have hfalse : R ≤ stabCenter _ (P (2 * j + 4)) → False := by
    intro hR4c
    apply hRn
    intro r hr
    have h1 : r ∈ stabCenter _ (P (2 * (j + 1))) := by
      rw [show 2 * (j + 1) = 2 * j + 2 by ring]
      exact hRc hr
    have h2 : r ∈ stabCenter _ (P (2 * (j + 1) + 2)) := by
      rw [show 2 * (j + 1) + 2 = 2 * j + 4 by ring]
      exact hR4c hr
    exact hch.mem_stabCenter_all (i := j + 1) (by omega) h1 h2 j (by omega)
  have hRcQ2 : R ≤ Subgroup.centralizer (Qv _ (P (2 * j + 2)) : Set _) := fun r hr =>
    Subgroup.mem_centralizer_iff.2 fun y hy =>
      S510.commute_of_mem_stabCenter (hRc hr) (qv_le_stab _ _ hy)
  have hRcV : ∀ {i : ℕ}, i ≤ 4 → IsMVtx _ (P (2 * j + i + b)) → 2 * j + i + b ≤ b + 2 * N →
      R ≤ Subgroup.centralizer (Vv _ (P (2 * j + i + b)) : Set _) := by
    intro i hi hMi hiN
    rw [Subgroup.le_centralizer_iff]
    refine (vv_le_centralizer_zm h hMi hMb0 ?_).trans (Subgroup.centralizer_le hRb)
    rw [hdist (by omega) hiN]
    omega
  have hRcV2 : R ≤ Subgroup.centralizer (Vv _ (P (2 * j + 2 + b)) : Set _) :=
    hRcV (i := 2) (by omega) hMb2 (by omega)
  have hRcV4 : R ≤ Subgroup.centralizer (Vv _ (P (2 * j + 4 + b)) : Set _) :=
    hRcV (i := 4) (by omega) hMb4 (by omega)
  have hVQ6 : Vv _ (P (2 * j + 2 + b)) ≤ Qv _ (P (2 * j + 6)) :=
    vv_le_qv_of_dist h hMb2 (by rw [hdist (by omega) (by omega)]; omega)
  have hVQ8 : Vv _ (P (2 * j + 4 + b)) ≤ Qv _ (P (2 * j + 8)) :=
    vv_le_qv_of_dist h hMb4 (by rw [hdist (by omega) (by omega)]; omega)
  have hX4 : ∀ E : Subgroup (puAmalgam h.le).Universal, E ≤ Qv _ (P (2 * j + 6)) →
      2 ^ k < (Qv _ (P (2 * j + 4))).relIndex E →
      ZM _ (P (2 * j + 4)) ⊓ Subgroup.centralizer (Qv _ (P (2 * j + 2)) : Set _) ⊓
        Subgroup.centralizer (E : Set _) ≤ stabCenter _ (P (2 * j + 4)) := by
    intro E hE hEq
    have := le_stabCenter_x1 h32 h53 h59 hmin hb4 hd hch (j := j + 2) (by omega) (by omega)
      (hgood (j + 2) (by omega) (by omega)) (E := E)
      (by rw [show 2 * (j + 2) + 2 = 2 * j + 6 by ring]; exact hE)
      (by rw [show 2 * (j + 2) = 2 * j + 4 by ring]; exact hEq)
    rwa [show 2 * (j + 2) = 2 * j + 4 by ring, show 2 * j + 4 - 2 = 2 * j + 2 by omega] at this
  have hX4' : ∀ E : Subgroup (puAmalgam h.le).Universal, E ≤ Qv _ (P (2 * j + 6)) →
      ¬ E ≤ Qv _ (P (2 * j + 4)) → ∀ H : Subgroup (puAmalgam h.le).Universal,
      H ≤ ZM _ (P (2 * j + 4)) ⊓ Subgroup.centralizer (Qv _ (P (2 * j + 2)) : Set _) ⊓
        Subgroup.centralizer (E : Set _) →
      (stabCenter _ (P (2 * j + 4))).relIndex H ≤ 2 ^ k := by
    intro E hE hEQ H hH
    have := relIndex_x1_le h32 h53 h59 hmin hb4 hd hch (j := j + 2) (by omega) (by omega)
      (hgood (j + 2) (by omega) (by omega)) (E := E)
      (by rw [show 2 * (j + 2) + 2 = 2 * j + 6 by ring]; exact hE)
      (by rw [show 2 * (j + 2) = 2 * j + 4 by ring]; exact hEQ) (H := H)
      (by rw [show 2 * (j + 2) = 2 * j + 4 by ring, show 2 * j + 4 - 2 = 2 * j + 2 by omega]
          exact hH)
    rwa [show 2 * (j + 2) = 2 * j + 4 by ring] at this
  have hX6 : ∀ E : Subgroup (puAmalgam h.le).Universal, E ≤ Qv _ (P (2 * j + 8)) →
      2 ^ k < (Qv _ (P (2 * j + 6))).relIndex E →
      ZM _ (P (2 * j + 6)) ⊓ Subgroup.centralizer (Qv _ (P (2 * j + 4)) : Set _) ⊓
        Subgroup.centralizer (E : Set _) ≤ stabCenter _ (P (2 * j + 6)) := by
    intro E hE hEq
    have := le_stabCenter_x1 h32 h53 h59 hmin hb4 hd hch (j := j + 3) (by omega) (by omega)
      (hgood (j + 3) (by omega) (by omega)) (E := E)
      (by rw [show 2 * (j + 3) + 2 = 2 * j + 8 by ring]; exact hE)
      (by rw [show 2 * (j + 3) = 2 * j + 6 by ring]; exact hEq)
    rwa [show 2 * (j + 3) = 2 * j + 6 by ring, show 2 * j + 6 - 2 = 2 * j + 4 by omega] at this
  have hX2' : ∀ E : Subgroup (puAmalgam h.le).Universal, E ≤ Qv _ (P (2 * j + 4)) →
      2 ^ k < (Qv _ (P (2 * j + 2))).relIndex E →
      (2 ^ k) ^ 2 ≤ (stabCenter _ (P (2 * j + 2))).relIndex
        ⁅S5.uSub h.le L (P (2 * j + 2)), E⁆ := by
    intro E hE hEq
    have := le_relIndex_commutator_x1 hb2 hd hch (j := j + 1) (by omega)
      (hgood (j + 1) (by omega) (by omega)) (E := E)
      (by rw [show 2 * (j + 1) + 2 = 2 * j + 4 by ring]; exact hE)
      (by rw [show 2 * (j + 1) = 2 * j + 2 by ring]; exact hEq)
    rwa [show 2 * (j + 1) = 2 * j + 2 by ring] at this
  have halt1 := alt h32 hX2 h52 h53 h54 h56f hZ h59 hmin hb4 hd h56all hch (j := j + 1)
    (by omega)
  rw [show 2 * (j + 1) = 2 * j + 2 by ring, show 2 * j + 2 + 2 = 2 * j + 4 by ring] at halt1
  have halt2 := alt h32 hX2 h52 h53 h54 h56f hZ h59 hmin hb4 hd h56all hch (j := j + 2)
    (by omega)
  rw [show 2 * (j + 2) = 2 * j + 4 by ring, show 2 * j + 4 + 2 = 2 * j + 6 by ring] at halt2
  rcases halt1 with hI1 | hB1
  · exact hfalse ((le_inf (le_inf hR4 hRcQ2) hRcV2).trans (hX4 _ hVQ6 hI1))
  rcases halt2 with hI2 | hB2
  swap
  · exact hfalse ((le_inf (le_inf hR4 hRcQ2)
      (hRcV4.trans (Subgroup.centralizer_le inf_le_left))).trans (hX4 _ inf_le_right hB2))
  set E' := Vv _ (P (2 * j + 2 + b)) ⊓ Qv _ (P (2 * j + 4)) with hE'
  set H := ⁅S5.uSub h.le L (P (2 * j + 2)), E'⁆ with hH
  have hX2v := hX2' E' inf_le_right hB1
  have hU2 : S5.uSub h.le L (P (2 * j + 2)) ≤ ZM _ (P (2 * j + 2)) := S5B.uSub_le_zm h.le _
  have hE'st : E' ≤ stab _ (P (2 * j + 2)) :=
    inf_le_right.trans ((qv_le_qv _ hyp hM4 hadj43).trans (qv_le_stab_of_adj _ hadj23.symm))
  have hHZ2 : H ≤ ZM _ (P (2 * j + 2)) :=
    (commutator_le_left_of_le_normalizer (hE'st.trans (S510.stab_le_normalizer_uSub h _))).trans
      hU2
  have hUn : S5.uSub h.le L (P (2 * j + 2)) ≤
      Subgroup.normalizer (E' : Set (puAmalgam h.le).Universal) := by
    have h1 : ZM _ (P (2 * j + 2)) ≤ stab _ (P (2 * j + 2 + b)) :=
      S510S2.zm_le_stab_of_dist_le h hM2 (by rw [tdist_comm, hdist (by omega) (by omega)]; omega)
    have h2 : ZM _ (P (2 * j + 2)) ≤ stab _ (P (2 * j + 4)) :=
      S510S2.zm_le_stab_of_dist_le h hM2 (by rw [tdist_comm, hdist (by omega) (by omega)]; omega)
    exact hU2.trans ((le_inf (h1.trans (stab_le_normalizer_of_smul _
      (fun g ρ => vi_smul _ g ρ 2) _)) (h2.trans (stab_le_normalizer_qv _ _))).trans
        (Subgroup.inf_normalizer_le_normalizer_inf))
  have hHE' : H ≤ E' := by
    rw [hH, Subgroup.commutator_comm]
    exact commutator_le_left_of_le_normalizer hUn
  have hHV : H ≤ Vv _ (P (2 * j + 2 + b)) := hHE'.trans inf_le_left
  obtain ⟨α₀, hc₀, hβ₀⟩ := exists_isCritical_geo _ hyp hb0 (isMVtx_baseA (puAmalgam h.le))
    (adj_baseA_baseB _)
  obtain ⟨l₀, hl₀⟩ := h56all α₀ hc₀ hβ₀
  have hJall : ∀ (δ : Vtx (puAmalgam h.le)) (l : Submodule F (MSP.V4 F)),
      (puAmalgam h.le).treeGraph.Adj (baseB _) δ → S5.Case56 h (2 ^ k) a δ l →
      ZM _ δ ⊓ XM _ (baseA (puAmalgam h.le)) ⊓ Subgroup.centralizer
        (S5.jOff h.le L (2 ^ k) (baseA (puAmalgam h.le)) (baseB _) : Set _) ≤
      ZM _ (baseA (puAmalgam h.le)) := fun _ _ hβδ hl =>
    zm_inf_xm_inf_centralizer_jOff_le_zm_e h32 h53 hZ h hmin hb2 hd hβδ hl
  have hJeq : S5.jOff h.le L (2 ^ k) (P (2 * j + 2)) (P (2 * j + 3)) =
      S5.jOff h.le L (2 ^ k) (P (2 * j + 4)) (P (2 * j + 3)) := by
    have := jOff_eq_gp h h56all hc1
    rw [hch.geo_eq (i := 2 * j + 2) (j := 2 * j + 2 + b) (m := 2) (by omega) (by omega)
      (by omega), hch.geo_eq (i := 2 * j + 2) (j := 2 * j + 2 + b) (m := 1) (by omega)
      (by omega) (by omega), show 2 * j + 2 + 2 = 2 * j + 4 by ring,
      show 2 * j + 2 + 1 = 2 * j + 3 by ring] at this
    exact this.symm
  have hHZ4 : H ≤ ZM _ (P (2 * j + 4)) :=
    (Subgroup.commutator_mono hU2 inf_le_right).trans (commutator_zm_qv_le_zm_gp h hb2 hd hJall
      hl₀.2.1 hl₀.2.2.1 hl₀.2.2.2 hM4 hadj43 hadj23.symm hJeq)
  have hVnQ4 : ¬ Vv _ (P (2 * j + 2 + b)) ≤ Qv _ (P (2 * j + 4)) := fun hle =>
    hr2.2.2 ((S38E.zm_le_vv _ hMb4
      (by rw [tdist_comm, hdist (by omega) (by omega)]; omega)).trans hle)
  have hHc2 : H ≤ Subgroup.centralizer (Qv _ (P (2 * j + 2)) : Set _) :=
    hHZ2.trans (zm_le_centralizer_qv _ hyp hM2)
  have hHcV : H ≤ Subgroup.centralizer (Vv _ (P (2 * j + 2 + b)) : Set _) :=
    hHV.trans (vv_le_centralizer_self h hb4 hMb2)
  have hX1'v := hX4' _ hVQ6 hVnQ4 H (le_inf (le_inf hHZ4 hHc2) hHcV)
  have hK6 : stabCenter _ (P (2 * j + 4)) ⊓ H ≤ stabCenter _ (P (2 * j + 6)) := by
    refine le_trans (le_inf (le_inf ?_ ?_) ?_) (hX6 _ hVQ8 hI2)
    · exact (le_inf inf_le_left (inf_le_right.trans (hHZ4.trans (zm_le_xm _ hyp hb0 hM4)))).trans
        ((S5B.stabCenter_inf_xm_le_zh h hM4 hadj45).trans (zh_le_zm _ hadj65))
    · exact fun r hr => Subgroup.mem_centralizer_iff.2 fun y hy =>
        S510.commute_of_mem_stabCenter hr.1 (qv_le_stab _ _ hy)
    · exact inf_le_right.trans (hHV.trans (vv_le_centralizer_vv h hMb2 hMb4
        (by rw [tdist_comm, hdist (by omega) (by omega)]; omega)))
  have hK2 : stabCenter _ (P (2 * j + 4)) ⊓ H ≤ stabCenter _ (P (2 * j + 2)) := by
    intro r hr
    have h1 : r ∈ stabCenter _ (P (2 * (j + 2))) := by
      rw [show 2 * (j + 2) = 2 * j + 4 by ring]
      exact hr.1
    have h2 : r ∈ stabCenter _ (P (2 * (j + 2) + 2)) := by
      rw [show 2 * (j + 2) + 2 = 2 * j + 6 by ring]
      exact hK6 hr
    have := hch.mem_stabCenter_all (i := j + 2) (by omega) h1 h2 (j + 1) (by omega)
    rwa [show 2 * (j + 1) = 2 * j + 2 by ring] at this
  have : Finite ↥(ZM _ (P (2 * j + 2))) := finite_zm h hb2 hM2
  have hHfin : Finite ↥H := Finite.of_injective _ (Subgroup.inclusion_injective hHZ2)
  have hle : (stabCenter _ (P (2 * j + 2))).relIndex H ≤
      (stabCenter _ (P (2 * j + 4))).relIndex H := by
    rw [← Subgroup.inf_relIndex_right (stabCenter _ (P (2 * j + 2))) H,
      ← Subgroup.inf_relIndex_right (stabCenter _ (P (2 * j + 4))) H]
    exact Subgroup.relIndex_le_of_le_left (le_inf hK2 inf_le_right)
      (by rw [Subgroup.relIndex]; exact Subgroup.index_ne_zero_of_finite)
  have hq : 2 ≤ 2 ^ k := by
    have := hd.1
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) this
  have h1 := hX2v.trans (hle.trans hX1'v)
  nlinarith

end IsChain

theorem false_of_gt6 (h32 : S32) (hX2 : S33.S33X52) (h52 : S52) (h53 : S53) (h54 : S54)
    (h56f : S5.S56f) (hZ : S5Q2.Q2EvenZ) (h59 : S5B.S59) (h : PUHyp M T L)
    (hmin : PUMin M T L) (hd : S5.IsSp4Data M T L k F a) (hb : 6 < critDist (puAmalgam h.le))
    (h56all : ∀ α' : Vtx (puAmalgam h.le), IsCritical _ (baseA _) α' →
      geo _ (baseA _) α' 1 = baseB _ →
      ∃ l : Submodule F (MSP.V4 F), S5.Case56 h (2 ^ k) a (geo _ (baseA (puAmalgam h.le)) α' 2) l) :
    False := by
  have hyp := h.hyp20
  have hb0 := h.critDist_pos
  have hC := h.centHyp
  have hb4 : 4 < critDist (puAmalgam h.le) := by omega
  have hb2 : 2 < critDist (puAmalgam h.le) := by omega
  obtain ⟨α', hcα⟩ := exists_isCritical_of_isMVtx _ hyp (isMVtx_baseA (puAmalgam h.le))
  obtain ⟨s, -, hch, hgood⟩ := exists_isChain_goodF h32 hX2 h52 h54 h56f h59 h hmin hb4 hd
    h56all hcα 4
  have hdd := hch.dist_eq
  set b := critDist (puAmalgam h.le) with hbdef
  set P := geo _ s α' with hP
  have hc0 : IsCritical _ (P 0) (P b) := by
    have := hch.crit 0 (by omega)
    rwa [Nat.mul_zero, zero_add] at this
  have hc1 : IsCritical _ (P 2) (P (2 + b)) := by
    have := hch.crit 1 (by omega)
    rwa [Nat.mul_one] at this
  have hMb0 := hc0.isMVtx_right _ hyp
  have hMb1 := hc1.isMVtx_right _ hyp
  have hst0 := IsChain.step2 h32 hX2 h52 h53 h54 h56f hZ h59 hmin hb hd h56all hch hgood
    (j := 0) (by omega)
  have hst1 := IsChain.step2 h32 hX2 h52 h53 h54 h56f hZ h59 hmin hb hd h56all hch hgood
    (j := 1) (by omega)
  rw [Nat.mul_zero, zero_add, zero_add] at hst0
  rw [Nat.mul_one, show 2 + 2 = 4 by rfl] at hst1
  have halt := IsChain.alt h32 hX2 h52 h53 h54 h56f hZ h59 hmin hb4 hd h56all hch (j := 1)
    (by omega)
  rw [Nat.mul_one, show 2 + 2 = 4 by rfl] at halt
  have hR1Z2 : critR _ (P 2) (P (2 + b)) ≤ ZM _ (P 2) := commutator_le_left_of_le_normalizer
    ((zm_le_stab_of_isCritical _ hyp hb0 hc1).trans (stab_le_normalizer_zm _ _))
  have hR1Z4 : critR _ (P 2) (P (2 + b)) ≤ ZM _ (P 4) := by
    have := critR_le_zm_gp h32 h53 hZ h hmin hb2 hd h56all hc1
    rwa [hch.geo_eq (i := 2) (j := 2 + b) (m := 2) (by omega) (by omega) (by omega)] at this
  have hR1Zb : critR _ (P 2) (P (2 + b)) ≤ ZM _ (P (2 + b)) := by
    rw [critR, Subgroup.commutator_comm]
    exact commutator_le_left_of_le_normalizer ((zm_le_stab_of_isCritical _ hyp hb0
      (ms22_iii _ hyp hb0 hC hc1)).trans (stab_le_normalizer_zm _ _))
  have hR0Z0 : critR _ (P 0) (P b) ≤ ZM _ (P 0) := commutator_le_left_of_le_normalizer
    ((zm_le_stab_of_isCritical _ hyp hb0 hc0).trans (stab_le_normalizer_zm _ _))
  have hR0Z2 : critR _ (P 0) (P b) ≤ ZM _ (P 2) := by
    have := critR_le_zm_gp h32 h53 hZ h hmin hb2 hd h56all hc0
    rwa [hch.geo_eq (i := 0) (j := b) (m := 2) (by omega) (by omega) (by omega)] at this
  have hR0Zb : critR _ (P 0) (P b) ≤ ZM _ (P b) := by
    rw [critR, Subgroup.commutator_comm]
    exact commutator_le_left_of_le_normalizer ((zm_le_stab_of_isCritical _ hyp hb0
      (ms22_iii _ hyp hb0 hC hc0)).trans (stab_le_normalizer_zm _ _))
  rcases halt with hI | hB
  ·
    apply hst1
    have hVQ6 : Vv _ (P (2 + b)) ≤ Qv _ (P 6) := vv_le_qv_of_dist h hMb1 (by
      rw [tdist_comm, hch.dist_P (by omega) (by omega)]
      omega)
    have key := IsChain.le_stabCenter_x1 h32 h53 h59 hmin hb4 hd hch (j := 2) (by omega)
      (by omega) (hgood 2 (by omega) (by omega)) (E := Vv _ (P (2 + b))) hVQ6 hI
    refine (le_inf (le_inf hR1Z4 (hR1Z2.trans (zm_le_centralizer_qv _ hyp hc1.1))) ?_).trans key
    exact (hR1Zb.trans (S38E.zm_le_vv _ hMb1 (by simp))).trans
      (vv_le_centralizer_self h hb4 hMb1)
  ·
    apply hst0
    have key := IsChain.le_stabCenter_x1 h32 h53 h59 hmin hb4 hd hch (j := 1) (by omega)
      (by omega) (hgood 1 (by omega) (by omega)) (E := Vv _ (P (2 + b)) ⊓ Qv _ (P 4))
      inf_le_right hB
    rw [Nat.mul_one, show 2 - 2 = 0 by rfl] at key
    refine (le_inf (le_inf hR0Z2 (hR0Z0.trans (zm_le_centralizer_qv _ hyp hc0.1))) ?_).trans key
    rw [Subgroup.le_centralizer_iff]
    refine (inf_le_left.trans (vv_le_centralizer_zm h hMb1 hMb0 ?_)).trans
      (Subgroup.centralizer_le hR0Zb)
    rw [tdist_comm, hch.dist_P (by omega) (by omega)]
    omega

end S511S

end CFSG.Quasithin.MS93
