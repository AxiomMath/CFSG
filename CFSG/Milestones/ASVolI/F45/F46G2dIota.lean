module

public import CFSG.Milestones.ASVolI.F45.F46G2dTransfer
public import CFSG.Milestones.ASVolI.F45.F46G2dLoc
public import CFSG.Milestones.ASVolI.F45.F46G2dInv
public import CFSG.Milestones.ASVolI.F45.G2d

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.TitsGeo CFSG.Quasithin.F7
  CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion CFSG.ASVolI.ChF

attribute [local instance 10000] burnsideF45_cosetAct burnsideF45_cosetSMul

section Q

variable {E : Type} [Group E] {M₁ M₂ : Subgroup E}

theorem burnsideF46_g2d_Qx_le_stv {Y : Type} [Group Y] (c : Cpl M₁ M₂ Y) (p : ℕ)
    (Gp : Subgroup E) : Qx p Gp c ≤ stv c c.xv := by
  rw [stv_xv_eq_range]
  exact Subgroup.map_le_range _ _

theorem burnsideF46_g2d_Ql_le_stv {Y : Type} [Group Y] (c : Cpl M₁ M₂ Y) (p : ℕ)
    (Gp : Subgroup E) : Ql p Gp c ≤ stv c c.lv := by
  rw [burnsideF46_g2d_stv_lv_eq_map]
  exact Subgroup.map_mono le_top

theorem burnsideF46_g2d_Qu_xv {Y : Type} [Group Y] (c : Cpl M₁ M₂ Y) (p : ℕ) {Gp : Subgroup E}
    (hN : Gp.Normal) : Qu p Gp c c.xv = Qx p Gp c :=
  Qvert_baseVert (burnsideF4b_QNormalized p hN c) false

theorem burnsideF46_g2d_Qu_lv {Y : Type} [Group Y] (c : Cpl M₁ M₂ Y) (p : ℕ) {Gp : Subgroup E}
    (hN : Gp.Normal) : Qu p Gp c c.lv = Ql p Gp c :=
  Qvert_baseVert (burnsideF4b_QNormalized p hN c) true

end Q

section Iota


variable {E : Type} [Group E] {M₁ M₂ : Subgroup E}

theorem burnsideF46_g2d_Q_fix (hyp : HypF_4_4 .G2d 2 1 ⊤ M₁ M₂) {Y : Type} [Group Y]
    (c : Cpl M₁ M₂ Y) :
    (∀ w, c.graph.Adj c.xv w → Qx 2 ⊤ c ≤ stv c w) ∧
      (∀ w, c.graph.Adj c.lv w → Ql 2 ⊤ c ≤ stv c w) := by
  haveI : Finite E := hyp.finite
  obtain ⟨K, fK, finK, hK, π, h1, h2⟩ := burnsideF45_g2d_chart hyp.toHypF_4_4g
  letI := fK
  have hP := burnsideF45_g2d_isLie hK π h1 h2
  have hQle := burnsideF4b_pCoreOf_le Nat.prime_two hP
  exact ⟨fun w hw => burnsideF4b_Qx_le_stv 2 inferInstance hQle.1 c hw,
    fun w hw => burnsideF4b_Ql_le_stv 2 inferInstance hQle.2 c hw⟩

theorem burnsideF46_g2d_poly (hyp : HypF_4_4 .G2d 2 1 ⊤ M₁ M₂) :
    IsGenPolygon (incl M₁ M₂).graph 6 :=
  burnsideF4gG2Two_polygon_derived hyp

theorem burnsideF46_g2d_iota_line_compl (hyp : HypF_4_4 .G2d 2 1 ⊤ M₁ M₂) :
    ∀ q : GPath (incl M₁ M₂).graph 6, q ∈ GPath.nbPaths (incl M₁ M₂).graph (incl M₁ M₂).lv 6 →
      IsComplementIn q.stabPath (Ql 2 ⊤ (incl M₁ M₂))
        (stv (incl M₁ M₂) (incl M₁ M₂).lv ⊓ stv (incl M₁ M₂) (q 1)) := by
  intro q hq
  obtain ⟨-, -, h9⟩ := burnsideF45_excKind_G2d 2 1 E ⊤ M₁ M₂ hyp
  have hpoly := burnsideF46_g2d_poly hyp
  have hv : (incl M₁ M₂).graph.dist (incl M₁ M₂).lv (q 6) = 6 :=
    CFSG.Quasithin.D4Hex.end_dist hpoly le_rfl hq
  have hc := (h9 (incl M₁ M₂).lv (q 6) hv).1 rfl
  rw [burnsideF46_g2d_Qu_lv (incl M₁ M₂) 2 inferInstance] at hc
  have hfix := (burnsideF46_g2d_Q_fix hyp (incl M₁ M₂)).2
  have hq1 : (incl M₁ M₂).graph.Adj (incl M₁ M₂).lv (q 1) := burnsideF45_adj_first (by norm_num) hq
  have hle : Ql 2 ⊤ (incl M₁ M₂) ≤ stv (incl M₁ M₂) (incl M₁ M₂).lv ⊓ stv (incl M₁ M₂) (q 1) :=
    le_inf (burnsideF46_g2d_Ql_le_stv _ 2 ⊤) (hfix _ hq1)
  have h2 := hc.inf_left hle inf_le_left
  have e : (q.stabPath : Subgroup (incl M₁ M₂).G0) =
      (stv (incl M₁ M₂) (incl M₁ M₂).lv ⊓ stv (incl M₁ M₂) (q 6)) ⊓
        (stv (incl M₁ M₂) (incl M₁ M₂).lv ⊓ stv (incl M₁ M₂) (q 1)) := by
    ext g
    constructor
    · intro hg
      have hgl : g ∈ stv (incl M₁ M₂) (incl M₁ M₂).lv := GPath.stabPath_le_stabilizer q hq.1 hg
      exact ⟨⟨hgl, MulAction.mem_stabilizer_iff.mpr (hg 6 le_rfl)⟩,
        ⟨hgl, MulAction.mem_stabilizer_iff.mpr (hg 1 (by norm_num))⟩⟩
    · rintro ⟨⟨hgl, hg6⟩, -, hg1⟩
      exact CFSG.Quasithin.D4Hex.mem_stabPath_of_fix hpoly hq (MulAction.mem_stabilizer_iff.mp hgl)
        (MulAction.mem_stabilizer_iff.mp hg1) (MulAction.mem_stabilizer_iff.mp hg6)
  rw [e]
  exact h2

theorem burnsideF46_g2d_iota_point_card (hyp : HypF_4_4 .G2d 2 1 ⊤ M₁ M₂) :
    ∀ q : GPath (incl M₁ M₂).graph 6, q ∈ GPath.nbPaths (incl M₁ M₂).graph (incl M₁ M₂).xv 6 →
      Nat.card (q.stabPath : Subgroup (incl M₁ M₂).G0) = 1 := by
  intro q hq
  obtain ⟨-, h8, h9⟩ := burnsideF45_excKind_G2d 2 1 E ⊤ M₁ M₂ hyp
  refine burnsideF46_g2d_point_card_of (burnsideF46_g2d_poly hyp) h8.1 ?_ (fun v hv => ?_) hq
  · rw [Nat.card_coe_set_eq]
    exact burnsideF45_g2d_three hyp _
  · rcases (h9 _ v hv).2 rfl with h | h
    · obtain ⟨e⟩ := h
      left
      rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
    · obtain ⟨e⟩ := h
      right
      rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_multiplicative,
        ZMod.card]

theorem burnsideF46_g2d_iota_edge_pGroup (hyp : HypF_4_4 .G2d 2 1 ⊤ M₁ M₂)
    {w : (incl M₁ M₂).Γ} (hw : (incl M₁ M₂).graph.Adj (incl M₁ M₂).xv w) :
    IsPGroup 2 ↥(stv (incl M₁ M₂) (incl M₁ M₂).xv ⊓ stv (incl M₁ M₂) w) := by
  haveI : Finite E := hyp.finite
  obtain ⟨K, fK, finK, hK, π, h1, h2⟩ := burnsideF45_g2d_chart hyp.toHypF_4_4g
  letI := fK
  have hB := burnsideF45_g2d_borel_pGroup hK π h1 h2
  have hbij := burnsideF45_toE_bijective hyp.gen
  have hBι : IsPGroup 2 ↥(stv (incl M₁ M₂) (incl M₁ M₂).xv ⊓ stv (incl M₁ M₂) (incl M₁ M₂).lv) := by
    have e : stv (incl M₁ M₂) (incl M₁ M₂).xv ⊓ stv (incl M₁ M₂) (incl M₁ M₂).lv =
        (M₁ ⊓ M₂).comap (toE (incl M₁ M₂)) := by
      ext g
      exact burnsideF45_g2d_mem_flag g
    rw [e]
    exact hB.comap_of_injective _ hbij.1
  obtain ⟨k, hk1, hk2⟩ := CosetGeom.stab_transitive_on_nbrs
    (show (incl M₁ M₂).lv ∈ CosetGeom.nbrs (incl M₁ M₂).xv from CosetGeom.adj_γ₀_γ₁) hw
  have hkx : k • (incl M₁ M₂).xv = (incl M₁ M₂).xv := CosetGeom.smul_eq_of_mem_stab hk1
  have e : stv (incl M₁ M₂) (incl M₁ M₂).xv ⊓ stv (incl M₁ M₂) w =
      conjSub k (stv (incl M₁ M₂) (incl M₁ M₂).xv ⊓ stv (incl M₁ M₂) (incl M₁ M₂).lv) := by
    rw [conjSub_inf, ← stv_smul, ← stv_smul, hkx, hk2]
  rw [e]
  exact hBι.map _

theorem burnsideF46_g2d_iota_relIndex (hyp : HypF_4_4 .G2d 2 1 ⊤ M₁ M₂)
    {w : (incl M₁ M₂).Γ} (hw : (incl M₁ M₂).graph.Adj (incl M₁ M₂).xv w) :
    (Qx 2 ⊤ (incl M₁ M₂)).relIndex (stv (incl M₁ M₂) (incl M₁ M₂).xv ⊓ stv (incl M₁ M₂) w) = 2 := by
  haveI : Finite E := hyp.finite
  obtain ⟨h6, -, -⟩ := burnsideF45_excKind_G2d 2 1 E ⊤ M₁ M₂ hyp
  obtain ⟨-, -, htr, hker, hcard⟩ := h6 (incl M₁ M₂).xv w hw
  rw [burnsideF46_g2d_Qu_xv (incl M₁ M₂) 2 inferInstance] at hker
  have hB := burnsideF46_g2d_iota_edge_pGroup hyp hw
  have hoP : oPPrime 2 (stv (incl M₁ M₂) (incl M₁ M₂).xv ⊓ stv (incl M₁ M₂) w) =
      stv (incl M₁ M₂) (incl M₁ M₂).xv ⊓ stv (incl M₁ M₂) w :=
    le_antisymm (burnsideF45_g2d_oPPrime_le _) (burnsideF45_g2d_le_oPPrime hB)
  rw [hoP] at htr hker
  have hthick := burnsideF45_q_G2d hyp rfl
  have hval := burnsideF4a_hval (incl_faithful M₁ M₂) (by rw [hthick.1]) (by rw [hthick.2])
  obtain ⟨w', hw', hw'w, -⟩ := hval (incl M₁ M₂).xv w w
  have hcard2 : Nat.card ↥(CosetGeom.nbrs (incl M₁ M₂).xv \ {w}) = 2 := by
    rw [hcard]
    exact hthick.1
  exact burnsideF46_g2d_relIndex_of (burnsideF46_g2d_Qx_le_stv _ 2 ⊤)
    (burnsideF46_g2d_Q_fix hyp (incl M₁ M₂)).1 hw htr hker hcard2 ⟨hw', hw'w⟩

end Iota

section Data


variable {E : Type} [Group E] {M₁ M₂ : Subgroup E}

theorem burnsideF46_g2d_data (hyp : HypF_4_4 .G2d 2 1 ⊤ M₁ M₂) {Y : Type} [Group Y]
    (β : Cpl M₁ M₂ Y) (hβ : β.IsFaithful) :
    burnsideF46_g2d_Data β (Qx 2 ⊤ β) (Ql 2 ⊤ β) := by
  obtain ⟨-, h8, -⟩ := burnsideF45_excKind_G2d 2 1 E ⊤ M₁ M₂ hyp
  have hι := incl_faithful M₁ M₂
  have hthick := burnsideF45_q_G2d hyp rfl
  have hfix := burnsideF46_g2d_Q_fix hyp β
  have hidx : ∀ q ∈ GPath.nbPaths (incl M₁ M₂).graph (incl M₁ M₂).xv 6,
      (q.stabPath : Subgroup (incl M₁ M₂).G0) ⊓ Qx 2 ⊤ (incl M₁ M₂) = ⊥ ∧
        (Qx 2 ⊤ (incl M₁ M₂) ⊔ q.stabPath).relIndex
          (stv (incl M₁ M₂) (incl M₁ M₂).xv ⊓ stv (incl M₁ M₂) (q 1)) = 2 := by
    intro q hq
    have hbot : (q.stabPath : Subgroup (incl M₁ M₂).G0) = ⊥ :=
      Subgroup.eq_bot_of_card_eq _ (burnsideF46_g2d_iota_point_card hyp q hq)
    rw [hbot, bot_inf_eq, sup_bot_eq]
    exact ⟨rfl, burnsideF46_g2d_iota_relIndex hyp (burnsideF45_adj_first (by norm_num) hq)⟩
  exact
    { faithful := hβ
      qOne := hthick.1
      qTwo := hthick.2
      transX := pathTrans_xv_transfer β hβ (incl M₁ M₂) hι 6 h8.1
      transL := pathTrans_lv_transfer β hβ (incl M₁ M₂) hι 5 h8.2.1
      qn := burnsideF4b_QNormalized 2 inferInstance β
      qx_le := burnsideF46_g2d_Qx_le_stv β 2 ⊤
      ql_le := burnsideF46_g2d_Ql_le_stv β 2 ⊤
      fix_x := hfix.1
      fix_l := hfix.2
      compl_l := fun q hq => burnsideF4b_transfer_l hβ hι (by norm_num) _
        (burnsideF46_g2d_iota_line_compl hyp) hq
      idx_x := fun q hq => burnsideF46_g2d_transfer_x_idx hβ hι (by norm_num) _ 2 hidx hq
      card_x := fun q hq => burnsideF46_g2d_transfer_x_card hβ hι 1 (by norm_num)
        (burnsideF46_g2d_iota_point_card hyp) hq
      invol_x := fun g hg hg2 w hw => burnsideF46_g2d_invol_fix hyp.toHypF_4_4g β hβ hg hg2 hw
      two_orb := burnsideF46_g2d_twoOrb_transfer_l hβ hι h8.2.2.1 }

end Data

end CFSG.ASVolI
