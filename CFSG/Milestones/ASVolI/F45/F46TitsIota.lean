module

public import CFSG.Milestones.ASVolI.F45.F46TitsTransfer
public import CFSG.Milestones.ASVolI.F45.TitsModel
public import CFSG.Milestones.ASVolI.F45.Lie
public import CFSG.Milestones.ASVolI.F4Reductions
public import CFSG.Milestones.ASVolI.F45.F46TitsHyp

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.TitsGeo CFSG.Quasithin.F7
  CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion CFSG.ASVolI.ChF

section Aff

variable {X V : Type*} [Group X] [MulAction X V] {Γ : SimpleGraph V}

theorem burnsideF46_aff_fix_all {a : V} {lab : ZMod 5 → V} (A : AffLab X Γ a lab) {g : X}
    (hga : g • a = a) {u w : V} (hu : Γ.Adj a u) (hw : Γ.Adj a w) (huw : u ≠ w)
    (hgu : g • u = u) (hgw : g • w = w) : ∀ t, Γ.Adj a t → g • t = t := by
  obtain ⟨a', b', -, hab⟩ := A.aff g hga
  obtain ⟨i, rfl⟩ := A.surj u hu
  obtain ⟨j, rfl⟩ := A.surj w hw
  have hij : i ≠ j := fun h => huw (by rw [h])
  have e1 : a' * i + b' = i := A.inj (by rw [← hab, hgu])
  have e2 : a' * j + b' = j := A.inj (by rw [← hab, hgw])
  obtain ⟨ha, hb⟩ := burnsideF45_aff_two_fix a' b' i j hij e1 e2
  intro t ht
  obtain ⟨k, rfl⟩ := A.surj t ht
  rw [hab, ha, hb, one_mul, add_zero]

end Aff

section Q

variable {E : Type} [Group E] {M₁ M₂ : Subgroup E}

theorem burnsideF46_Qx_le_stv {Y : Type} [Group Y] (c : Cpl M₁ M₂ Y) (p : ℕ) (Gp : Subgroup E) :
    Qx p Gp c ≤ stv c c.xv := by
  rw [stv_xv_eq_range]
  exact Subgroup.map_le_range _ _

theorem burnsideF46_Ql_le_stv {Y : Type} [Group Y] (c : Cpl M₁ M₂ Y) (p : ℕ) (Gp : Subgroup E) :
    Ql p Gp c ≤ stv c c.lv := by
  rw [burnsideF46_stv_lv_eq_map]
  exact Subgroup.map_mono le_top

end Q

section Data

variable {α : RankTwoAmalgam.{0}} {Y : Type} [Group Y] [Finite Y] {c : α.Completion Y}

theorem burnsideF46_line_compl_of_data (T : burnsideF45_TitsData c) {Q : Subgroup c.G0}
    (hQ : Q = pCoreOf 2 (stv c c.lv)) (hfix : ∀ w, c.graph.Adj c.lv w → Q ≤ stv c w) :
    ∀ q ∈ GPath.nbPaths c.graph c.lv 8,
      IsComplementIn q.stabPath Q (stv c c.lv ⊓ stv c (q 1)) := by
  intro q hq
  subst hQ
  have hfix' : ∀ w, c.graph.Adj c.lv w → ∀ g ∈ pCoreOf 2 (stv c c.lv), g • w = w :=
    fun w hw g hg => MulAction.mem_stabilizer_iff.mp (hfix w hw hg)
  have hv : c.graph.dist c.lv (q 8) = 8 := end_dist T.poly le_rfl hq
  have hc := T.line_compl hv hfix'
  have hq1 : c.graph.Adj c.lv (q 1) := burnsideF45_adj_first (by norm_num) hq
  have hle : pCoreOf 2 (stv c c.lv) ≤ stv c c.lv ⊓ stv c (q 1) :=
    le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 _) (hfix _ hq1)
  have h2 := hc.inf_left hle inf_le_left
  have e : (q.stabPath : Subgroup c.G0) =
      (stv c c.lv ⊓ stv c (q 8)) ⊓ (stv c c.lv ⊓ stv c (q 1)) := by
    ext g
    constructor
    · intro hg
      have hgl : g ∈ stv c c.lv := GPath.stabPath_le_stabilizer q hq.1 hg
      exact ⟨⟨hgl, MulAction.mem_stabilizer_iff.mpr (hg 8 le_rfl)⟩,
        ⟨hgl, MulAction.mem_stabilizer_iff.mpr (hg 1 (by norm_num))⟩⟩
    · rintro ⟨⟨hgl, hg8⟩, -, hg1⟩
      exact mem_stabPath_of_fix T.poly hq (MulAction.mem_stabilizer_iff.mp hgl)
        (MulAction.mem_stabilizer_iff.mp hg1) (MulAction.mem_stabilizer_iff.mp hg8)
  rw [e]
  exact h2

theorem burnsideF46_point_idx_of_data (T : burnsideF45_TitsData c) (TH : TitsHyp c 6)
    {Q : Subgroup c.G0} (hQ : Q = pCoreOf 2 (stv c c.xv)) (hQx : Q ≤ stv c c.xv)
    (hfix : ∀ w, c.graph.Adj c.xv w → Q ≤ stv c w) :
    ∀ q ∈ GPath.nbPaths c.graph c.xv 8,
      (q.stabPath : Subgroup c.G0) ⊓ Q = ⊥ ∧
        (Q ⊔ q.stabPath).relIndex (stv c c.xv ⊓ stv c (q 1)) = 2 := by
  intro q hq
  obtain ⟨lab, A⟩ := T.aff
  have hQk : Q = burnsideF45_nbrKer c c.xv := by
    refine le_antisymm (fun g hg => ⟨MulAction.mem_stabilizer_iff.mp (hQx hg), fun w hw =>
        MulAction.mem_stabilizer_iff.mp (hfix w hw hg)⟩) ?_
    rw [hQ]
    exact T.nbrKer_x_le
  have hq1 : c.graph.Adj c.xv (q 1) := burnsideF45_adj_first (by norm_num) hq
  have hQB : Q ≤ stv c c.xv ⊓ stv c (q 1) := le_inf hQx (hfix _ hq1)
  have hRB : (q.stabPath : Subgroup c.G0) ≤ stv c c.xv ⊓ stv c (q 1) := fun g hg =>
    ⟨GPath.stabPath_le_stabilizer q hq.1 hg, MulAction.mem_stabilizer_iff.mpr (hg 1 (by norm_num))⟩
  have hbot : (q.stabPath : Subgroup c.G0) ⊓ Q = ⊥ := by
    refine eq_bot_iff.mpr fun g hg => ?_
    have hv : c.graph.dist c.xv (q 8) = 8 := end_dist T.poly le_rfl hq
    exact (Subgroup.mem_bot).mpr (T.point_faithful hv ⟨(hRB hg.1).1,
      MulAction.mem_stabilizer_iff.mpr (hg.1 8 le_rfl)⟩
      fun w hw => MulAction.mem_stabilizer_iff.mp (hfix w hw hg.2))
  refine ⟨hbot, ?_⟩
  obtain ⟨w, hw, hwq, -⟩ := burnsideF46_hval TH c.xv (q 1) (q 1)
  have hstw : stv c w ⊓ (stv c c.xv ⊓ stv c (q 1)) = Q := by
    refine le_antisymm ?_ (le_inf (hfix w hw) hQB)
    rintro g ⟨hgw, hgx, hg1⟩
    rw [hQk]
    exact ⟨MulAction.mem_stabilizer_iff.mp hgx, burnsideF46_aff_fix_all A
      (MulAction.mem_stabilizer_iff.mp hgx) hq1 hw (Ne.symm hwq)
      (MulAction.mem_stabilizer_iff.mp hg1) (MulAction.mem_stabilizer_iff.mp hgw)⟩
  have hl1 : CosetGeom.vtype (q 1) = true := by
    have := CosetGeom.vtype_ne_of_adj hq1
    have h0 : CosetGeom.vtype c.xv = false := rfl
    rw [h0] at this
    cases h : CosetGeom.vtype (q 1)
    · exact absurd h.symm this
    · rfl
  have horb : MulAction.orbit ↥(stv c c.xv ⊓ stv c (q 1)) w = CosetGeom.nbrs c.xv \ {q 1} := by
    ext t
    constructor
    · rintro ⟨g, rfl⟩
      have hgx : (g : c.G0) • c.xv = c.xv := MulAction.mem_stabilizer_iff.mp g.2.1
      have hg1 : (g : c.G0) • q 1 = q 1 := MulAction.mem_stabilizer_iff.mp g.2.2
      refine ⟨?_, ?_⟩
      · show c.graph.Adj c.xv ((g : c.G0) • w)
        have := (GraphAction.adj_smul (g : c.G0) c.xv w).mpr hw
        rwa [hgx] at this
      · intro h
        rw [Set.mem_singleton_iff] at h
        exact hwq (smul_left_cancel _ (h.trans hg1.symm))
    · rintro ⟨ht, htq⟩
      have ht' : c.graph.Adj c.xv t := ht
      have htq' : t ≠ q 1 := htq
      have e1 : burnsideF45_edge hq1.symm 1 = c.xv := burnsideF45_edge_one hq1.symm
      obtain ⟨g, hg1, hgq, hgw⟩ := GPath.exists_fix_path_smul_eq (m := 6) (burnsideF46_hval TH)
        (TH.transLn (q 1) hl1) (i := 1) (by norm_num) (burnsideF45_edge_mem hq1.symm) (y := w)
        (y' := t) (by rw [e1]; exact hw) (by rw [e1]; exact ht') (fun _ => hwq) (fun _ => htq')
      have hgx : g • c.xv = c.xv := by
        have := congrArg (fun r : GPath c.graph 1 => r 1) hgq
        simpa [e1] using this
      exact ⟨⟨g, MulAction.mem_stabilizer_iff.mpr hgx, MulAction.mem_stabilizer_iff.mpr hg1⟩, hgw⟩
  have hQB4 : Q.relIndex (stv c c.xv ⊓ stv c (q 1)) = 4 := by
    rw [← hstw, Subgroup.inf_relIndex_right, burnsideF45_relIndex_stv, horb,
      Set.ncard_sdiff_singleton_of_mem (show q 1 ∈ CosetGeom.nbrs c.xv from hq1),
      ← Nat.card_coe_set_eq, T.card_nbrs_xv]
  haveI hnorm : (Q.subgroupOf (stv c c.xv ⊓ stv c (q 1))).Normal := by
    refine ⟨fun n hn b => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    rw [hQk] at hn ⊢
    have hbx : (b : c.G0) • c.xv = c.xv := MulAction.mem_stabilizer_iff.mp b.2.1
    have hbx' : (b : c.G0)⁻¹ • c.xv = c.xv := by
      rw [inv_smul_eq_iff, hbx]
    refine ⟨?_, fun u hu => ?_⟩
    · simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_smul, hbx', hn.1, hbx]
    · have hu' : c.graph.Adj c.xv ((b : c.G0)⁻¹ • u) := by
        have := (GraphAction.adj_smul ((b : c.G0)⁻¹) c.xv u).mpr hu
        rwa [hbx'] at this
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_smul, hn.2 _ hu', smul_inv_smul]
  have hQR : Q.relIndex (Q ⊔ q.stabPath) = 2 := by
    rw [← Subgroup.relIndex_subgroupOf (sup_le hQB hRB), Subgroup.subgroupOf_sup hQB hRB,
      Subgroup.relIndex_sup_left, Subgroup.relIndex_subgroupOf hRB,
      ← Subgroup.inf_relIndex_right, inf_comm, hbot, Subgroup.relIndex_bot_left,
      T.point_card_stabPath hq]
  have hmul := Subgroup.relIndex_mul_relIndex Q (Q ⊔ q.stabPath)
    (stv c c.xv ⊓ stv c (q 1)) le_sup_left (sup_le hQB hRB)
  rw [hQR, hQB4] at hmul
  omega

end Data

section IotaQ

variable {E : Type} [Group E] {M₁ M₂ : Subgroup E}

theorem burnsideF46_iota_Qu (hyp : HypF_4_4 .Tits 2 1 ⊤ M₁ M₂) (u : (incl M₁ M₂).Γ) :
    Qu 2 ⊤ (incl M₁ M₂) u = pCoreOf 2 (stv (incl M₁ M₂) u) := by
  have hp : Nat.Prime 2 := Nat.prime_two
  have hm : 3 ≤ GLKind.Tits.m := burnsideF45_three_le_m _
  have hN : (burnsideF45_setting hyp hp hm).N = ⊤ := by
    show (⊤ : Subgroup E).comap (toE (incl M₁ M₂)) = ⊤
    rw [Subgroup.comap_top]
  refine (burnsideF45_Qu_eq_Qbar hyp hp hm u).trans ?_
  show pCoreOf 2 ((burnsideF45_setting hyp hp hm).N ⊓ stv (incl M₁ M₂) u) = _
  rw [hN, top_inf_eq]

theorem burnsideF46_iota_Qx (hyp : HypF_4_4 .Tits 2 1 ⊤ M₁ M₂) :
    Qx 2 ⊤ (incl M₁ M₂) = pCoreOf 2 (stv (incl M₁ M₂) (incl M₁ M₂).xv) := by
  have h := Qvert_baseVert (burnsideF4b_QNormalized 2
    (inferInstance : (⊤ : Subgroup E).Normal) (incl M₁ M₂)) false
  rw [← burnsideF46_iota_Qu hyp]
  exact h.symm

theorem burnsideF46_iota_Ql (hyp : HypF_4_4 .Tits 2 1 ⊤ M₁ M₂) :
    Ql 2 ⊤ (incl M₁ M₂) = pCoreOf 2 (stv (incl M₁ M₂) (incl M₁ M₂).lv) := by
  have h := Qvert_baseVert (burnsideF4b_QNormalized 2
    (inferInstance : (⊤ : Subgroup E).Normal) (incl M₁ M₂)) true
  rw [← burnsideF46_iota_Qu hyp]
  exact h.symm

end IotaQ

section QFix


variable {E : Type} [Group E] {M₁ M₂ : Subgroup E}

theorem burnsideF46_Q_fix (hyp : HypF_4_4 .Tits 2 1 ⊤ M₁ M₂) {Y : Type} [Group Y]
    (c : Cpl M₁ M₂ Y) :
    (∀ w, c.graph.Adj c.xv w → Qx 2 ⊤ c ≤ stv c w) ∧
      (∀ w, c.graph.Adj c.lv w → Ql 2 ⊤ c ≤ stv c w) := by
  haveI : Finite E := hyp.finite
  have hP := burnsideF45_parabolics hyp.toHypF_4_4g
  have hQle := burnsideF4b_pCoreOf_le Nat.prime_two hP
  exact ⟨fun w hw => burnsideF4b_Qx_le_stv 2 inferInstance hQle.1 c hw,
    fun w hw => burnsideF4b_Ql_le_stv 2 inferInstance hQle.2 c hw⟩

end QFix

section Iota



variable {E : Type} [Group E] {M₁ M₂ : Subgroup E}

theorem burnsideF46_titsModel (hyp : HypF_4_4 .Tits 2 1 ⊤ M₁ M₂) :
    TitsModel (incl M₁ M₂) 6 := by
  haveI : Finite E := hyp.finite
  have T := burnsideF45_titsData hyp
  obtain ⟨b₀, P⟩ := T.pt
  obtain ⟨lab, A⟩ := T.aff
  obtain ⟨b₇, b₁, b₂, L⟩ := T.ln
  refine ⟨T.faithful, by have := T.qOne_eq; omega, by have := T.qTwo_eq; omega, by norm_num,
    by decide, T.transX, T.transL, fun q hq y hy hne => P.noFix T.poly hq hy hne,
    fun q hq r hr hqr y y' hy hy' => P.transPair T.poly A hq hr hqr hy hy',
    fun q hq r hr hqr y y' hy hy' => L.transPair T.poly hq hr hqr hy hy'⟩

theorem burnsideF46_q (hyp : HypF_4_4 .Tits 2 1 ⊤ M₁ M₂) :
    (RankTwoAmalgam.ofSubgroups M₁ M₂).qOne = 4 ∧ (RankTwoAmalgam.ofSubgroups M₁ M₂).qTwo = 2 := by
  haveI : Finite E := hyp.finite
  have T := burnsideF45_titsData hyp
  exact ⟨T.qOne_eq, T.qTwo_eq⟩

theorem burnsideF46_iota_line_compl (hyp : HypF_4_4 .Tits 2 1 ⊤ M₁ M₂) :
    ∀ q ∈ GPath.nbPaths (incl M₁ M₂).graph (incl M₁ M₂).lv 8,
      IsComplementIn q.stabPath (Ql 2 ⊤ (incl M₁ M₂))
        (stv (incl M₁ M₂) (incl M₁ M₂).lv ⊓ stv (incl M₁ M₂) (q 1)) := by
  haveI : Finite E := hyp.finite
  exact burnsideF46_line_compl_of_data (burnsideF45_titsData hyp) (burnsideF46_iota_Ql hyp)
    (burnsideF46_Q_fix hyp (incl M₁ M₂)).2

theorem burnsideF46_iota_point_idx (hyp : HypF_4_4 .Tits 2 1 ⊤ M₁ M₂) :
    ∀ q ∈ GPath.nbPaths (incl M₁ M₂).graph (incl M₁ M₂).xv 8,
      (q.stabPath : Subgroup (incl M₁ M₂).G0) ⊓ Qx 2 ⊤ (incl M₁ M₂) = ⊥ ∧
        (Qx 2 ⊤ (incl M₁ M₂) ⊔ q.stabPath).relIndex
          (stv (incl M₁ M₂) (incl M₁ M₂).xv ⊓ stv (incl M₁ M₂) (q 1)) = 2 := by
  haveI : Finite E := hyp.finite
  exact burnsideF46_point_idx_of_data (burnsideF45_titsData hyp)
    ((burnsideF46_titsModel hyp).titsHyp (incl_faithful M₁ M₂)) (burnsideF46_iota_Qx hyp)
    (burnsideF46_Qx_le_stv (incl M₁ M₂) 2 ⊤) (burnsideF46_Q_fix hyp (incl M₁ M₂)).1

end Iota

end CFSG.ASVolI
