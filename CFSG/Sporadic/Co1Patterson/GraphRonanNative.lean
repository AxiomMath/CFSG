module

public import CFSG.Sporadic.Co1Patterson.GraphQC
public import Certificates.Certificate21153
public import Certificates.Certificate21154
public import Certificates.Certificate21155
public import CFSG.Sporadic.Co1Patterson.GraphDist

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Sporadic.Co1Patterson

open Subgroup CFSG.Sporadic.Co1Schreier CFSG.Sporadic.Co1Block CFSG.Sporadic.SmallF2
  CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1.Module CFSG.Monster.GMS
  CFSG.Sporadic.Co1Patterson.Native CFSG.Monster.B.Recog
open CFSG.Blueprint (NativeSporadic.Co1)

theorem ronan_check2_0 : ronanCheck2 0 = true :=
  Certificates.certificate21153.1

theorem ronan_check2_1 : ronanCheck2 1 = true :=
  Certificates.certificate21153.2

theorem q2_check_0 : q2Check 0 = true :=
  Certificates.certificate21154.1

theorem q2_check_1 : q2Check 1 = true :=
  Certificates.certificate21154.2.1

theorem q2_check_2 : q2Check 2 = true :=
  Certificates.certificate21154.2.2.1

theorem q2_check_3 : q2Check 3 = true :=
  Certificates.certificate21154.2.2.2

theorem q2_check_4 : q2Check 4 = true :=
  Certificates.certificate21155.1

theorem q2_check_5 : q2Check 5 = true :=
  Certificates.certificate21155.2.1

theorem q2_check_6 : q2Check 6 = true :=
  Certificates.certificate21155.2.2

theorem ronanCheck2_true {t : ℕ} (ht : t < 2) :
    ronanCheck2 t = true := by
  interval_cases t
  · exact ronan_check2_0
  · exact ronan_check2_1

theorem q2Check_true {t : ℕ}
    (ht : t < 7) : q2Check t = true := by
  interval_cases t
  · exact q2_check_0
  · exact q2_check_1
  · exact q2_check_2
  · exact q2_check_3
  · exact q2_check_4
  · exact q2_check_5
  · exact q2_check_6


theorem dist_smul (g : NativeSporadic.Co1) (u v : Vt) :
    (a2Graph aNC).dist (g • u) (g • v) = (a2Graph aNC).dist u v := by
  have := iso_dist_eq (conjIso (t := aNC) g) u v
  rwa [conjIso_apply, conjIso_apply] at this

theorem forall_of_rep (P : Vt → Vt → Prop)
    (hP : ∀ (g : NativeSporadic.Co1) a b, P a b → P (g • a) (g • b)) (d : ℕ)
    (hrep : ∀ i < 11, distT.getD i 0 = d → P vA (rep11V i)) :
    ∀ a b, (a2Graph aNC).dist a b = d → P a b := by
  intro a b hab
  obtain ⟨x, hx⟩ := isConj_iff.1 a.2
  have ha : a = x • vA := Subtype.ext hx.symm
  subst ha
  have hd : (a2Graph aNC).dist vA (x⁻¹ • b) = d := by
    rw [← dist_smul x, smul_inv_smul]
    exact hab
  obtain ⟨i, hi, k, hk, hkb⟩ := suborbits_cover (x⁻¹ • b)
  have hdi : distT.getD i 0 = d := by
    rw [← hd, hkb, dist_vA_smul hk]
    exact (dist_rep11 hi).1.symm
  have h1 := hP k _ _ (hrep i hi hdi)
  rw [(smul_vA_eq_iff k).2 hk, ← hkb] at h1
  have h2 := hP x _ _ h1
  rwa [smul_inv_smul] at h2

theorem preconnected_image (g : NativeSporadic.Co1) {S : Set Vt}
    (h : ((a2Graph aNC).induce S).Preconnected) :
    ((a2Graph aNC).induce ((g • ·) '' S)).Preconnected := by
  let f : (a2Graph aNC).induce S →g (a2Graph aNC).induce ((g • ·) '' S) :=
    { toFun := fun x => ⟨g • x.1, x.1, x.2, rfl⟩
      map_rel' := fun h => a2Graph_adj_smul g h }
  rintro ⟨_, u, hu, rfl⟩ ⟨_, w, hw, rfl⟩
  exact (h ⟨u, hu⟩ ⟨w, hw⟩).map f

theorem ronanSet_smul (g : NativeSporadic.Co1) (a b : Vt) (n : ℕ) :
    {c | (a2Graph aNC).Adj (g • a) c ∧ (a2Graph aNC).dist c (g • b) = n} =
      (g • ·) '' {c | (a2Graph aNC).Adj a c ∧ (a2Graph aNC).dist c b = n} := by
  ext c
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨g⁻¹ • c, ⟨?_, ?_⟩, smul_inv_smul g c⟩
    · rw [← a2Graph_adj_smul_iff g, smul_inv_smul]
      exact h1
    · rw [← dist_smul g, smul_inv_smul]
      exact h2
  · rintro ⟨c', ⟨h1, h2⟩, rfl⟩
    exact ⟨a2Graph_adj_smul g h1, by rw [dist_smul]; exact h2⟩

theorem preconnected_of_treeIn {N : Set Vt} {ns ps : List ℕ} {P Q : ℕ → Bool}
    (h : treeIn orbE (ptSet orbE) ns ps P Q = true)
    (hP : ∀ k < orbE.c.pts.size, P k = true → cV k ∈ N)
    (hN : ∀ v ∈ N, ∃ k < orbE.c.pts.size, v = cV k ∧ Q k = true) :
    ((a2Graph aNC).induce N).Preconnected := by
  obtain ⟨hpos, -, hall, hcomp⟩ := treeIn_parts h
  let node : ℕ → ℕ := fun t => ns.toArray[t]!
  have hmem : ∀ t < ns.toArray.size, cV (node t) ∈ N := fun t ht =>
    hP _ (hall t ht).1 (hall t ht).2.1
  have hreach : ∀ t (ht : t < ns.toArray.size),
      ((a2Graph aNC).induce N).Reachable ⟨cV (node 0), hmem 0 hpos⟩ ⟨cV (node t), hmem t ht⟩ := by
    intro t
    induction t using Nat.strong_induction_on with
    | _ t ih =>
      intro ht
      rcases (hall t ht).2.2 with rfl | ⟨hp, hadj⟩
      · exact SimpleGraph.Reachable.refl _
      · have hk := (hall t ht).1
        have hkp := (hall _ (hp.trans ht)).1
        have hpk : ((a2Graph aNC).induce N).Adj ⟨cV (node t), hmem t ht⟩
            ⟨cV (node (ps.toArray[t]!)), hmem _ (hp.trans ht)⟩ :=
          (adj_cV_iff hk (nrep_cV hkp) (valid_pts hkp)).2 hadj
        exact (ih _ hp (hp.trans ht)).trans hpk.symm.reachable
  have hnode : ∀ v (hv : v ∈ N), ∃ t, ∃ ht : t < ns.toArray.size,
      (⟨v, hv⟩ : N) = ⟨cV (node t), hmem t ht⟩ := by
    intro v hv
    obtain ⟨k, hk, rfl, hQ⟩ := hN v hv
    obtain ⟨t, ht, hkt⟩ := List.getElem_of_mem (hcomp k hk hQ)
    refine ⟨t, by simpa using ht, Subtype.ext ?_⟩
    show cV k = cV (ns.toArray[t]!)
    rw [getElem!_pos ns.toArray t (by simpa using ht)]
    simp [hkt]
  rintro ⟨u, hu⟩ ⟨w, hw⟩
  obtain ⟨t, ht, e⟩ := hnode u hu
  obtain ⟨t', ht', e'⟩ := hnode w hw
  rw [e, e']
  exact (hreach t ht).symm.trans (hreach t' ht')

theorem d2_index : ∀ i < 11, distT.getD i 0 = 2 → ∃ t < 7, d2Reps.getD t 0 + 1 = i := by
  decide

theorem far_index : ∀ i < 11, distT.getD i 0 = 3 → ∃ t < 2, farReps.getD t 0 + 1 = i := by
  decide

theorem ronan_i_two (a b : Vt) (hab : (a2Graph aNC).dist a b = 2) :
    ((a2Graph aNC).induce
      {c | (a2Graph aNC).Adj a c ∧ (a2Graph aNC).dist c b = 2 - 1}).Preconnected := by
  refine forall_of_rep (fun a b => ((a2Graph aNC).induce
    {c | (a2Graph aNC).Adj a c ∧ (a2Graph aNC).dist c b = 2 - 1}).Preconnected) ?_ 2 ?_ a b hab
  · intro g a b h
    rw [ronanSet_smul]
    exact preconnected_image g h
  · intro i hi hdi
    obtain ⟨t, ht, rfl⟩ := d2_index i hi hdi
    rw [rep11V_succ]
    have hj := d2Reps_lt ht
    have h := ronanCheck1_parts.1 t ht
    unfold lvl2Check at h
    simp only [Bool.and_eq_true] at h
    have hB := nrep_repV hj
    have hBv := valid_repRows hj
    refine preconnected_of_treeIn h.2 (fun k hk hP => ⟨adj_vA_cV hk, ?_⟩) (fun v hv => ?_)
    · exact SimpleGraph.dist_eq_one_iff_adj.2 ((adj_cV_iff hk hB hBv).2 hP)
    · obtain ⟨k, hk, rfl⟩ := exists_cV hv.1
      exact ⟨k, hk, rfl, (adj_cV_iff hk hB hBv).1 (SimpleGraph.dist_eq_one_iff_adj.1 hv.2)⟩

theorem nrep_atK {k : ℕ} (hk : k < orbE.c.pts.size) {B : Native.Rows} {b : Vt} (hB : NRep B b)
    (hBv : CFSG.Sporadic.Co1.InvNative.validRows B = true) :
    NRep (atK orbE k B) (((xE k)⁻¹ • b : Vt) : NativeSporadic.Co1) ∧
      CFSG.Sporadic.Co1.InvNative.validRows (atK orbE k B) = true := by
  refine ⟨?_, validRows_mul (validRows_mul (valid_xeiK hk) hBv) (valid_xeK hk)⟩
  rw [coe_smul_conjVert, inv_inv]
  exact ((nrep_xEinv hk).mul hB).mul (nrep_xE hk)

theorem dist_cV_eq (k : ℕ) (b : Vt) :
    (a2Graph aNC).dist (cV k) b = (a2Graph aNC).dist vA ((xE k)⁻¹ • b) := by
  rw [← dist_smul (xE k)⁻¹]
  unfold cV
  rw [inv_smul_smul]


theorem ronanCheck2_parts {t : ℕ} (ht : t < 2) :
    treeIn orbE (ptSet orbE) (lvl3Tree t).1 (lvl3Tree t).2
      (fun k => dcls (ptSet orbE) (atK orbE k (repRows (farReps.getD t 0))) == 2)
      (fun k => dcls (ptSet orbE) (atK orbE k (repRows (farReps.getD t 0))) != 3) = true ∧
    ∀ m < orbE.c.pts.size,
      let gp := nbrX orbE (repP (farReps.getD t 0)) m
      let d := dcls (ptSet orbE) (vtxR gp.1 gp.2)
      (d == 1 || d == 2 || (d == 3 &&
        match (lvl3Wit t)[m]? with
        | some k => decide (k < orbE.c.pts.size) &&
            dcls (ptSet orbE) (atK orbE k (repRows (farReps.getD t 0))) == 2 &&
            dcls (ptSet orbE) (atK orbE k (vtxR gp.1 gp.2)) == 2
        | none => false)) = true := by
  have h := ronanCheck2_true ht
  unfold ronanCheck2 at h
  rw [Bool.and_eq_true, List.all_eq_true] at h
  exact ⟨h.1, fun m hm => h.2 m (List.mem_range.2 hm)⟩

theorem ronan_i_three (a b : Vt) (hab : (a2Graph aNC).dist a b = 3) :
    ((a2Graph aNC).induce
      {c | (a2Graph aNC).Adj a c ∧ (a2Graph aNC).dist c b = 3 - 1}).Preconnected := by
  refine forall_of_rep (fun a b => ((a2Graph aNC).induce
    {c | (a2Graph aNC).Adj a c ∧ (a2Graph aNC).dist c b = 3 - 1}).Preconnected) ?_ 3 ?_ a b hab
  · intro g a b h
    rw [ronanSet_smul]
    exact preconnected_image g h
  · intro i hi hdi
    obtain ⟨t, ht, rfl⟩ := far_index i hi hdi
    rw [rep11V_succ]
    have hj := farReps_lt ht
    have hB := nrep_repV hj
    have hBv := valid_repRows hj
    refine preconnected_of_treeIn (ronanCheck2_parts ht).1 (fun k hk hP => ⟨adj_vA_cV hk, ?_⟩)
      (fun v hv => ?_)
    · simp only [beq_iff_eq] at hP
      obtain ⟨h1, h2⟩ := nrep_atK hk hB hBv
      rw [dist_cV_eq, dist_of_dcls h1 h2 hP (by norm_num)]
    · obtain ⟨k, hk, rfl⟩ := exists_cV hv.1
      refine ⟨k, hk, rfl, ?_⟩
      simp only [bne_iff_ne, ne_eq]
      intro h3
      obtain ⟨h1, h2⟩ := nrep_atK hk hB hBv
      have := dist_of_dcls h1 h2 h3 (by norm_num)
      have h4 := hv.2
      rw [dist_cV_eq, this] at h4
      exact absurd h4 (by norm_num)

theorem ronan_ii_three (a b : Vt) (hab : (a2Graph aNC).dist a b = 3) :
    ∀ g, (a2Graph aNC).dist a g = 3 → (a2Graph aNC).Adj b g →
      ∃ c c', (a2Graph aNC).Adj a c ∧ (a2Graph aNC).dist c b = 3 - 1 ∧ (a2Graph aNC).Adj a c' ∧
        (a2Graph aNC).dist c' g = 3 - 1 ∧ (c = c' ∨ (a2Graph aNC).Adj c c') := by
  refine forall_of_rep (fun a b => ∀ g, (a2Graph aNC).dist a g = 3 → (a2Graph aNC).Adj b g →
      ∃ c c', (a2Graph aNC).Adj a c ∧ (a2Graph aNC).dist c b = 3 - 1 ∧ (a2Graph aNC).Adj a c' ∧
        (a2Graph aNC).dist c' g = 3 - 1 ∧ (c = c' ∨ (a2Graph aNC).Adj c c')) ?_ 3 ?_ a b hab
  · intro x a b h g hg hbg
    obtain ⟨c, c', h1, h2, h3, h4, h5⟩ := h (x⁻¹ • g)
      (by rw [← dist_smul x, smul_inv_smul]; exact hg)
      (by rw [← a2Graph_adj_smul_iff x, smul_inv_smul]; exact hbg)
    refine ⟨x • c, x • c', a2Graph_adj_smul x h1, by rw [dist_smul]; exact h2,
      a2Graph_adj_smul x h3, ?_, ?_⟩
    · rw [← dist_smul x⁻¹, inv_smul_smul]; exact h4
    · exact h5.imp (congrArg (x • ·)) (a2Graph_adj_smul x)
  · intro i hi hdi
    obtain ⟨t, ht, rfl⟩ := far_index i hi hdi
    rw [rep11V_succ]
    intro g hg hbg
    have hj := farReps_lt ht
    have hB := nrep_repV hj
    have hBv := valid_repRows hj
    have hbx : repV (farReps.getD t 0) = gElt (repJ (farReps.getD t 0)) • vA := repV_eq_smul _
    rw [hbx] at hbg
    obtain ⟨m, hm, rfl⟩ := exists_nbrV hbg
    have hgp := crep_nbrX (crep_rep hj) hm
    have hG := nrep_vtxR hgp.1 hgp.2.1
    have hGv := valid_vtxR hgp.2.2.1 hgp.2.2.2
    have h := (ronanCheck2_parts ht).2 m hm
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
    rcases h with (h | h) | ⟨h3, hw⟩
    · have := dist_of_dcls hG hGv h (by norm_num)
      unfold nbrV at hg
      rw [this] at hg
      exact absurd hg (by norm_num)
    · have := dist_of_dcls hG hGv h (by norm_num)
      unfold nbrV at hg
      rw [this] at hg
      exact absurd hg (by norm_num)
    · cases hk : (lvl3Wit t)[m]? with
      | none =>
        rw [hk] at hw
        exact (Bool.false_ne_true hw).elim
      | some k =>
        rw [hk] at hw
        simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hw
        obtain ⟨⟨hk', hcb⟩, hcg⟩ := hw
        refine ⟨cV k, cV k, adj_vA_cV hk', ?_, adj_vA_cV hk', ?_, Or.inl rfl⟩
        · obtain ⟨h1, h2⟩ := nrep_atK hk' hB hBv
          rw [dist_cV_eq, dist_of_dcls h1 h2 hcb (by norm_num)]
        · obtain ⟨h1, h2⟩ := nrep_atK hk' hG hGv
          rw [dist_cV_eq]
          unfold nbrV
          rw [dist_of_dcls h1 h2 hcg (by norm_num)]

theorem ronan_q2 (a b : Vt) (hab : (a2Graph aNC).dist a b = 2) :
    ∀ g, (a2Graph aNC).dist a g = 2 → (a2Graph aNC).Adj b g → Q2Good (a2Graph aNC) a b g := by
  refine forall_of_rep (fun a b => ∀ g, (a2Graph aNC).dist a g = 2 → (a2Graph aNC).Adj b g →
      Q2Good (a2Graph aNC) a b g) ?_ 2 ?_ a b hab
  · intro x a b h g hg hbg
    have h1 := h (x⁻¹ • g) (by rw [← dist_smul x, smul_inv_smul]; exact hg)
      (by rw [← a2Graph_adj_smul_iff x, smul_inv_smul]; exact hbg)
    have h2 : Q2Good (a2Graph aNC) (x • a) (x • b) (x • x⁻¹ • g) := h1.map (conjIso x).toHom
    rwa [smul_inv_smul] at h2
  · intro i hi hdi
    obtain ⟨t, ht, rfl⟩ := d2_index i hi hdi
    rw [rep11V_succ]
    intro g hg hbg
    have hj := d2Reps_lt ht
    have hB := nrep_repV hj
    have hbx : repV (d2Reps.getD t 0) = gElt (repJ (d2Reps.getD t 0)) • vA := repV_eq_smul _
    rw [hbx] at hbg
    obtain ⟨m, hm, rfl⟩ := exists_nbrV hbg
    have hgp := crep_nbrX (crep_rep hj) hm
    have hG := nrep_vtxR hgp.1 hgp.2.1
    have hGv := valid_vtxR hgp.2.2.1 hgp.2.2.2
    have h := q2Check_true ht
    unfold q2Check at h
    simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨hcent, -⟩, hlen⟩, hroots⟩, hall⟩ := h
    have hm' := hall m hm
    simp only [Bool.or_eq_true, beq_iff_eq] at hm'
    rcases hm' with (h1 | h3) | hf
    · have := dist_of_dcls hG hGv h1 (by norm_num)
      unfold nbrV at hg
      rw [this] at hg
      exact absurd hg (by norm_num)
    · have := dist_of_dcls hG hGv h3 (by norm_num)
      unfold nbrV at hg
      rw [this] at hg
      exact absurd hg (by norm_num)
    · rw [Std.HashSet.contains_ofList, List.contains_iff_mem, List.mem_flatMap] at hf
      obtain ⟨f, hf1, hf2⟩ := hf
      obtain ⟨n, hn, rfl⟩ := List.getElem_of_mem hf1
      rw [Array.mem_toList_iff, Array.mem_iff_getElem] at hf2
      obtain ⟨p, hp, hpG⟩ := hf2
      have hn' : n < (q2Roots.getD t []).length := (beq_iff_eq.1 hlen) ▸ hn
      obtain ⟨⟨hmn, hok⟩, hqc⟩ := hroots n hn'
      have hfn : (q2Forest orbE t).getD n default = (q2Forest orbE t)[n] := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn, Option.getD_some]
      rw [hfn] at hok
      have hgn := crep_nbrX (crep_rep hj) hmn
      obtain ⟨h, hh, -, -, hhp⟩ := orbOK_sound matHom hok (gensElt (gensKb.getD t []))
        (fun l hl => nrep_gensArr dagOK_true _ hl) _ (nrep_vtxR hgn.1 hgn.2.1) p hp
      have hhC := (Subgroup.closure_le _).2 (by
        rintro _ ⟨l, hl, rfl⟩
        exact mem_of_centOK hcent (fun l hl => nrep_gensArr dagOK_true _ hl) hB l hl) hh
      have hQ := qcOK_sound _ _ _ _ _ (crep_rep hj) hgn (adj_nbrV _ hmn) hqc
      have hQ' : Q2Good (a2Graph aNC) (h • vA) (h • (gElt (repJ (d2Reps.getD t 0)) • vA))
          (h • ((gElt (repJ (d2Reps.getD t 0)) * xE ((q2Roots.getD t []).getD n 0)) • vA)) :=
        hQ.map (conjIso h).toHom
      have e1 : h • vA = vA := (smul_vA_eq_iff h).2 (mem_inf.1 hhC).1
      have e2 : h • repV (d2Reps.getD t 0) = repV (d2Reps.getD t 0) :=
        (smul_eq_self_iff h _).2 (mem_inf.1 hhC).2
      have e3 : h • ((gElt (repJ (d2Reps.getD t 0)) * xE ((q2Roots.getD t []).getD n 0)) • vA) =
          nbrV (gElt (repJ (d2Reps.getD t 0))) m := by
        apply Subtype.ext
        rw [coe_smul_conjVert]
        refine NRep.unique (R := (q2Forest orbE t)[n].c.pts[p]!) hhp ?_
        rw [getElem!_pos _ p hp, hpG]
        exact hG
      rw [e1, ← hbx, e2, e3] at hQ'
      exact hQ'

theorem a2_triangulable : Triangulable (a2Graph aNC) := by
  refine triangulable_of_ronan_q2 (d := 3) dist_le_three ?_
    (fun a b g hab hag hbg => ronan_q2 a b hab g hag hbg) ?_
  · intro i hi2 hi3 a b hab
    interval_cases i
    · exact ronan_i_two a b hab
    · exact ronan_i_three a b hab
  · intro i hi3 hi3' a b g hab hag hbg
    obtain rfl : i = 3 := by omega
    exact ronan_ii_three a b hab g hag hbg

end CFSG.Sporadic.Co1Patterson
