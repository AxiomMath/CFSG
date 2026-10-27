module

public import CFSG.Sporadic.Co1Patterson.GraphPoints
public import CFSG.Sporadic.Co1Patterson.GraphRonan

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Sporadic.Co1Patterson

open Subgroup CFSG.Sporadic.Co1Schreier CFSG.Sporadic.Co1Block CFSG.Sporadic.SmallF2
  CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1.Module CFSG.Monster.GMS
  CFSG.Sporadic.Co1Patterson.Native
open CFSG.Blueprint (NativeSporadic.Co1)

@[expose] def distT : List ℕ := [0, 2, 1, 2, 2, 2, 3, 2, 2, 3, 2]

theorem nrep_pows {M : Native.Rows} {m : NativeSporadic.Co1} (h : NRep M m) :
    NRep (Native.mul M M) (m ^ 2) ∧ NRep (Native.mul (Native.mul M M) M) (m ^ 3) ∧
    NRep (Native.mul (Native.mul (Native.mul M M) M) M) (m ^ 4) ∧
    NRep (Native.mul (Native.mul (Native.mul (Native.mul M M) M) M) M) (m ^ 5) ∧
    NRep (Native.mul (Native.mul (Native.mul (Native.mul (Native.mul M M) M) M) M) M)
      (m ^ 6) := by
  have e : ∀ n : ℕ, m ^ (n + 1) = m ^ n * m := fun n => pow_succ (M := NativeSporadic.Co1) m n
  have h2 : NRep (Native.mul M M) (m ^ 2) := by
    rw [e 1, pow_one]; exact h.mul h
  have h3 : NRep (Native.mul (Native.mul M M) M) (m ^ 3) := by rw [e 2]; exact h2.mul h
  have h4 : NRep (Native.mul (Native.mul (Native.mul M M) M) M) (m ^ 4) := by
    rw [e 3]; exact h3.mul h
  have h5 : NRep (Native.mul (Native.mul (Native.mul (Native.mul M M) M) M) M) (m ^ 5) := by
    rw [e 4]; exact h4.mul h
  have h6 : NRep (Native.mul (Native.mul (Native.mul (Native.mul (Native.mul M M) M) M) M) M)
      (m ^ 6) := by
    rw [e 5]; exact h5.mul h
  exact ⟨h2, h3, h4, h5, h6⟩

theorem rows_eq_one_iff {P : Native.Rows} {p : NativeSporadic.Co1} (h : NRep P p)
    (hv : CFSG.Sporadic.Co1.InvNative.validRows P = true) : P = Native.one ↔ p = 1 := by
  constructor
  · rintro rfl
    exact NRep.unique h NRep.one'
  · rintro rfl
    exact NRep.rows_eq h NRep.one' hv validRows_one

theorem orderOf_of_ord6 {M : Native.Rows} {m : NativeSporadic.Co1} (h : NRep M m)
    (hv : CFSG.Sporadic.Co1.InvNative.validRows M = true) {o : ℕ} (ho : ord6 M = o)
    (h1 : 1 ≤ o) : orderOf m = o := by
  obtain ⟨h2, h3, h4, h5, h6⟩ := nrep_pows h
  have v2 := validRows_mul hv hv
  have v3 := validRows_mul v2 hv
  have v4 := validRows_mul v3 hv
  have v5 := validRows_mul v4 hv
  have v6 := validRows_mul v5 hv
  have e1 := rows_eq_one_iff h hv
  have e2 := rows_eq_one_iff h2 v2
  have e3 := rows_eq_one_iff h3 v3
  have e4 := rows_eq_one_iff h4 v4
  have e5 := rows_eq_one_iff h5 v5
  have e6 := rows_eq_one_iff h6 v6
  rw [← pow_one m] at e1
  unfold ord6 at ho
  simp only [beq_iff_eq] at ho
  rw [orderOf_eq_iff (by omega)]
  split_ifs at ho with c1 c2 c3 c4 c5 c6 <;> subst ho
  · exact ⟨e1.1 c1, fun j hj hj0 => by omega⟩
  · refine ⟨e2.1 c2, fun j hj hj0 => ?_⟩
    interval_cases j
    exact fun h' => c1 (e1.2 h')
  · refine ⟨e3.1 c3, fun j hj hj0 => ?_⟩
    interval_cases j
    · exact fun h' => c1 (e1.2 h')
    · exact fun h' => c2 (e2.2 h')
  · refine ⟨e4.1 c4, fun j hj hj0 => ?_⟩
    interval_cases j
    · exact fun h' => c1 (e1.2 h')
    · exact fun h' => c2 (e2.2 h')
    · exact fun h' => c3 (e3.2 h')
  · refine ⟨e5.1 c5, fun j hj hj0 => ?_⟩
    interval_cases j
    · exact fun h' => c1 (e1.2 h')
    · exact fun h' => c2 (e2.2 h')
    · exact fun h' => c3 (e3.2 h')
    · exact fun h' => c4 (e4.2 h')
  · refine ⟨e6.1 c6, fun j hj hj0 => ?_⟩
    interval_cases j
    · exact fun h' => c1 (e1.2 h')
    · exact fun h' => c2 (e2.2 h')
    · exact fun h' => c3 (e3.2 h')
    · exact fun h' => c4 (e4.2 h')
    · exact fun h' => c5 (e5.2 h')
  · omega

theorem exists_adj_adj_of_dist_two {V : Type*} {G : SimpleGraph V} {u w : V}
    (hr : G.Reachable u w) (h : G.dist u w = 2) : ∃ c, G.Adj u c ∧ G.Adj c w := by
  obtain ⟨q, hq⟩ := hr.exists_walk_length_eq_dist
  rw [h] at hq
  cases q with
  | nil => simp at hq
  | @cons _ c _ hac q =>
    cases q with
    | nil => simp at hq
    | @cons _ d _ hcd q =>
      cases q with
      | nil => exact ⟨c, hac, hcd⟩
      | cons _ q => simp at hq

theorem treeIn_parts {o : Orb} {S : Std.HashSet (Array ℕ)} {ns ps : List ℕ} {P Q : ℕ → Bool}
    (h : treeIn o S ns ps P Q = true) :
    0 < ns.toArray.size ∧ ps.toArray.size = ns.toArray.size ∧
    (∀ t < ns.toArray.size, ns.toArray[t]! < o.c.pts.size ∧ P ns.toArray[t]! = true ∧
      (t = 0 ∨ (ps.toArray[t]! < t ∧ adjC S (xeK o ns.toArray[t]!) (xeiK o ns.toArray[t]!)
        o.c.pts[ns.toArray[ps.toArray[t]!]!]! = true))) ∧
    ∀ k < o.c.pts.size, Q k = true → k ∈ ns := by
  unfold treeIn at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨hpos, hps⟩, hall⟩, hcomp⟩ := h
  refine ⟨hpos, hps, fun t ht => ?_, fun k hk hQ => ?_⟩
  · obtain ⟨⟨h1, h2⟩, h3⟩ := hall t ht
    exact ⟨h1, h2, h3.imp_right fun h => ⟨h.1, h.2⟩⟩
  · have := hcomp k hk
    rw [hQ] at this
    simp only [Std.HashSet.contains_ofList, List.contains_iff_mem] at this
    exact this.resolve_left (by decide)


theorem adj_vA_iff_contains {V : Native.Rows} {v : Vt} (hV : NRep V v)
    (hVv : CFSG.Sporadic.Co1.InvNative.validRows V = true) :
    (a2Graph aNC).Adj vA v ↔ (ptSet orbE).contains V = true := by
  rw [a2_adj_vA_iff, mem_cOrb_iff_of_exactOK exact_orbE vE nrep_eRows, ptSet_contains_iff]
  constructor
  · rintro ⟨i, hi, hpi⟩
    exact ⟨i, hi, NRep.rows_eq hpi hV (valid_pts hi) hVv⟩
  · rintro ⟨i, hi, hpi⟩
    exact ⟨i, hi, hpi ▸ hV⟩

theorem eq_vA_iff {V : Native.Rows} {v : Vt} (hV : NRep V v)
    (hVv : CFSG.Sporadic.Co1.InvNative.validRows V = true) : v = vA ↔ V = iotaARows := by
  constructor
  · rintro rfl
    exact NRep.rows_eq hV nrep_aNC hVv twoA_misc_parts.2.2.2.2.2.1
  · rintro rfl
    exact Subtype.ext (NRep.unique hV nrep_aNC)

theorem valid_repRows {j : ℕ} (hj : j < 10) :
    CFSG.Sporadic.Co1.InvNative.validRows (repRows j) = true := by
  have := dagOK_parts dagOK_true
  exact validRows_mul (validRows_mul (this.2 _ (repJ_mem hj).1 (repJ_mem hj).2).1
    twoA_misc_parts.2.2.2.2.2.1) (this.2 _ (repJ_mem hj).1 (repJ_mem hj).2).2.1

theorem ronanCheck1_parts :
    (∀ t < 7, lvl2Check orbE (ptSet orbE) t = true) ∧
      ∀ t < 2, farCheck orbE (ptSet orbE) t = true := by
  have h := ronan_check1
  unfold ronanCheck1 at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  exact ⟨h.1.2, h.2⟩

theorem d2Reps_lt {t : ℕ} (ht : t < 7) : d2Reps.getD t 0 < 10 := by
  interval_cases t <;> decide

theorem farReps_lt {t : ℕ} (ht : t < 2) : farReps.getD t 0 < 10 := by
  interval_cases t <;> decide

theorem dist_d2 {t : ℕ} (ht : t < 7) :
    (a2Graph aNC).dist vA (repV (d2Reps.getD t 0)) = 2 ∧
      (a2Graph aNC).Reachable vA (repV (d2Reps.getD t 0)) := by
  have h := ronanCheck1_parts.1 t ht
  unfold lvl2Check at h
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨hne, hnc⟩, htree⟩ := h
  have hB := nrep_repV (d2Reps_lt ht)
  have hBv := valid_repRows (d2Reps_lt ht)
  have hb_ne : repV (d2Reps.getD t 0) ≠ vA := fun e => hne ((eq_vA_iff hB hBv).1 e)
  have hb_nadj : ¬ (a2Graph aNC).Adj vA (repV (d2Reps.getD t 0)) := fun e => by
    rw [adj_vA_iff_contains hB hBv, hnc] at e
    exact Bool.false_ne_true e
  obtain ⟨hpos, -, hall, -⟩ := treeIn_parts htree
  obtain ⟨hk, hP, -⟩ := hall 0 hpos
  have hc := (adj_cV_iff hk hB hBv).2 hP
  let p : (a2Graph aNC).Walk vA (repV (d2Reps.getD t 0)) := .cons (adj_vA_cV hk) (.cons hc .nil)
  exact ⟨dist_eq_two_of_walk p rfl hb_ne.symm hb_nadj, p.reachable⟩

theorem dist_far {t : ℕ} (ht : t < 2) :
    (a2Graph aNC).dist vA (repV (farReps.getD t 0)) = 3 ∧
      (a2Graph aNC).Reachable vA (repV (farReps.getD t 0)) := by
  have h := ronanCheck1_parts.2 t ht
  unfold farCheck at h
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true', decide_eq_true_eq,
    List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨hne, hnc⟩, hnone⟩, hi⟩, hm⟩, hz⟩ := h
  have hB := nrep_repV (farReps_lt ht)
  have hBv := valid_repRows (farReps_lt ht)
  have hb_ne : repV (farReps.getD t 0) ≠ vA := fun e => hne ((eq_vA_iff hB hBv).1 e)
  have hb_nadj : ¬ (a2Graph aNC).Adj vA (repV (farReps.getD t 0)) := fun e => by
    rw [adj_vA_iff_contains hB hBv, hnc] at e
    exact Bool.false_ne_true e
  obtain ⟨hz1, hz2⟩ := nrep_nbrX (nrep_xE hi) (nrep_xEinv hi) hm
  obtain ⟨hv1, hv2⟩ := valid_nbrX (valid_xeK hi) (valid_xeiK hi) hm
  have hzb : (a2Graph aNC).Adj (nbrV (xE (farPath.getD t (0, 0)).1) (farPath.getD t (0, 0)).2)
      (repV (farReps.getD t 0)) :=
    (adj_iff_adjC hz1 hz2 hB hv1 hv2 hBv).2 hz
  have hr : (a2Graph aNC).Reachable vA (repV (farReps.getD t 0)) :=
    ((adj_vA_cV hi).reachable.trans (adj_nbrV _ hm).reachable).trans hzb.reachable
  refine ⟨le_antisymm ?_ ?_, hr⟩
  · exact SimpleGraph.dist_le (.cons (adj_vA_cV hi) (.cons (adj_nbrV _ hm) (.cons hzb .nil)))
  · by_contra hlt
    have h0 : (a2Graph aNC).dist vA (repV (farReps.getD t 0)) ≠ 0 := fun e =>
      hb_ne ((hr.dist_eq_zero_iff).1 e).symm
    have h1 : (a2Graph aNC).dist vA (repV (farReps.getD t 0)) ≠ 1 := fun e =>
      hb_nadj (SimpleGraph.dist_eq_one_iff_adj.1 e)
    have h2 : (a2Graph aNC).dist vA (repV (farReps.getD t 0)) = 2 := by omega
    obtain ⟨c, hac, hcb⟩ := exists_adj_adj_of_dist_two hr h2
    obtain ⟨k, hk, hck⟩ := exists_cV hac
    rw [hck] at hcb
    have h4 : (true : Bool) = false := ((adj_cV_iff hk hB hBv).1 hcb).symm.trans (hnone k hk)
    exact Bool.noConfusion h4

theorem dist_rep11 {i : ℕ} (hi : i < 11) :
    (a2Graph aNC).dist vA (rep11V i) = distT.getD i 0 ∧ (a2Graph aNC).Reachable vA (rep11V i) := by
  have hd2 : ∀ t < 7, (a2Graph aNC).dist vA (repV (d2Reps.getD t 0)) = 2 ∧
      (a2Graph aNC).Reachable vA (repV (d2Reps.getD t 0)) := fun t ht => dist_d2 ht
  have hfar : ∀ t < 2, (a2Graph aNC).dist vA (repV (farReps.getD t 0)) = 3 ∧
      (a2Graph aNC).Reachable vA (repV (farReps.getD t 0)) := fun t ht => dist_far ht
  interval_cases i
  · rw [rep11V_zero]
    exact ⟨SimpleGraph.dist_self, SimpleGraph.Reachable.refl _⟩
  · rw [rep11V_succ]; exact hd2 0 (by norm_num)
  · rw [rep11V_succ]
    exact ⟨SimpleGraph.dist_eq_one_iff_adj.2 a2_adj_vA_vE, a2_adj_vA_vE.reachable⟩
  · rw [rep11V_succ]; exact hd2 1 (by norm_num)
  · rw [rep11V_succ]; exact hd2 2 (by norm_num)
  · rw [rep11V_succ]; exact hd2 3 (by norm_num)
  · rw [rep11V_succ]; exact hfar 0 (by norm_num)
  · rw [rep11V_succ]; exact hd2 4 (by norm_num)
  · rw [rep11V_succ]; exact hd2 5 (by norm_num)
  · rw [rep11V_succ]; exact hfar 1 (by norm_num)
  · rw [rep11V_succ]; exact hd2 6 (by norm_num)

theorem dist_vA_smul {k : NativeSporadic.Co1}
    (hk : k ∈ centralizer ({aNC} : Set NativeSporadic.Co1)) (v : Vt) :
    (a2Graph aNC).dist vA (k • v) = (a2Graph aNC).dist vA v := by
  have := iso_dist_eq (conjIso (t := aNC) k) vA v
  rw [conjIso_apply, conjIso_apply, (smul_vA_eq_iff k).2 hk] at this
  exact this

theorem reachable_vA_smul {k : NativeSporadic.Co1}
    (hk : k ∈ centralizer ({aNC} : Set NativeSporadic.Co1)) {v : Vt}
    (h : (a2Graph aNC).Reachable vA v) : (a2Graph aNC).Reachable vA (k • v) := by
  have := h.map (conjIso (t := aNC) k).toHom
  have e1 : (conjIso (t := aNC) k).toHom vA = vA := by
    show k • vA = vA
    exact (smul_vA_eq_iff k).2 hk
  have e2 : (conjIso (t := aNC) k).toHom v = k • v := rfl
  rwa [e1, e2] at this

theorem dist_vA_eq {i : ℕ} (hi : i < 11) {v : Vt} (hv : v ∈ cOrb (rep11V i)) :
    (a2Graph aNC).dist vA v = distT.getD i 0 ∧ (a2Graph aNC).Reachable vA v := by
  obtain ⟨k, hk, rfl⟩ := hv
  rw [dist_vA_smul hk]
  exact ⟨(dist_rep11 hi).1, reachable_vA_smul hk (dist_rep11 hi).2⟩

theorem a2_preconnected : (a2Graph aNC).Preconnected := by
  have hr : ∀ v : Vt, (a2Graph aNC).Reachable vA v := fun v => by
    obtain ⟨i, hi, hv⟩ := suborbits_cover v
    exact (dist_vA_eq hi hv).2
  exact fun u v => (hr u).symm.trans (hr v)

theorem distT_le : ∀ i < 11, distT.getD i 0 ≤ 3 := by decide

theorem dist_le_three (u v : Vt) : (a2Graph aNC).dist u v ≤ 3 := by
  obtain ⟨x, hx⟩ := isConj_iff.1 u.2
  have hu : u = x • vA := Subtype.ext hx.symm
  have := iso_dist_eq (conjIso (t := aNC) x⁻¹) u v
  rw [conjIso_apply, conjIso_apply] at this
  rw [← this, hu, inv_smul_smul]
  obtain ⟨i, hi, hv⟩ := suborbits_cover (x⁻¹ • v)
  rw [(dist_vA_eq hi hv).1]
  exact distT_le i hi

theorem distT_of_ord2 : ∀ i < 11, i ≠ 0 → i ≠ 2 →
    ((tableCode i).1 = 2 ∨ (tableCode i).1 = 4 ∨ (tableCode i).1 = 6) → distT.getD i 0 = 2 := by
  decide

theorem distT_of_ord3_12 : ∀ i < 11, (tableCode i).1 = 3 → (tableCode i).2.2.2 = 2 ^ 12 →
    distT.getD i 0 = 2 := by
  decide

theorem distT_of_ord5 : ∀ i < 11, (tableCode i).1 = 5 → distT.getD i 0 = 3 := by
  decide

theorem distT_of_ord3_8 : ∀ i < 11, (tableCode i).1 = 3 → (tableCode i).2.2.2 = 2 ^ 8 →
    distT.getD i 0 = 3 := by
  decide

theorem eq_vA_of_mem_cOrb {v : Vt} (h : v ∈ cOrb vA) : v = vA := by
  obtain ⟨k, hk, rfl⟩ := h
  exact (smul_vA_eq_iff k).2 hk

theorem dist_of_dcls {V : Native.Rows} {v : Vt} (hV : NRep V v)
    (hVv : CFSG.Sporadic.Co1.InvNative.validRows V = true) {d : ℕ}
    (h : dcls (ptSet orbE) V = d) (hd : d ≤ 3) : (a2Graph aNC).dist vA v = d := by
  have hM : NRep (Native.mul iotaARows V) (aNC * v) := nrep_aNC.mul hV
  have hMv := validRows_mul twoA_misc_parts.2.2.2.2.2.1 hVv
  have hfixM : ∀ e, fixDimIs (Native.mul iotaARows V) e = true → fixA v = 2 ^ e := fun e he => by
    unfold fixA
    rw [show matHom (aNC * (v : NativeSporadic.Co1)) = rowsMatrix 24 (Native.mul iotaARows V)
      from hM]
    exact ncard_fix_of_fixDimIs he
  unfold dcls at h
  by_cases h0 : V = iotaARows
  · rw [ite_eq_left (by simpa using h0)] at h
    subst h
    rw [(eq_vA_iff hV hVv).2 h0, SimpleGraph.dist_self]
  rw [ite_eq_right (by simpa using h0)] at h
  by_cases h1 : (ptSet orbE).contains V = true
  · rw [ite_eq_left h1] at h
    subst h
    exact SimpleGraph.dist_eq_one_iff_adj.2 ((adj_vA_iff_contains hV hVv).2 h1)
  rw [ite_eq_right h1] at h
  obtain ⟨i, hi, hv⟩ := suborbits_cover v
  have hcode := (vCode_eq_of_mem hv).trans (vCode_rep11 hi)
  rw [vCode_eq] at hcode
  have hord : ∀ o, ord6 (Native.mul iotaARows V) = o → 1 ≤ o → (tableCode i).1 = o :=
    fun o ho h1o => by
      rw [← hcode]
      exact orderOf_of_ord6 hM hMv ho h1o
  have hfixT : ∀ e, fixDimIs (Native.mul iotaARows V) e = true → (tableCode i).2.2.2 = 2 ^ e :=
    fun e he => by rw [← hcode]; exact hfixM e he
  have hi0 : i ≠ 0 := by
    rintro rfl
    rw [rep11V_zero] at hv
    exact h0 ((eq_vA_iff hV hVv).1 (eq_vA_of_mem_cOrb hv))
  have hi2 : i ≠ 2 := by
    rintro rfl
    rw [rep11V_two] at hv
    exact h1 ((adj_vA_iff_contains hV hVv).1 ((a2_adj_vA_iff v).2 hv))
  rw [(dist_vA_eq hi hv).1]
  set o := ord6 (Native.mul iotaARows V) with ho
  by_cases c246 : (o == 2 || o == 4 || o == 6) = true
  · rw [ite_eq_left c246] at h
    subst h
    simp only [Bool.or_eq_true, beq_iff_eq] at c246
    refine distT_of_ord2 i hi hi0 hi2 ?_
    rcases c246 with (c | c) | c
    · exact Or.inl (hord 2 c (by norm_num))
    · exact Or.inr (Or.inl (hord 4 c (by norm_num)))
    · exact Or.inr (Or.inr (hord 6 c (by norm_num)))
  rw [ite_eq_right c246] at h
  by_cases c5 : (o == 5) = true
  · rw [ite_eq_left c5] at h
    subst h
    simp only [beq_iff_eq] at c5
    exact distT_of_ord5 i hi (hord 5 c5 (by norm_num))
  rw [ite_eq_right c5] at h
  by_cases c3 : (o == 3) = true
  · rw [ite_eq_left c3] at h
    simp only [beq_iff_eq] at c3
    by_cases f12 : fixDimIs (Native.mul iotaARows V) 12 = true
    · rw [ite_eq_left f12] at h
      subst h
      exact distT_of_ord3_12 i hi (hord 3 c3 (by norm_num)) (hfixT 12 f12)
    rw [ite_eq_right f12] at h
    by_cases f8 : fixDimIs (Native.mul iotaARows V) 8 = true
    · rw [ite_eq_left f8] at h
      subst h
      exact distT_of_ord3_8 i hi (hord 3 c3 (by norm_num)) (hfixT 8 f8)
    rw [ite_eq_right f8] at h
    omega
  rw [ite_eq_right c3] at h
  omega

end CFSG.Sporadic.Co1Patterson
