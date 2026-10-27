module

public import CFSG.Sporadic.Co1Patterson.GraphCoverLower
public import Certificates.Certificate21150
public import Certificates.Certificate21151
public import CFSG.Sporadic.Co1Patterson.GraphFixDim

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Sporadic.Co1Patterson

open Subgroup CFSG.Sporadic.Co1Schreier CFSG.Sporadic.Co1Block CFSG.Sporadic.SmallF2
  CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1.Module CFSG.Monster.GMS
  CFSG.Sporadic.Co1Patterson.Native
open CFSG.Blueprint (NativeSporadic.Co1)

theorem suborb_check1 : suborbCheck1 = true :=
  Certificates.certificate21150.1

theorem suborb_check2 : suborbCheck2 = true :=
  Certificates.certificate21150.2.1

theorem suborb_check3 : suborbCheck3 = true :=
  Certificates.certificate21150.2.2

theorem suborb_check4 : suborbCheck4 = true :=
  Certificates.certificate21151.1

theorem suborb_check5 : suborbCheck5 = true :=
  Certificates.certificate21151.2

@[expose] def orbSize : List ℕ :=
  [1, 270, 12600, 60480, 34560, 573440, 491520, 4838400, 2419200, 12386304, 25804800]

theorem dagOK_true : dagOK = true := by
  have h := suborb_check1
  unfold suborbCheck1 at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1

theorem qTreeOK_true : qTreeOK = true := by
  have h := suborb_check1
  unfold suborbCheck1 at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.2

open CFSG.Sporadic.Co1.TwoBNative CFSG.Sporadic.Co1.InvNative in
theorem mem_twoAQNC_iff_contains
    {R : Native.Rows}
    {x : NativeSporadic.Co1} (hR : NRep R x) (hv : CFSG.Sporadic.Co1.InvNative.validRows R = true) :
    x ∈ twoAQNC ↔ qPts.contains R = true := by
  have hM : MRep R (nativeEmb x) := by
    unfold MRep
    rw [← matHom_eq_nativeEmb]
    exact hR.symm
  have hok : gtOK twoAQRows.toArray twoAQTree = true := by
    have h := qTreeOK_true
    unfold qTreeOK at h
    exact h
  rw [qPts, Std.HashSet.contains_ofList, mem_twoAQNC_iff]
  have hcl : nativeEmb x ∈ twoAQ ↔
      nativeEmb x ∈ Subgroup.closure (twoAQg '' {l | l < twoAQRows.toArray.size}) := by
    rw [← qSub_eq]
  rw [hcl]
  generalize twoAQTree = T at hok ⊢
  constructor
  · intro hx'
    obtain ⟨f, hf, -, heq⟩ := prodTree_closure_eq valHom valHom_injective hok twoAQg
      (qRep_arr qRep_twoA)
    have hmem : nativeEmb x ∈ f '' Set.Iio T.pts.size := by
      rw [← heq]
      exact hx'
    obtain ⟨i, hi, hfi⟩ := hmem
    have hvalid : validRows T.pts[i]! = true := by
      have hp := CFSG.Sporadic.Th.allIn_eq_true.1 (by
        unfold gtOK at hok
        simp only [Bool.and_eq_true] at hok
        exact hok.1.1.2) i (Nat.zero_le _) hi
      simp only [gtPointOK, Bool.and_eq_true] at hp
      exact hp.1
    have hrow : T.pts[i]! = R := by
      refine rowsMatrix_injective_of_valid hvalid hv ?_
      rw [← hf i hi, hfi]
      exact hM.symm
    have hi' : i < T.pts.size := hi
    rw [List.contains_iff_mem, Array.mem_toList_iff, ← hrow, getElem!_pos _ i hi']
    exact Array.getElem_mem hi'
  · intro hc
    rw [List.contains_iff_mem, Array.mem_toList_iff, Array.mem_iff_getElem] at hc
    obtain ⟨i, hi, hie⟩ := hc
    refine mem_closure_of_prodTree valHom valHom_injective hok twoAQg (qRep_arr qRep_twoA) hi ?_
    rw [getElem!_pos _ i hi, hie]
    exact hM.symm

@[expose] noncomputable def rep11V (i : ℕ) : Vt :=
  if i = 0 then vA else repV (i - 1)

section Reps

theorem nrep_rep11 {i : ℕ} (hi : i < 11) : NRep (rep11 i) (rep11V i) := by
  unfold rep11 rep11V
  by_cases h0 : i = 0
  · subst h0
    exact nrep_aNC
  · simp only [h0, ↓reduceIte, beq_iff_eq]
    exact nrep_repRows dagOK_true (by omega)

theorem nrep_repV {i : ℕ} (hi : i < 10) : NRep (repRows i) (repV i) :=
  nrep_repRows dagOK_true hi

theorem nrep_eRows : NRep eRows (repV 1) := nrep_repV (by norm_num)

theorem nrep_zRows : NRep zRows (repV 0) := nrep_repV (by norm_num)

end Reps

section Lower

theorem suborbCheck1_parts :
    exactOK orbQ zRows 270 = true ∧ exactOK orbE eRows 12600 = true := by
  have h := suborb_check1
  unfold suborbCheck1 at h
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.2, h.2⟩

theorem exact_orbQ : exactOK orbQ zRows 270 = true := suborbCheck1_parts.1

theorem exact_orbE : exactOK orbE eRows 12600 = true := suborbCheck1_parts.2

theorem exact_orb4c : exactOK orb4c (repRows 3) 34560 = true := suborb_check2

theorem mem_cOrb_of_contains {o : Orb} {root Y : Native.Rows} {n : ℕ}
    (h : exactOK o root n = true) {b : Vt} (hb : NRep root b) {y : Vt} (hy : NRep Y y)
    (hc : (ptSet o).contains Y = true) : y ∈ cOrb b := by
  obtain ⟨i, hi, rfl⟩ := ptSet_contains_iff.1 hc
  exact (mem_cOrb_iff_of_exactOK h b hb y).2 ⟨i, hi, hy⟩

theorem ncard_cOrb_z : (cOrb (repV 0)).ncard = 270 := ncard_cOrb_of_exactOK exact_orbQ _ nrep_zRows

theorem ncard_cOrb_e : (cOrb (repV 1)).ncard = 12600 :=
  ncard_cOrb_of_exactOK exact_orbE _ nrep_eRows

theorem ncard_cOrb_4c : (cOrb (repV 3)).ncard = 34560 :=
  ncard_cOrb_of_exactOK exact_orb4c _ (nrep_repV (by norm_num))

theorem le_ncard_cOrb_A4 : 60480 ≤ (cOrb (repV 2)).ncard := by
  have h := suborb_check3
  unfold suborbCheck3 at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨hok, hn⟩, -⟩ := h
  rw [← hn]
  exact le_ncard_of_orbOK hok _ brayNC (fun l hl => nrep_brayArr l hl)
    (fun l hl => brayNC_mem l hl) _ (nrep_repV (by norm_num))

theorem anchor_le {j k f : ℕ} (hj : j < 10)
    (hanchor : (aNC * (repV j : NativeSporadic.Co1)) ^ k = (repV 1 : NativeSporadic.Co1))
    {T : Array ℕ × Array ℕ} (hfib : fibreOK gensKe eRows (repRows j) f T = true) :
    12600 * f ≤ (cOrb (repV j)).ncard := by
  let R : Vt → Vt → Prop := fun u v => (aNC * (v : NativeSporadic.Co1)) ^ k = u
  have hR : ∀ g ∈ centralizer ({aNC} : Set NativeSporadic.Co1), ∀ u v, R u v →
      R (g • u) (g • v) := by
    intro g hg u v huv
    show (aNC * ((g • v : Vt) : NativeSporadic.Co1)) ^ k = ((g • u : Vt) : NativeSporadic.Co1)
    rw [aNC_mul_smul hg, conj_pow, coe_smul_conjVert, huv]
  have hm : f ≤ {v | v ∈ cOrb (repV j) ∧ R (repV 1) v}.ncard := by
    refine (fibre_le dagOK_true hfib nrep_eRows (nrep_repV hj)).trans
      (Set.ncard_le_ncard ?_ (Set.toFinite _))
    rintro _ ⟨g, hg, rfl⟩
    obtain ⟨hga, hge⟩ := mem_inf.1 hg
    refine ⟨⟨g, hga, rfl⟩, ?_⟩
    show (aNC * ((g • repV j : Vt) : NativeSporadic.Co1)) ^ k = ((repV 1 : Vt) : NativeSporadic.Co1)
    rw [aNC_mul_smul hga, conj_pow, hanchor]
    rw [mem_centralizer_singleton_iff] at hge
    rw [hge, mul_inv_cancel_right]
  have hn : {u | u ∈ cOrb (repV 1) ∧ R u (repV j)}.ncard ≤ 1 := by
    refine (Set.ncard_le_one (Set.toFinite _)).2 fun u hu w hw => Subtype.ext ?_
    exact hu.2.symm.trans hw.2
  have := card_le_of_double_count R hR (repV 1) (repV j) hm hn
  rw [ncard_cOrb_e, mul_one] at this
  exact this

theorem incidence_le {t b c₀ : Vt} {f N : ℕ} (hrel : orbRel t c₀ b)
    (hm : f ≤ {v : Vt | ∃ g ∈ centralizer ({aNC} : Set NativeSporadic.Co1) ⊓
      centralizer ({(c₀ : NativeSporadic.Co1)} : Set NativeSporadic.Co1), v = g • b}.ncard)
    (hn : {u | u ∈ cOrb c₀ ∧ orbRel t u b}.ncard ≤ N) :
    (cOrb c₀).ncard * f ≤ (cOrb b).ncard * N := by
  refine card_le_of_double_count (orbRel t) (fun g _ u v h => orbRel_smul g h) c₀ b
    (hm.trans (Set.ncard_le_ncard ?_ (Set.toFinite _))) hn
  rintro _ ⟨g, hg, rfl⟩
  obtain ⟨hga, hgc⟩ := mem_inf.1 hg
  refine ⟨⟨g, hga, rfl⟩, ?_⟩
  have hfix : g • c₀ = c₀ := (smul_eq_self_iff g _).2 hgc
  rw [← hfix]
  exact orbRel_smul g hrel

end Lower

section Invariants

open Classical in
@[expose] noncomputable def vCode (v : Vt) : ℕ × Bool × Bool × ℕ :=
  (ordA v, decide (inQa v), decide (inQa2 v), fixA v)

open Classical in
theorem vCode_eq (v : Vt) : vCode v = (ordA v, decide (inQa v), decide (inQa2 v), fixA v) := rfl

theorem vCode_smul {k : NativeSporadic.Co1} (hk : k ∈ centralizer ({aNC} : Set NativeSporadic.Co1))
    (v : Vt) : vCode (k • v) = vCode v := by
  unfold vCode
  rw [ordA_smul hk, fixA_smul hk, decide_eq_decide.2 (inQa_smul hk v),
    decide_eq_decide.2 (inQa2_smul hk v)]

theorem vCode_eq_of_mem {v w : Vt} (h : w ∈ cOrb v) : vCode w = vCode v := by
  obtain ⟨k, hk, rfl⟩ := h
  exact vCode_smul hk v

@[expose] def tableCode (i : ℕ) : ℕ × Bool × Bool × ℕ :=
  let t := invTable.getD i (0, false, false, 0)
  (t.1, t.2.1, t.2.2.1, 2 ^ t.2.2.2)

theorem tableCode_injective : ∀ i < 11, ∀ j < 11, tableCode i = tableCode j → i = j := by
  decide

theorem invOK_parts {b : Native.Rows} {o : ℕ} {inQ inQ2 : Bool} {d : ℕ}
    (h : invOK b o inQ inQ2 d = true) :
    CFSG.Sporadic.Co1.InvNative.validRows b = true ∧
    CFSG.Sporadic.Co1.InvNative.validRows
      (Native.mul (Native.mul iotaARows b) (Native.mul iotaARows b)) = true ∧
    CFSG.Sporadic.Co1.InvNative.orderIs (Native.mul iotaARows b) o = true ∧
    qPts.contains b = inQ ∧
    qPts.contains (Native.mul (Native.mul iotaARows b) (Native.mul iotaARows b)) = inQ2 ∧
    fixDimIs (Native.mul iotaARows b) d = true := by
  unfold invOK at h
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
    Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at h
  exact ⟨h.1.1.1.1.1, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

open Classical in
theorem vCode_rep11 {i : ℕ} (hi : i < 11) : vCode (rep11V i) = tableCode i := by
  have h := suborb_check3
  unfold suborbCheck3 invCheck at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  have hinv := h.2 i hi
  set t := invTable.getD i (0, false, false, 0) with ht
  obtain ⟨hv, hv2, hord, hq, hq2, hfix⟩ := invOK_parts hinv
  have hb := nrep_rep11 hi
  have hab : NRep (Native.mul iotaARows (rep11 i)) (aNC * rep11V i) := nrep_aNC.mul hb
  have hpos : ∀ j < 11, 0 < (invTable.getD j (0, false, false, 0)).1 := by decide
  have ho : 0 < t.1 := hpos i hi
  unfold vCode tableCode
  simp only [← ht]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · exact orderOf_eq_of_orderIs hab ho hord
  · simp only
    rw [← hq]
    exact Bool.eq_iff_iff.2 (by
      rw [decide_eq_true_iff]
      exact mem_twoAQNC_iff_contains hb hv)
  · simp only
    rw [← hq2]
    have hsq : NRep (Native.mul (Native.mul iotaARows (rep11 i)) (Native.mul iotaARows (rep11 i)))
        ((aNC * rep11V i) ^ 2) := by
      rw [sq]
      exact hab.mul hab
    exact Bool.eq_iff_iff.2 (by
      rw [decide_eq_true_iff]
      exact mem_twoAQNC_iff_contains hsq hv2)
  · simp only
    unfold fixA
    rw [show matHom (aNC * (rep11V i : NativeSporadic.Co1)) =
      rowsMatrix 24 (Native.mul iotaARows (rep11 i)) from hab]
    exact ncard_fix_of_fixDimIs hfix

theorem cOrb_disjoint {i j : ℕ} (hi : i < 11) (hj : j < 11) {v : Vt}
    (hvi : v ∈ cOrb (rep11V i)) (hvj : v ∈ cOrb (rep11V j)) : i = j := by
  refine tableCode_injective i hi j hj ?_
  rw [← vCode_rep11 hi, ← vCode_rep11 hj, ← vCode_eq_of_mem hvi, ← vCode_eq_of_mem hvj]

end Invariants

section Cover

theorem rep11V_succ (i : ℕ) : rep11V (i + 1) = repV i := by
  simp [rep11V]

theorem rep11V_zero : rep11V 0 = vA := by
  simp [rep11V]

theorem eq_of_rows {R S : Native.Rows} {x y : NativeSporadic.Co1} (hx : NRep R x) (hy : NRep S y)
    (h : R = S) : x = y :=
  NRep.unique hx (h ▸ hy)

theorem suborbCheck4_parts :
    (aNC * (repV 6 : NativeSporadic.Co1)) ^ 2 = (repV 1 : NativeSporadic.Co1) ∧
    (aNC * (repV 7 : NativeSporadic.Co1)) ^ 2 = (repV 1 : NativeSporadic.Co1) ∧
    (aNC * (repV 9 : NativeSporadic.Co1)) ^ 3 = (repV 1 : NativeSporadic.Co1) ∧
    fibreOK gensKe eRows (repRows 6) 384 (treeT fib6Masks) = true ∧
    fibreOK gensKe eRows (repRows 7) 192 (treeT fib7Masks) = true ∧
    fibreOK gensKe eRows (repRows 9) 2048 (treeT fib9Masks) = true := by
  have h := suborb_check4
  unfold suborbCheck4 at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  have hab : ∀ {j : ℕ}, j < 10 → NRep (Native.mul iotaARows (repRows j))
      (aNC * (repV j : NativeSporadic.Co1)) := fun hj => nrep_aNC.mul (nrep_repV hj)
  refine ⟨?_, ?_, ?_, h4, h5, h6⟩
  · rw [sq]; exact eq_of_rows ((hab (by norm_num)).mul (hab (by norm_num))) nrep_eRows h1
  · rw [sq]; exact eq_of_rows ((hab (by norm_num)).mul (hab (by norm_num))) nrep_eRows h2
  · rw [pow_succ, sq]
    exact eq_of_rows (((hab (by norm_num)).mul (hab (by norm_num))).mul (hab (by norm_num)))
      nrep_eRows h3

end Cover

end CFSG.Sporadic.Co1Patterson
