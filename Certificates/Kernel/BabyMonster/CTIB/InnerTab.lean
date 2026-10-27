module

public import CFSG.Monster.B.CTIB.HInnerCertInputs
public import CFSG.Certificates.Kernel.MonsterB.CTIBBfsSound
public import CFSG.Certificates.Kernel.MonsterB.TowerSound
public import CFSG.Certificates.Kernel.VecKRegs
public import Certificates.Data.Kernel.BabyMonster.CTIB.OrbitList
public import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.BabyMonster.Native.Small
public import CFSG.Perm.ChainSpec

public section

namespace CertificateChecks.KernelBM.CTIB.Inner

open CFSG.Monster.B.CTIB CFSG.Monster.B.CTIB.Native CFSG.KC.Bfs

@[expose] def cvalid (v : ℕ) : Bool := decide (0 < v) && decide (v < 2 ^ 22)

@[expose] def CensusLists : Prop :=
  ∀ r ∈ censusRecs, CFSG.Monster.B.CTIB.Kernel.OrbitList censusAct 2 cvalid r.1 r.2

@[expose] def rootOf (k : ℕ) : ℕ := (censusRecs.getD k (0, 0)).1

@[expose] def sizeOf (k : ℕ) : ℕ := (censusRecs.getD k (0, 0)).2

@[expose] def pR1 : ℕ :=
  47810743259111486330935542784346315201874441183507165481329202104220575218793395611769087365703509850697132031121010599184865917151007606903262209

@[expose] def pR2 : ℕ :=
  353571326888955612740596122068480721355288003717522751110349181088530461626401076082072501768454020411708742041340067980361879627965776369166961

@[expose] def pN2 : ℕ :=
  13146554364270667203224635494917066503611691250053258962166126914852182882843574289181126179668799120984568561875863272406778751695709494767072591

theorem r1_unpack : CFSG.Monster.B.Max2.Native.r1Rows = CFSG.KC.Co1F2.unpackR 22 pR1 := by
  decide +kernel

theorem r2_unpack : CFSG.Monster.B.Max2.Native.r2Rows = CFSG.KC.Co1F2.unpackR 22 pR2 := by
  decide +kernel

theorem r1_inv : Nat.beq (CFSG.KC.M1F2.mulF 22 pR1 pR1) (CFSG.KC.M1F2.idF 22) = true := by
  quickRfl

theorem r2_inv : Nat.beq (CFSG.KC.M1F2.mulF 22 pR2 pN2) (CFSG.KC.M1F2.idF 22) = true := by
  quickRfl

theorem censusAct_inj {k : ℕ} (hk : k < 2) {a b : ℕ} (ha : a < 2 ^ 22) (hb : b < 2 ^ 22)
    (h : censusAct k a = censusAct k b) : a = b := by
  rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
  · simp only [censusAct, ↓reduceIte, r1_unpack, CFSG.KC.Tower.act22_unpack] at h
    rw [← CFSG.KC.VecK.vmF_inv r1_inv ha, ← CFSG.KC.VecK.vmF_inv r1_inv hb, h]
  · simp only [censusAct, Nat.one_ne_zero, ↓reduceIte, r2_unpack,
      CFSG.KC.Tower.act22_unpack] at h
    rw [← CFSG.KC.VecK.vmF_inv r2_inv ha, ← CFSG.KC.VecK.vmF_inv r2_inv hb, h]

section Orbit

variable {act : ℕ → ℕ → ℕ} {ngen : ℕ}

theorem reach_trans {r x y : ℕ} (hx : Reach act ngen r x) (hy : Reach act ngen x y) :
    Reach act ngen r y := by
  induction hy with
  | root => exact hx
  | step k hk _ ih => exact .step k hk ih

theorem reach_iter {r y k : ℕ} (hk : k < ngen) (hy : Reach act ngen r y) :
    ∀ n, Reach act ngen r ((act k)^[n] y)
  | 0 => hy
  | n + 1 => by
    rw [Function.iterate_succ_apply']
    exact .step k hk (reach_iter hk hy n)

theorem iter_mem {f : ℕ → ℕ} {S : Finset ℕ} (hS : ∀ x ∈ S, f x ∈ S) {x : ℕ} (hx : x ∈ S) :
    ∀ n, f^[n] x ∈ S
  | 0 => hx
  | n + 1 => by
    rw [Function.iterate_succ_apply']
    exact hS _ (iter_mem hS hx n)

theorem iter_back {f : ℕ → ℕ} {S : Finset ℕ} (hS : ∀ x ∈ S, f x ∈ S)
    (hinj : ∀ x ∈ S, ∀ y ∈ S, f x = f y → x = y) {x : ℕ} (hx : x ∈ S) :
    ∃ n, f^[n + 1] x = x := by
  obtain ⟨i, hi, j, hj, hne, e⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (s := Finset.range (S.card + 1)) (t := S) (f := fun i => f^[i] x) (by simp)
    (fun i _ => iter_mem hS hx i)
  have cancel : ∀ i d, f^[i] x = f^[i + d] x → x = f^[d] x := by
    intro i
    induction i with
    | zero => intro d h; simpa using h
    | succ i ih =>
      intro d h
      apply ih d
      rw [Function.iterate_succ_apply', show i + 1 + d = (i + d) + 1 by omega,
        Function.iterate_succ_apply'] at h
      exact hinj _ (iter_mem hS hx i) _ (iter_mem hS hx (i + d)) h
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt h
    exact ⟨d, (cancel i (d + 1) (by rw [← Nat.add_assoc]; exact e)).symm⟩
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt h
    exact ⟨d, (cancel j (d + 1) (by rw [← Nat.add_assoc]; exact e.symm)).symm⟩

theorem orbit_facts {valid : ℕ → Bool} {root size : ℕ}
    (OL : CFSG.Monster.B.CTIB.Kernel.OrbitList act ngen valid root size)
    (hinj : ∀ k < ngen, ∀ a b, valid a = true → valid b = true → act k a = act k b → a = b) :
    ∃ S : Finset ℕ, (∀ x, Reach act ngen root x ↔ x ∈ S) ∧ S.card = size ∧
      (∀ x ∈ S, valid x = true ∧ root ≤ x) ∧ ∀ x ∈ S, Reach act ngen x root := by
  obtain ⟨pts, hlen, hnd, hroot, hval, hcl, hreach⟩ := OL
  have hcl' : ∀ k < ngen, ∀ x ∈ pts.toFinset, act k x ∈ pts.toFinset := fun k hk x hx => by
    rw [List.mem_toFinset] at hx ⊢
    exact hcl x hx k hk
  have hinj' : ∀ k < ngen, ∀ x ∈ pts.toFinset, ∀ y ∈ pts.toFinset, act k x = act k y → x = y :=
    fun k hk x hx y hy e => by
      rw [List.mem_toFinset] at hx hy
      exact hinj k hk x y (hval x hx).1 (hval y hy).1 e
  have fwd : ∀ x, Reach act ngen root x → x ∈ pts := fun x h => by
    induction h with
    | root => exact hroot
    | step k hk _ ih => exact hcl _ ih k hk
  have back : ∀ x, CFSG.Monster.B.CTIB.Kernel.Reach act ngen valid root x →
      x ∈ pts ∧ Reach act ngen root x := fun x h => by
    induction h with
    | root => exact ⟨hroot, .root⟩
    | step k hk ha hb _ hab ih =>
      rcases hab with rfl | e
      · exact ⟨hcl _ ih.1 k hk, .step k hk ih.2⟩
      · obtain ⟨n, hn⟩ := iter_back (hcl' k hk) (hinj' k hk) (List.mem_toFinset.2 ih.1)
        rw [Function.iterate_succ_apply'] at hn
        have hm := iter_mem (hcl' k hk) (List.mem_toFinset.2 ih.1) n
        rw [List.mem_toFinset] at hm
        have eb := hinj k hk _ _ hb (hval _ hm).1 (e.trans hn.symm)
        subst eb
        exact ⟨hm, reach_iter hk ih.2 n⟩
  have hS : ∀ x, Reach act ngen root x ↔ x ∈ pts.toFinset := fun x => by
    rw [List.mem_toFinset]
    exact ⟨fwd x, fun h => (back x (hreach x h)).2⟩
  refine ⟨pts.toFinset, hS, by rw [List.toFinset_card_of_nodup hnd, hlen],
    fun x hx => hval x (List.mem_toFinset.1 hx), fun x hx => ?_⟩
  have h := (hS x).2 hx
  clear hx
  induction h with
  | root => exact .root
  | @step y k hk ha ih =>
    obtain ⟨n, hn⟩ := iter_back (hcl' k hk) (hinj' k hk) ((hS _).1 ha)
    rw [Function.iterate_succ_apply] at hn
    have h1 : Reach act ngen (act k y) ((act k)^[n] (act k y)) := reach_iter hk Reach.root n
    rw [hn] at h1
    exact reach_trans h1 ih

end Orbit

theorem cvalid_lt {v : ℕ} (h : cvalid v = true) : v < 2 ^ 22 := by
  simp only [cvalid, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.2

theorem cvalid_pos {v : ℕ} (h : cvalid v = true) : 0 < v := by
  simp only [cvalid, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

theorem census_inj : ∀ k < 2, ∀ a b, cvalid a = true → cvalid b = true →
    censusAct k a = censusAct k b → a = b :=
  fun _ hk _ _ ha hb e => censusAct_inj hk (cvalid_lt ha) (cvalid_lt hb) e

theorem rec_mem {k : ℕ} (hk : k < 5) : censusRecs.getD k (0, 0) ∈ censusRecs := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [censusRecs]; omega)]
  exact List.getElem_mem _

theorem rootOf_eq : ∀ k < 5, rootOf k = [1, 3, 7, 17, 19].getD k 0 := by decide

theorem sizeOf_eq : ∀ k < 5, sizeOf k = [2300, 46575, 2049300, 1619200, 476928].getD k 0 := by
  decide

theorem census_orbit (hC : CensusLists) {k : ℕ} (hk : k < 5) :
    ∃ S : Finset ℕ, (∀ x, Reach censusAct 2 (rootOf k) x ↔ x ∈ S) ∧ S.card = sizeOf k ∧
      (∀ x ∈ S, cvalid x = true ∧ rootOf k ≤ x) ∧ ∀ x ∈ S, Reach censusAct 2 x (rootOf k) :=
  orbit_facts (hC _ (rec_mem hk)) census_inj

theorem census_disj (hC : CensusLists) {j k : ℕ} (hj : j < 5) (hk : k < 5) (hne : j ≠ k)
    {x : ℕ} (h1 : Reach censusAct 2 (rootOf j) x) (h2 : Reach censusAct 2 (rootOf k) x) : False := by
  obtain ⟨S, hS, -, hv, hb⟩ := census_orbit hC hj
  obtain ⟨T, hT, -, hw, hc⟩ := census_orbit hC hk
  have a1 : rootOf j ≤ rootOf k :=
    (hv _ ((hS _).1 (reach_trans h1 (hc x ((hT x).1 h2))))).2
  have a2 : rootOf k ≤ rootOf j :=
    (hw _ ((hT _).1 (reach_trans h2 (hb x ((hS x).1 h1))))).2
  have e : rootOf j = rootOf k := le_antisymm a1 a2
  rw [rootOf_eq j hj, rootOf_eq k hk] at e
  interval_cases j <;> interval_cases k <;> simp_all

theorem natBfs_census (hC : CensusLists) {k : ℕ} (hk : k < 5) :
    (∀ x, x ∈ (natBfs censusAct 2 (rootOf k) (sizeOf k + 1)).1 ↔
      Reach censusAct 2 (rootOf k) x) ∧
      (natBfs censusAct 2 (rootOf k) (sizeOf k + 1)).1.size = sizeOf k := by
  obtain ⟨S, hS, hcard, -, -⟩ := census_orbit hC hk
  obtain ⟨hmem, hsz, -⟩ := gBfs_listing (key := id) (fuel := sizeOf k + 1) S hS
    (fun _ _ _ _ e => e) (by omega)
  rw [native_natBfs_eq]
  exact ⟨fun x => (hmem x).trans (hS x).symm, hsz.trans hcard⟩

@[expose] def tabAfter (m : ℕ) : Array ℕ :=
  (List.range m).foldl (fun t k => (natBfs censusAct 2 (rootOf k) (sizeOf k + 1)).1.toList.foldl
    (fun t p => t.set! p (k + 1)) t) (Array.replicate (2 ^ 22) 0)

theorem innerTab_eq : innerTab = tabAfter 5 := by
  simp only [innerTab, tabAfter, rootOf, sizeOf, Id.run, Std.Legacy.Range.forIn_eq_forIn_range',
    Array.forIn_pure_yield_eq_foldl, Array.foldl_toList]
  rfl

theorem foldl_set (v : ℕ) : ∀ (L : List ℕ) (t : Array ℕ),
    (L.foldl (fun t p => t.set! p v) t).size = t.size ∧
      ∀ q, (L.foldl (fun t p => t.set! p v) t)[q]! = if q ∈ L ∧ q < t.size then v else t[q]!
  | [], t => ⟨rfl, fun q => by simp⟩
  | a :: L, t => by
    obtain ⟨h1, h2⟩ := foldl_set v L (t.set! a v)
    rw [List.foldl_cons]
    refine ⟨by rw [h1, Array.set!_eq_setIfInBounds, Array.size_setIfInBounds], fun q => ?_⟩
    rw [h2, Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]
    by_cases hq : q < t.size
    · have e : (t.setIfInBounds a v)[q]! = if a = q then v else t[q]! := by
        rw [getElem!_pos _ q (by rw [Array.size_setIfInBounds]; exact hq), getElem!_pos t q hq,
          Array.getElem_setIfInBounds]
      rw [e]
      by_cases ha : a = q
      · subst ha
        simp [hq]
      · by_cases hL : q ∈ L
        · simp [hL, hq]
        · simp [hL, hq, ha, Ne.symm ha]
    · have e : (t.setIfInBounds a v)[q]! = t[q]! := by
        rw [getElem!_neg _ q (by rw [Array.size_setIfInBounds]; exact hq), getElem!_neg t q hq]
      simp [hq]

theorem tabAfter_spec (hC : CensusLists) : ∀ m ≤ 5, (tabAfter m).size = 2 ^ 22 ∧
    ∀ q, (∀ k < m, q ∈ (natBfs censusAct 2 (rootOf k) (sizeOf k + 1)).1 → (tabAfter m)[q]! = k + 1) ∧
      ((∀ k < m, q ∉ (natBfs censusAct 2 (rootOf k) (sizeOf k + 1)).1) → (tabAfter m)[q]! = 0)
  | 0, _ => by
    refine ⟨by simp [tabAfter], fun q => ⟨fun k hk => absurd hk (Nat.not_lt_zero k), fun _ => ?_⟩⟩
    simp only [tabAfter, List.range_zero, List.foldl_nil]
    by_cases hq : q < 2 ^ 22
    · rw [getElem!_pos _ q (by simpa using hq), Array.getElem_replicate]
    · rw [getElem!_neg _ q (by simpa using hq)]
      rfl
  | m + 1, hm => by
    obtain ⟨hsz, hval⟩ := tabAfter_spec hC m (by omega)
    have e : tabAfter (m + 1) = (natBfs censusAct 2 (rootOf m) (sizeOf m + 1)).1.toList.foldl
        (fun t p => t.set! p (m + 1)) (tabAfter m) := by
      simp only [tabAfter, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    obtain ⟨h1, h2⟩ := foldl_set (m + 1) (natBfs censusAct 2 (rootOf m) (sizeOf m + 1)).1.toList
      (tabAfter m)
    rw [e]
    refine ⟨h1.trans hsz, fun q => ⟨fun k hk hq => ?_, fun hq => ?_⟩⟩
    · rw [h2, hsz]
      have hlt : q < 2 ^ 22 := by
        obtain ⟨S, hS, -, hv, -⟩ := census_orbit hC (by omega : k < 5)
        exact cvalid_lt (hv q ((hS q).1 (((natBfs_census hC (by omega : k < 5)).1 q).1 hq))).1
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk' | rfl
      · have hn : q ∉ (natBfs censusAct 2 (rootOf m) (sizeOf m + 1)).1.toList := by
          rw [Array.mem_toList_iff]
          intro hq'
          exact census_disj hC (by omega : k < 5) (by omega : m < 5) (by omega)
            (((natBfs_census hC (by omega : k < 5)).1 q).1 hq)
            (((natBfs_census hC (by omega : m < 5)).1 q).1 hq')
        rw [ite_eq_right (fun h => hn h.1)]
        exact (hval q).1 k hk' hq
      · rw [ite_eq_left ⟨Array.mem_toList_iff.2 hq, hlt⟩]
    · rw [h2, ite_eq_right (fun h => hq m (Nat.lt_succ_self m) (Array.mem_toList_iff.1 h.1))]
      exact (hval q).2 fun k hk => hq k (by omega)

theorem innerTab_facts (hC : CensusLists) :
    innerTab.size = 2 ^ 22 ∧
      (∀ k < 5, ∀ p, Reach censusAct 2 (rootOf k) p → innerTab[p]! = k + 1) ∧
      (∀ p, (∀ k < 5, ¬ Reach censusAct 2 (rootOf k) p) → innerTab[p]! = 0) ∧
      ∀ p, 0 < p → p < 2 ^ 22 → ∃ k < 5, Reach censusAct 2 (rootOf k) p := by
  obtain ⟨hsz, hval⟩ := tabAfter_spec hC 5 le_rfl
  rw [innerTab_eq]
  refine ⟨hsz, fun k hk p hp => (hval p).1 k hk (((natBfs_census hC hk).1 p).2 hp),
    fun p hp => (hval p).2 fun k hk h => hp k hk (((natBfs_census hC hk).1 p).1 h), ?_⟩
  choose S hS using fun k : Fin 5 => census_orbit hC k.2
  let U : Finset ℕ := Finset.univ.biUnion S
  have hdisj : (Set.univ : Set (Fin 5)).PairwiseDisjoint S := by
    intro i _ j _ hij
    rw [Function.onFun, Finset.disjoint_left]
    intro x hi hj
    exact census_disj hC i.2 j.2 (fun e => hij (Fin.ext e)) (((hS i).1 x).2 hi) (((hS j).1 x).2 hj)
  have hcard : U.card = 2 ^ 22 - 1 := by
    rw [Finset.card_biUnion (fun i _ j _ hij => hdisj (Set.mem_univ i) (Set.mem_univ j) hij)]
    simp only [fun k : Fin 5 => (hS k).2.1, Fin.sum_univ_five]
    decide
  have hsub : U ⊆ Finset.Ioo 0 (2 ^ 22) := by
    intro x hx
    obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.1 hx
    have h := ((hS i).2.2.1 x hi).1
    exact Finset.mem_Ioo.2 ⟨cvalid_pos h, cvalid_lt h⟩
  have hU : U = Finset.Ioo 0 (2 ^ 22) :=
    Finset.eq_of_subset_of_card_le hsub (by rw [Nat.card_Ioo, hcard]; omega)
  intro p hp0 hp1
  have hp : p ∈ U := hU ▸ Finset.mem_Ioo.2 ⟨hp0, hp1⟩
  obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.1 hp
  exact ⟨i, i.2, ((hS i).1 p).2 hi⟩

theorem innerTab_zero (hC : CensusLists) : innerTab[0]! = 0 :=
  (innerTab_facts hC).2.2.1 0 fun k hk h => by
    obtain ⟨S, hS, -, hv, -⟩ := census_orbit hC hk
    exact absurd (cvalid_pos (hv 0 ((hS 0).1 h)).1) (Nat.lt_irrefl 0)

@[expose] noncomputable def pB (b : Bool) : ℕ := Bool.rec (motive := fun _ => ℕ) pR1 pR2 b

@[expose] noncomputable def walkK (w len v : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) v (fun i acc => CFSG.KC.M1F2.vmF (nat_lit 22)
    (pB (Nat.beq (Nat.land (Nat.shiftRight w i) (nat_lit 1)) (nat_lit 1))) acc) len

theorem censusAct_pB (b : Bool) (v : ℕ) :
    CFSG.KC.M1F2.vmF 22 (pB b) v = censusAct (if b then 1 else 0) v := by
  cases b
  · simp only [pB, censusAct, Bool.false_eq_true, ↓reduceIte, r1_unpack,
      CFSG.KC.Tower.act22_unpack]
  · simp only [pB, censusAct, ↓reduceIte, Nat.one_ne_zero, r2_unpack, CFSG.KC.Tower.act22_unpack]

theorem reach_walk (w v : ℕ) : ∀ len, Reach censusAct 2 v (walkK w len v)
  | 0 => .root
  | len + 1 => by
    change Reach censusAct 2 v (CFSG.KC.M1F2.vmF 22 (pB _) (walkK w len v))
    rw [censusAct_pB]
    exact .step _ (by split <;> omega) (reach_walk w v len)

@[expose] def rootsL : List ℕ := [1, 3, 7, 17, 19]

theorem rootsL_eq : ∀ k < 5, CFSG.KC.BM.nthN rootsL k = rootOf k := by decide

@[expose] noncomputable def eV (e : ℕ) : ℕ := Nat.land e (nat_lit 4194303)

@[expose] noncomputable def eRec (e : ℕ) : ℕ := Nat.land (Nat.shiftRight e (nat_lit 22)) (nat_lit 7)

@[expose] noncomputable def eWalk (e : ℕ) : ℕ :=
  walkK (Nat.shiftRight e (nat_lit 31)) (Nat.land (Nat.shiftRight e (nat_lit 25)) (nat_lit 63))
    (CFSG.KC.BM.nthN rootsL (eRec e))

@[expose] noncomputable def walkOK (e : ℕ) : Bool := Nat.blt (eRec e) 5 && Nat.beq (eWalk e) (eV e)

@[expose] noncomputable def walksOK (L : List ℕ) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun e _ ih => walkOK e && ih) L

theorem walksOK_mem {L : List ℕ} (h : walksOK L = true) : ∀ e ∈ L, walkOK e = true := by
  induction L with
  | nil => intro e he; exact absurd he List.not_mem_nil
  | cons a L ih =>
    intro e he
    have h' : (walkOK a && walksOK L) = true := h
    rw [Bool.and_eq_true] at h'
    rcases List.mem_cons.1 he with rfl | he
    · exact h'.1
    · exact ih h'.2 e he

theorem innerTab_walk (hC : CensusLists) {e : ℕ} (h : walkOK e = true) :
    innerTab[eV e]! = eRec e + 1 := by
  simp only [walkOK, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
  obtain ⟨hk, he⟩ := h
  rw [← he]
  refine (innerTab_facts hC).2.1 _ hk _ ?_
  rw [← rootsL_eq _ hk]
  exact reach_walk _ _ _

theorem reach_of_tab (hC : CensusLists) {k u : ℕ} (hk : k < 5) (h : innerTab[u]! = k + 1) :
    Reach censusAct 2 (rootOf k) u := by
  by_cases hr : ∃ j < 5, Reach censusAct 2 (rootOf j) u
  · obtain ⟨j, hj, hju⟩ := hr
    have e := (innerTab_facts hC).2.1 j hj u hju
    rw [h] at e
    rw [Nat.succ_inj.1 e.symm] at hju
    exact hju
  · rw [(innerTab_facts hC).2.2.1 u fun j hj hju => hr ⟨j, hj, hju⟩] at h
    exact absurd h (by omega)

theorem orbit_complete (hC : CensusLists) {k : ℕ} (hk : k < 5) {L : List ℕ}
    (hw : ∀ e ∈ L, walkOK e = true ∧ eRec e = k) (hnd : (L.map eV).Nodup)
    (hlen : L.length = sizeOf k) {u : ℕ} (hu : Reach censusAct 2 (rootOf k) u) : u ∈ L.map eV := by
  obtain ⟨S, hS, hcard, -, -⟩ := census_orbit hC hk
  have hsub : (L.map eV).toFinset ⊆ S := by
    intro x hx
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hx)
    obtain ⟨h1, h2⟩ := hw e he
    simp only [walkOK, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h1
    rw [← h1.2, eWalk, h2, rootsL_eq k hk]
    exact (hS _).1 (reach_walk _ _ _)
  have heq : (L.map eV).toFinset = S := Finset.eq_of_subset_of_card_le hsub (by
    rw [List.toFinset_card_of_nodup hnd, List.length_map, hlen, hcard])
  exact List.mem_toFinset.1 (heq ▸ (hS u).1 hu)

theorem innerTy_walk (hC : CensusLists) {e n : ℕ} (h : walkOK e = true) (hn : n % 2 ^ 22 = eV e)
    (h0 : eV e ≠ 0) : innerTy innerTab n = eRec e + 1 := by
  simp only [innerTy, hn, h0, ↓reduceIte, innerTab_walk hC h]

end CertificateChecks.KernelBM.CTIB.Inner

end
