module

public import CFSG.Sporadic.Co1Block.TwoBTri
public import CFSG.Certificates.MergePrimitivity
public import CFSG.Certificates.NativeInvariantMerge
public import CFSG.Sporadic.ONOddCore.TreeOrbit
public import CFSG.Sporadic.Co1Block.CompQuot

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Sporadic.Co1Block

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Sporadic.Schreier.Tits CFSG.ONSchreier.Native

theorem twoBStrong_size :
    twoBStrong.size = 6 := twoB_tri_parts.2.2.2.2.2.1

theorem twoB_baseArr : baseArr 1365 twoBChainBase = twoBChainBase.toArray := by decide

theorem twoB_chainOK :
    rawChainOK 1365 (twoBStrong.extract 0 2) twoBStrong
    (baseArr 1365 twoBChainBase) twoBW 4 = true := by
  rw [twoB_baseArr]
  exact twoB_tri_parts.2.2.2.2.2.2.2.2.1

theorem twoB_allPerms : allPermsOK 1365 twoBStrong = true := by
  rw [allPermsOK, allLt_iff]
  intro j hj
  have := (chainCheckFacts twoB_chainOK).strong_inv j hj
  rwa [rawInvs, getElem!_map_of_lt hj] at this

theorem twoB_nodup : (finList 1365 twoBChainBase).Nodup := by decide

theorem twoBStrong_two_le : 2 ≤ twoBStrong.size := by
  rw [twoBStrong_size]
  norm_num

abbrev twoBQ : RawSchreierDatum 1365 :=
  RawSchreierDatum.ofArrays 1365 (by norm_num) twoBStrong 2 twoBStrong_two_le
    (finList 1365 twoBChainBase) twoB_nodup twoBW

abbrev xBar :
    Equiv.Perm (Fin 1365) := triHom (d₂C twoBXY.1)

abbrev yBar :
    Equiv.Perm (Fin 1365) := triHom (d₂C twoBXY.2)

abbrev twoBD :
    Subgroup (Equiv.Perm (Fin 1365)) := Subgroup.closure {xBar, yBar}

theorem strong_rep {j : ℕ} (hj : j < 6) :
    Rep 1365 twoBStrong[j]! (permOfArr 1365 twoBStrong[j]!) :=
  rep_of_allPermsOK twoB_allPerms (by rw [twoBStrong_size]; exact hj)

theorem strong0_eq :
    permOfArr 1365 twoBStrong[0]! = xBar :=
  eq_of_eqA (strong_rep (by norm_num)) rep_x twoB_tri_parts.2.2.2.2.2.2.1

theorem strong1_eq :
    permOfArr 1365 twoBStrong[1]! = yBar :=
  eq_of_eqA (strong_rep (by norm_num)) rep_y twoB_tri_parts.2.2.2.2.2.2.2.1

theorem range_strong :
    Set.range (fun i : Fin 2 => permOfArr 1365 twoBStrong[(i : ℕ)]!) = {xBar, yBar} := by
  ext g
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, rfl⟩
    match i with
    | ⟨0, _⟩ => exact Or.inl strong0_eq
    | ⟨1, _⟩ => exact Or.inr strong1_eq
  · rintro (rfl | rfl)
    · exact ⟨0, strong0_eq⟩
    · exact ⟨1, strong1_eq⟩

theorem twoBQ_original :
    twoBQ.originalSubgroup = twoBD := by
  rw [originalSubgroup_ofArrays, range_strong]

theorem card_twoBD :
    Nat.card twoBD = 251596800 := by
  rw [← twoBQ_original, card_ofArrays twoB_allPerms (by norm_num : 0 < 4) twoB_chainOK,
    twoB_baseArr, twoB_tri_parts.2.2.2.2.2.2.2.2.2.1]
  rfl

theorem mem_twoBD_of_sift
    {g : Array ℕ} {G : Equiv.Perm (Fin 1365)} (hG : Rep 1365 g G)
    (h : siftA 1365 (rawLevels 1365 twoBStrong twoBChainBase.toArray) twoBChainBase.toArray 0 g =
      true) : G ∈ twoBD := by
  rw [← twoBQ_original]
  rw [← twoB_baseArr] at h
  exact (siftA_iff_mem_ofArrays twoB_allPerms (by norm_num : 0 < 4) twoB_chainOK hG).1 h

theorem strong_mem
    {j : ℕ} (hj : j < 6) : permOfArr 1365 twoBStrong[j]! ∈ twoBD := by
  rw [← twoBQ_original]
  exact strong_mem_ofArrays twoB_allPerms (by norm_num : 0 < 4) twoB_chainOK
    (by rw [twoBStrong_size]; exact hj)

theorem twoBD_exists_apply
    (z : Fin 1365) : ∃ g ∈ twoBD, g 0 = z := by
  have hfull : ((rawLevels 1365 twoBStrong (baseArr 1365 twoBChainBase))[0]!).pts.size = 1365 := by
    rw [twoB_baseArr]
    exact levelSize_of_orbitSizes twoB_tri_parts.2.2.2.2.2.2.2.2.2.1 (by norm_num)
  have h0 : 0 < twoBQ.baseCount := by
    show 0 < (finList 1365 twoBChainBase).length
    decide
  obtain ⟨g, hg, hgz⟩ := exists_mem_ofArrays_apply_base (hn := by norm_num)
    (hk := twoBStrong_two_le) (hb := twoB_nodup) twoB_allPerms (by norm_num : 0 < 4)
    twoB_chainOK h0 hfull z
  refine ⟨g, twoBQ_original ▸ hg, ?_⟩
  have hb0 : twoBQ.base.get ⟨0, h0⟩ = 0 := rfl
  rw [← hb0]
  exact hgz

instance twoBD_pretransitive :
    MulAction.IsPretransitive twoBD (Fin 1365) := by
  refine ⟨fun x y => ?_⟩
  obtain ⟨g, hg, hgx⟩ := twoBD_exists_apply x
  obtain ⟨h, hh, hhy⟩ := twoBD_exists_apply y
  refine ⟨⟨h * g⁻¹, mul_mem hh (inv_mem hg)⟩, ?_⟩
  show (h * g⁻¹) x = y
  rw [Equiv.Perm.mul_apply, ← hgx, ← Equiv.Perm.mul_apply g⁻¹ g, inv_mul_cancel,
    Equiv.Perm.one_apply, hhy]

theorem twoB_prim_parts : twoBChainBase = [0, 1, 2] ∧
    (∀ x ∈ twoBSubReps, x < 1365 ∧ x ≠ 0 ∧ mergeOK 1365 (twoBStrong.extract 0 2) 0 x
      (Native.mergeSearch 1365 (twoBStrong.extract 0 2) 0 x) = true) ∧
    (∀ h ∈ twoBHSteps, h[0]! = 0) ∧
    clevelOK 1365 0 twoBHSteps (cbfs 1365 0 twoBHSteps) = true ∧
    clevelOK 1365 1 twoBHSteps (cbfs 1365 1 twoBHSteps) = true ∧
    clevelOK 1365 5 twoBHSteps (cbfs 1365 5 twoBHSteps) = true ∧
    clevelOK 1365 83 twoBHSteps (cbfs 1365 83 twoBHSteps) = true ∧
    ∀ z < 1365, (cbfs 1365 0 twoBHSteps).pos[z]! < (cbfs 1365 0 twoBHSteps).pts.size ∨
      (cbfs 1365 1 twoBHSteps).pos[z]! < (cbfs 1365 1 twoBHSteps).pts.size ∨
      (cbfs 1365 5 twoBHSteps).pos[z]! < (cbfs 1365 5 twoBHSteps).pts.size ∨
      (cbfs 1365 83 twoBHSteps).pos[z]! < (cbfs 1365 83 twoBHSteps).pts.size := by
  have h := twoB_prim_check
  simp only [twoBPrimCheckOf, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨hA, hB⟩, hC⟩, hD⟩, hE⟩ := h
  simp only [twoBHTrees, twoBSubReps, List.map_cons, List.map_nil, List.zip_cons_cons,
    List.zip_nil_right, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hD
  obtain ⟨hD0, hD1, hD5, hD83⟩ := hD
  refine ⟨by simpa using hA, fun x hx => ?_, fun t ht => ?_, hD0, hD1, hD5, hD83,
    fun z hz => ?_⟩
  · have := (List.all_eq_true.1 hB) x hx
    simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at this
    exact ⟨this.1.1, this.1.2, this.2⟩
  · have := (Array.all_eq_true'.1 hC) t ht
    simpa using this
  · have := allLt_spec hE hz
    simpa only [twoBHTrees, twoBSubReps, List.map_cons, List.map_nil, List.any_cons,
      List.any_nil, Bool.or_false, Bool.or_eq_true, decide_eq_true_eq] using this

abbrev twoBHGens : List (Equiv.Perm (Fin 1365)) := twoBHSteps.toList.map (permOfArr 1365)

abbrev twoBH : Subgroup (Equiv.Perm (Fin 1365)) := Subgroup.closure {g | g ∈ twoBHGens}

theorem twoBHSteps_get {j : ℕ} (hj : j < twoBHSteps.size) :
    ∃ i < 6, twoBHSteps[j]! = twoBStrong[i]! := by
  have hj' : j < (levelIdx twoBStrong twoBChainBase.toArray 1).length := by
    simpa only [twoBHSteps, List.size_toArray, List.length_map] using hj
  refine ⟨(levelIdx twoBStrong twoBChainBase.toArray 1)[j]'hj', ?_, ?_⟩
  · have hm := List.getElem_mem (l := levelIdx twoBStrong twoBChainBase.toArray 1) hj'
    simp only [levelIdx, List.mem_filter, List.mem_range, twoBStrong_size] at hm
    exact hm.1
  · rw [twoBHSteps, List.getElem!_toArray, List.getElem!_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_getElem hj', Option.map_some, Option.getD_some]

theorem twoBHSteps_rep {j : ℕ} (hj : j < twoBHSteps.size) :
    Rep 1365 twoBHSteps[j]! (permOfArr 1365 twoBHSteps[j]!) := by
  obtain ⟨i, hi, e⟩ := twoBHSteps_get hj
  rw [e]
  exact strong_rep hi

theorem twoBHGens_getD {j : ℕ} (hj : j < twoBHSteps.size) :
    twoBHGens.getD j 1 = permOfArr 1365 twoBHSteps[j]! := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, Array.getElem?_toList,
    Array.getElem?_eq_getElem hj, Option.map_some, Option.getD_some, getElem!_pos twoBHSteps j hj]

theorem twoBHGens_length : twoBHSteps.size = twoBHGens.length := by simp

theorem twoBH_le :
    twoBH ≤ twoBD := by
  rw [Subgroup.closure_le]
  intro g hg
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem (show g ∈ twoBHGens from hg)
  have hj' : j < twoBHSteps.size := by simpa using hj
  rw [← List.getD_eq_getElem _ 1 hj, twoBHGens_getD hj']
  obtain ⟨i, hi, e⟩ := twoBHSteps_get hj'
  rw [e]
  exact strong_mem hi

theorem twoBH_fix : ∀ h ∈ twoBH, h 0 = 0 := by
  intro h hh
  induction hh using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem (show g ∈ twoBHGens from hg)
    have hj' : j < twoBHSteps.size := by simpa using hj
    rw [← List.getD_eq_getElem _ 1 hj, twoBHGens_getD hj']
    have hmem : twoBHSteps[j]! ∈ twoBHSteps := by
      rw [getElem!_pos twoBHSteps j hj']
      exact Array.getElem_mem hj'
    apply Fin.ext
    rw [← (twoBHSteps_rep hj') 0]
    exact twoB_prim_parts.2.2.1 _ hmem
  | one => rfl
  | mul x y _ _ hx hy => rw [Equiv.Perm.mul_apply, hy, hx]
  | inv x _ hx => rw [Equiv.Perm.inv_eq_iff_eq, hx]

theorem twoBH_orbit {r : ℕ} (hr : r < 1365)
    (hL : clevelOK 1365 r twoBHSteps (cbfs 1365 r twoBHSteps) = true) {z : Fin 1365}
    (hz : (cbfs 1365 r twoBHSteps).pos[(z : ℕ)]! < (cbfs 1365 r twoBHSteps).pts.size) :
    ∃ h ∈ twoBH, h ⟨r, hr⟩ = z := by
  have hS : ∀ j < twoBHSteps.size, CFSG.ONSchreier.PRep 1365 twoBHSteps[j]! (twoBHGens.getD j 1) :=
    fun j hj x => by rw [twoBHGens_getD hj]; exact (twoBHSteps_rep hj) x
  have hmem := (CFSG.Sporadic.ONOddCore.mem_orbit_iff_tree
    (CFSG.ONSchreier.clevelFacts_of_clevelOK hL) hS twoBHGens_length hr z).2 hz
  obtain ⟨⟨h, hh⟩, e⟩ := hmem
  exact ⟨h, hh, e⟩

abbrev twoBXs (j : Fin 3) : Fin 1365 := finPt 1365 twoBSubReps[(j : ℕ)]!

theorem twoB_cover
    (x : Fin 1365) (hx : x ≠ 0) : ∃ j, ∃ h ∈ twoBH, h (twoBXs j) = x := by
  obtain ⟨-, -, -, h0, h1, h5, h83, hc⟩ := twoB_prim_parts
  rcases hc x x.2 with h | h | h | h
  · obtain ⟨g, hg, e⟩ := twoBH_orbit (by norm_num) h0 h
    exfalso
    apply hx
    rw [← e]
    exact twoBH_fix g hg
  · obtain ⟨g, hg, e⟩ := twoBH_orbit (by norm_num) h1 h
    exact ⟨0, g, hg, e⟩
  · obtain ⟨g, hg, e⟩ := twoBH_orbit (by norm_num) h5 h
    exact ⟨1, g, hg, e⟩
  · obtain ⟨g, hg, e⟩ := twoBH_orbit (by norm_num) h83 h
    exact ⟨2, g, hg, e⟩

theorem mergeStep_foldl_flag {G : Array (Array ℕ)} : ∀ (l : List (ℕ × ℕ × ℕ))
    (st : Bool × Array ℕ), (l.foldl (mergeStep 1365 G) st).1 = true → st.1 = true
  | [], _, h => h
  | t :: l, st, h => by
    have := mergeStep_foldl_flag l _ h
    simp only [mergeStep, Bool.and_eq_true] at this
    exact this.1.1.1.1

theorem mergeStep_foldl_ranges {G : Array (Array ℕ)} : ∀ (l : List (ℕ × ℕ × ℕ))
    (st : Bool × Array ℕ), (l.foldl (mergeStep 1365 G) st).1 = true →
      ∀ t ∈ l, t.1 < G.size ∧ t.2.1 < 1365 ∧ t.2.2 < 1365
  | [], _, _, t, ht => absurd ht List.not_mem_nil
  | t₀ :: l, st, h, t, ht => by
    rw [List.foldl_cons] at h
    rcases List.mem_cons.1 ht with rfl | ht
    · have := mergeStep_foldl_flag l _ h
      simp only [mergeStep, Bool.and_eq_true, decide_eq_true_eq] at this
      exact ⟨this.1.1.1.2, this.1.1.2, this.1.2⟩
    · exact mergeStep_foldl_ranges l _ h t ht

abbrev mergeFin (l : List (ℕ × ℕ × ℕ)) : List (Fin 2 × Fin 1365 × Fin 1365) :=
  l.map fun t => (finPt 2 t.1, finPt 1365 t.2.1, finPt 1365 t.2.2)

theorem mergeVals_mergeFin {G : Array (Array ℕ)} (hG : G.size = 2) {b x : ℕ}
    {l : List (ℕ × ℕ × ℕ)} (h : mergeOK 1365 G b x l = true) :
    mergeVals (mergeFin l) = l := by
  have hf : (l.foldl (mergeStep 1365 G) (true, mergeInit 1365 b x)).1 = true := by
    simp only [mergeOK, Bool.and_eq_true] at h
    exact h.1.2
  have hr := mergeStep_foldl_ranges l _ hf
  rw [mergeVals, List.map_map]
  conv_rhs => rw [← List.map_id l]
  refine List.map_congr_left fun t ht => ?_
  obtain ⟨h1, h2, h3⟩ := hr t ht
  rw [hG] at h1
  simp only [Function.comp_apply, id_eq, finPt_val h1, finPt_val h2, finPt_val h3, Prod.mk.eta]

theorem twoB_merge (j : Fin 3) : ∃ L, ValidInvariantMerge
    (fun i : Fin 2 => permOfArr 1365 twoBStrong[(i : ℕ)]!) 0 (twoBXs j) L := by
  have hsz : (twoBStrong.extract 0 2).size = 2 := by
    simp [twoBStrong_size]
  have hrep : ∀ i : Fin 2, Rep 1365 (twoBStrong.extract 0 2)[(i : ℕ)]!
      (permOfArr 1365 twoBStrong[(i : ℕ)]!) := by
    intro i
    have e : (twoBStrong.extract 0 2)[(i : ℕ)]! = twoBStrong[(i : ℕ)]! := by
      rw [getElem!_pos _ _ (by rw [hsz]; exact i.2), Array.getElem_extract,
        getElem!_pos _ _ (by rw [twoBStrong_size]; omega)]
      simp
    rw [e]
    exact strong_rep (by omega)
  have hx : ∀ j : Fin 3, twoBSubReps[(j : ℕ)]! < 1365 ∧
      mergeOK 1365 (twoBStrong.extract 0 2) 0 twoBSubReps[(j : ℕ)]!
        (Native.mergeSearch 1365 (twoBStrong.extract 0 2) 0 twoBSubReps[(j : ℕ)]!) = true := by
    intro j
    have hm : twoBSubReps[(j : ℕ)]! ∈ twoBSubReps := by
      rw [getElem!_pos _ _ (by simp [twoBSubReps])]
      exact List.getElem_mem _
    obtain ⟨h1, -, h3⟩ := twoB_prim_parts.2.1 _ hm
    exact ⟨h1, h3⟩
  obtain ⟨hlt, hok⟩ := hx j
  refine ⟨mergeFin (Native.mergeSearch 1365 (twoBStrong.extract 0 2) 0 twoBSubReps[(j : ℕ)]!),
    validInvariantMerge_of_mergeOK hrep ?_⟩
  rw [mergeVals_mergeFin hsz hok]
  rw [show ((twoBXs j : Fin 1365) : ℕ) = twoBSubReps[(j : ℕ)]! from finPt_val hlt]
  exact hok

instance twoBD_preprimitive :
    MulAction.IsPreprimitive twoBD (Fin 1365) := by
  have htrans : MulAction.IsPretransitive
      (Subgroup.closure (Set.range fun i : Fin 2 => permOfArr 1365 twoBStrong[(i : ℕ)]!))
      (Fin 1365) := by
    rw [range_strong]
    exact twoBD_pretransitive
  have h := stabilizer_orbit_merge_primitivity
    (fun i : Fin 2 => permOfArr 1365 twoBStrong[(i : ℕ)]!) 0 twoBH
    (by rw [range_strong]; exact twoBH_le) twoBH_fix twoBXs twoB_cover twoB_merge
  rw [range_strong] at h
  exact h

theorem rep_powTri {t : Array ℕ} {g : Equiv.Perm (Fin 1365)} (ht : Rep 1365 t g) :
    ∀ k, Rep 1365 (Native.powTri 1365 t k) (g ^ k)
  | 0 => by rw [pow_zero]; exact rep_idA
  | k + 1 => by rw [pow_succ]; exact rep_compA (rep_powTri ht k) ht

theorem orderOf_of_isPrimeOrderA {t : Array ℕ} {g : Equiv.Perm (Fin 1365)} (ht : Rep 1365 t g)
    {p : ℕ} [Fact p.Prime] (h : Native.isPrimeOrderA 1365 t p = true) : orderOf g = p := by
  simp only [Native.isPrimeOrderA, Bool.and_eq_true, Bool.not_eq_true'] at h
  refine orderOf_eq_prime (eq_of_eqA (rep_powTri ht p) rep_idA h.1) fun h1 => ?_
  have := (eqA_iff ht rep_idA).2 h1
  rw [this] at h
  exact Bool.noConfusion h.2

theorem orderOf_xBar :
    orderOf xBar = 2 :=
  orderOf_of_isPrimeOrderA rep_x twoB_tri_parts.2.2.2.2.2.2.2.2.2.2.1

theorem orderOf_yBar :
    orderOf yBar = 5 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact orderOf_of_isPrimeOrderA rep_y twoB_tri_parts.2.2.2.2.2.2.2.2.2.2.2.1

theorem orderOf_xyBar :
    orderOf (xBar * yBar) = 13 := by
  have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  exact orderOf_of_isPrimeOrderA (rep_compA rep_x rep_y)
    twoB_tri_parts.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem xBar_yBar_ne :
    xBar * yBar ≠ yBar * xBar := by
  intro h
  have hc : Commute xBar yBar := h
  have h10 : (xBar * yBar) ^ 10 = 1 := by
    rw [hc.mul_pow, show (10 : ℕ) = 2 * 5 by norm_num, pow_mul, ← orderOf_xBar, pow_orderOf_eq_one,
      one_pow, one_mul, mul_comm, pow_mul, ← orderOf_yBar, pow_orderOf_eq_one, one_pow]
  have := orderOf_dvd_of_pow_eq_one h10
  rw [orderOf_xyBar] at this
  norm_num at this

theorem xBar_mem :
    xBar ∈ twoBD := Subgroup.subset_closure (Set.mem_insert _ _)

theorem yBar_mem :
    yBar ∈ twoBD := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

abbrev xD :
    twoBD := ⟨xBar, xBar_mem⟩

abbrev yD :
    twoBD := ⟨yBar, yBar_mem⟩

theorem xD_yD_ne :

    xD * yD ≠ yD * xD := fun h => xBar_yBar_ne (congrArg Subtype.val h)

theorem index_stab_twoBD :
    (MulAction.stabilizer twoBD (0 : Fin 1365)).index = 1365 := by
  rw [MulAction.index_stabilizer_of_transitive, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem card_stab_twoBD :

    Nat.card (MulAction.stabilizer twoBD (0 : Fin 1365)) = 184320 := by
  have h := Subgroup.card_mul_index (MulAction.stabilizer twoBD (0 : Fin 1365))
  rw [index_stab_twoBD, card_twoBD] at h
  generalize Nat.card (MulAction.stabilizer twoBD (0 : Fin 1365)) = m at h ⊢
  omega

theorem isSimpleGroup_twoBD :
    IsSimpleGroup twoBD :=
  isSimpleGroup_closure_pair (by norm_num) (by rw [orderOf_xBar, orderOf_yBar]; norm_num) 0
    (by rw [orderOf_xyBar, card_stab_twoBD]; norm_num)

end CFSG.Sporadic.Co1Block
