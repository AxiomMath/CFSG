module

public import CFSG.Timmesfeld.Orders.ExceptionalWeyl

public noncomputable section

namespace CFSG.Timmesfeld.ExceptionalOrders

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CoxeterSystem

theorem eq_of_digits_eq : ∀ (n c c' : ℕ), c < 16 ^ n → c' < 16 ^ n →
    (∀ j < n, c / 16 ^ j % 16 = c' / 16 ^ j % 16) → c = c'
  | 0, c, c', hc, hc', _ => by
    rw [pow_zero] at hc hc'
    omega
  | n + 1, c, c', hc, hc', h => by
    have h0 := h 0 (Nat.succ_pos n)
    rw [pow_zero, Nat.div_one, Nat.div_one] at h0
    have hlt : ∀ x, x < 16 ^ (n + 1) → x / 16 < 16 ^ n := fun x hx => by
      rw [Nat.div_lt_iff_lt_mul (by norm_num), ← pow_succ]
      exact hx
    have ih := eq_of_digits_eq n (c / 16) (c' / 16) (hlt c hc) (hlt c' hc') fun j hj => by
      have := h (j + 1) (by omega)
      rwa [pow_succ', ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul] at this
    have e := Nat.div_add_mod c 16
    have e' := Nat.div_add_mod c' 16
    omega

theorem eq_of_decodeVec_eq {τ : Tag} {c c' : ℕ} (hc : c < 16 ^ τ.rank) (hc' : c' < 16 ^ τ.rank)
    (h : decodeVec (τ := τ) c = decodeVec c') : c = c' := by
  refine eq_of_digits_eq τ.rank c c' hc hc' fun j hj => ?_
  have := congrFun h ⟨j, hj⟩
  simp only [decodeVec] at this
  omega

@[expose] def maskSet (τ : Tag) (m : ℕ) : Finset (Fin τ.rank) :=
  Finset.univ.filter fun k => m.testBit k

theorem mem_maskSet {τ : Tag} {m : ℕ} {k : Fin τ.rank} :
    k ∈ maskSet τ m ↔ m.testBit k = true := by
  simp [maskSet]

structure OrbitCert (τ : Tag) where
  lam : ℕ
  pts : List ℕ
  parents : List ℕ
  table : List ℕ
  lens : List ℕ

namespace OrbitCert

variable {τ : Tag} (C : OrbitCert τ) (mJ mJ' : ℕ)

@[expose] def pt (k : ℕ) : Fin τ.rank → ℤ :=
  decodeVec (C.pts.getD k 0)

@[expose] def image (k : ℕ) (i : Fin τ.rank) : ℕ :=
  C.table.getD k 0 / 256 ^ (i : ℕ) % 256

@[expose] def parent (k : ℕ) : ℕ :=
  C.parents.getD (k - 1) 0 / 16

@[expose] def parentIndex (k : ℕ) : ℕ :=
  C.parents.getD (k - 1) 0 % 16

@[expose] def checkLam : Bool :=
  (List.finRange τ.rank).all fun i =>
    if mJ'.testBit i then decide (label τ (decodeVec C.lam) i = 0)
    else !mJ.testBit i || decide (0 < label τ (decodeVec C.lam) i)

@[expose] def checkHead : Bool :=
  decide (0 < C.pts.length) && List.ofFn (C.pt 0) == List.ofFn (label τ (decodeVec C.lam))

@[expose] def checkParents : Bool :=
  (List.range C.pts.length).all fun k =>
    decide (k = 0) ||
      (decide (C.parent k < k) &&
        if h : C.parentIndex k < τ.rank then
          mJ.testBit (C.parentIndex k) &&
            List.ofFn (C.pt k) == List.ofFn (dualReflect τ ⟨_, h⟩ (C.pt (C.parent k)))
        else false)

@[expose] def checkTable : Bool :=
  (List.range C.pts.length).all fun k => (List.finRange τ.rank).all fun i =>
    !mJ.testBit i ||
      (decide (C.image k i < C.pts.length) &&
        List.ofFn (C.pt (C.image k i)) == List.ofFn (dualReflect τ i (C.pt k)))

@[expose] def checkCodes : Bool :=
  C.pts.all (· < 16 ^ τ.rank) && decide C.pts.Nodup

@[expose] def checkLens : Bool :=
  decide (C.lens.length = C.pts.length) && C.lens.getD 0 0 == 0 &&
    (List.range C.pts.length).all fun k =>
      decide (k = 0) ||
        if h : C.parentIndex k < τ.rank then
          C.lens.getD k 0 + (if C.pt (C.parent k) ⟨_, h⟩ < 0 then 1 else 0) ==
            C.lens.getD (C.parent k) 0 + (if 0 < C.pt (C.parent k) ⟨_, h⟩ then 1 else 0)
        else false

@[expose] def check : Bool :=
  C.checkLam mJ mJ' && C.checkHead && C.checkParents mJ && C.checkTable mJ && C.checkCodes &&
    C.checkLens

variable {C mJ mJ'}

theorem eq_of_ofFn_beq {u v : Fin τ.rank → ℤ} (h : (List.ofFn u == List.ofFn v) = true) :
    u = v :=
  List.ofFn_injective (eq_of_beq h)

theorem pt_eq_getElem {k : ℕ} (hk : k < C.pts.length) :
    C.pt k = decodeVec (C.pts[k]) := by
  rw [pt, List.getD_eq_getElem _ _ hk]

theorem pt_mem {k : ℕ} (hk : k < C.pts.length) :
    C.pt k ∈ C.pts.map (decodeVec (τ := τ)) := by
  rw [pt_eq_getElem hk]
  exact List.mem_map_of_mem (List.getElem_mem hk)

theorem exists_pt_eq {c : Fin τ.rank → ℤ} (hc : c ∈ C.pts.map (decodeVec (τ := τ))) :
    ∃ k < C.pts.length, C.pt k = c := by
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hc
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem ha
  exact ⟨k, hk, pt_eq_getElem hk⟩

theorem isOrbitList (hJ : maskSet τ mJ' ⊆ maskSet τ mJ) (h : C.check mJ mJ' = true) :
    IsOrbitList τ (maskSet τ mJ) (maskSet τ mJ') (decodeVec C.lam) (C.pts.map decodeVec) ∧
      C.lens = C.pts.map fun c => negCount τ (maskSet τ mJ) (decodeVec c) := by
  simp only [check, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hlam, hhead⟩, hpar⟩, htab⟩, hcodes⟩, hlens⟩ := h
  set J := maskSet τ mJ
  set J' := maskSet τ mJ'
  set lam : Fin τ.rank → ℤ := decodeVec C.lam
  simp only [checkLam, List.all_eq_true, List.mem_finRange, true_implies] at hlam
  have h0 : ∀ i ∈ J', label τ lam i = 0 := fun i hi => by
    have := hlam i
    simp only [mem_maskSet.1 hi, ↓reduceIte] at this
    exact of_decide_eq_true this
  have hpos : ∀ i ∈ J, i ∉ J' → 0 < label τ lam i := fun i hi hi' => by
    have := hlam i
    have hi'' : mJ'.testBit i = false := by simpa [J', mem_maskSet] using hi'
    simp only [hi'', Bool.false_eq_true, ↓reduceIte, mem_maskSet.1 hi, Bool.not_true,
      Bool.false_or, decide_eq_true_eq] at this
    exact this
  simp only [checkHead, Bool.and_eq_true, decide_eq_true_eq] at hhead
  have hpt0 : C.pt 0 = label τ lam := eq_of_ofFn_beq hhead.2
  simp only [checkParents, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    decide_eq_true_eq, Bool.and_eq_true] at hpar
  simp only [checkTable, List.all_eq_true, List.mem_range, List.mem_finRange, true_implies,
    Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_true, decide_eq_true_eq] at htab
  have hnodup : (C.pts.map (decodeVec (τ := τ))).Nodup := by
    simp only [checkCodes, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hcodes
    refine hcodes.2.map_on fun a ha b hb hab => eq_of_decodeVec_eq (hcodes.1 a ha)
      (hcodes.1 b hb) hab
  have hparent : ∀ k < C.pts.length, k ≠ 0 → ∃ (i : Fin τ.rank), i ∈ J ∧ C.parent k < k ∧
      (i : ℕ) = C.parentIndex k ∧ C.pt k = dualReflect τ i (C.pt (C.parent k)) := by
    intro k hk hk0
    rcases hpar k hk with h | ⟨hlt, hrefl⟩
    · exact absurd h hk0
    · split at hrefl
      · rename_i hi
        simp only [Bool.and_eq_true] at hrefl
        exact ⟨⟨_, hi⟩, mem_maskSet.2 hrefl.1, hlt, rfl, eq_of_ofFn_beq hrefl.2⟩
      · exact absurd hrefl (by simp)
  have hreach : ∀ k < C.pts.length, ∃ w ∈ (coxeterSystem τ).parabolic (J : Set (Fin τ.rank)),
      label τ (w • lam) = C.pt k := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk
      rcases eq_or_ne k 0 with rfl | hk0
      · exact ⟨1, one_mem _, by rw [one_smul, hpt0]⟩
      · obtain ⟨i, hi, hlt, -, hkp⟩ := hparent k hk hk0
        obtain ⟨w, hw, hwk⟩ := ih _ hlt (hlt.trans hk)
        refine ⟨simple τ i * w, mul_mem ((coxeterSystem τ).simple_mem_parabolic hi) hw, ?_⟩
        rw [mul_smul, simple_smul, label_reflect_eq_dualReflect, hwk, hkp]
  have hL : IsOrbitList τ J J' lam (C.pts.map decodeVec) :=
    { subset := hJ
      zero := h0
      pos := hpos
      nodup := hnodup
      mem := hpt0 ▸ pt_mem hhead.1
      closed := fun c hc i hi => by
        obtain ⟨k, hk, rfl⟩ := exists_pt_eq hc
        obtain ⟨himg, heq⟩ := (htab k hk i).resolve_left (by simp [mem_maskSet.1 hi])
        rw [← eq_of_ofFn_beq heq]
        exact pt_mem himg
      reach := fun c hc => by
        obtain ⟨k, hk, rfl⟩ := exists_pt_eq hc
        exact hreach k hk }
  refine ⟨hL, ?_⟩
  simp only [checkLens, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true,
    List.mem_range, Bool.or_eq_true] at hlens
  obtain ⟨⟨hlen, hl0⟩, hstep⟩ := hlens
  have hcount : ∀ k < C.pts.length, C.lens.getD k 0 = negCount τ J (C.pt k) := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk
      rcases eq_or_ne k 0 with rfl | hk0
      · rw [hl0, hpt0, hL.negCount_label_lam]
      · obtain ⟨i, hi, hlt, hidx, hkp⟩ := hparent k hk hk0
        have hs := (hstep k hk).resolve_left hk0
        have hlt' : C.parentIndex k < τ.rank := hidx ▸ i.2
        rw [dite_eq_left hlt', beq_iff_eq] at hs
        have hi_eq : (⟨C.parentIndex k, hlt'⟩ : Fin τ.rank) = i := Fin.ext hidx.symm
        rw [hi_eq, ih _ hlt (hlt.trans hk)] at hs
        have key := negCount_dualReflect hi (C.pt (C.parent k))
        rw [← hkp] at key
        omega
  refine List.ext_getElem (by rw [List.length_map, hlen]) fun k hk hk' => ?_
  rw [List.getElem_map, ← pt_eq_getElem (by rwa [List.length_map] at hk'), ← hcount k
    (by rwa [List.length_map] at hk'), List.getD_eq_getElem _ _ hk]

theorem cosetSum_eq [Fintype (WeylGroup τ)] (hJ : maskSet τ mJ' ⊆ maskSet τ mJ)
    (h : C.check mJ mJ' = true) (q : ℕ) :
    cosetSum τ (maskSet τ mJ) (maskSet τ mJ') q = (C.lens.map (q ^ ·)).sum := by
  obtain ⟨hL, hlens⟩ := C.isOrbitList hJ h
  rw [hL.cosetSum_eq_sum, hlens, List.map_map, List.map_map]
  rfl

end OrbitCert

@[expose] def prodExps : List (ℕ × ℕ) → List ℕ
  | [] => [0]
  | (n, s) :: fs => (List.range n).flatMap fun i => (prodExps fs).map (s * i + ·)

@[expose] def geomSum (n s q : ℕ) : ℕ := ∑ i ∈ Finset.range n, q ^ (s * i)

theorem list_sum_map_range (f : ℕ → ℕ) (n : ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.sum_range_succ, Finset.sum_range_succ, ih]

theorem sum_map_pow_flatMap (q : ℕ) (l : List ℕ) (g : ℕ → List ℕ) :
    ((l.flatMap g).map (q ^ ·)).sum = (l.map fun i => ((g i).map (q ^ ·)).sum).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, List.sum_append, ih]

theorem sum_map_pow_prodExps (fs : List (ℕ × ℕ)) (q : ℕ) :
    ((prodExps fs).map (q ^ ·)).sum = (fs.map fun f => geomSum f.1 f.2 q).prod := by
  induction fs with
  | nil => simp [prodExps]
  | cons f fs ih =>
    obtain ⟨n, s⟩ := f
    rw [prodExps, sum_map_pow_flatMap, List.map_cons, List.prod_cons, ← ih, geomSum,
      Finset.sum_mul, ← list_sum_map_range]
    congr 1
    refine List.map_congr_left fun i _ => ?_
    rw [List.map_map, ← List.sum_map_mul_left]
    congr 1
    refine List.map_congr_left fun e _ => ?_
    simp [pow_add]

structure ChainStep (τ : Tag) where
  mask : ℕ
  prev : ℕ
  cert : OrbitCert τ
  factors : List (ℕ × ℕ)

namespace ChainStep

variable {τ : Tag}

@[expose] def check (s : ChainStep τ) : Bool :=
  s.cert.check s.mask s.prev &&
    ((List.finRange τ.rank).all fun k => !s.prev.testBit k || s.mask.testBit k) &&
    decide (s.cert.lens.Perm (prodExps s.factors))

@[expose] def value (s : ChainStep τ) (q : ℕ) : ℕ :=
  (s.factors.map fun f => geomSum f.1 f.2 q).prod

end ChainStep

@[expose] def chainCheck {τ : Tag} : List (ChainStep τ) → ℕ → Bool
  | [], m => m == 0
  | s :: ss, m => s.mask == m && s.check && chainCheck ss s.prev

theorem maskSet_zero {τ : Tag} : maskSet τ 0 = ∅ := by
  ext k
  simp [maskSet]

theorem parabolicSum_eq_of_chainCheck {τ : Tag} [Fintype (WeylGroup τ)] (q : ℕ) :
    ∀ (ss : List (ChainStep τ)) (m : ℕ), chainCheck ss m = true →
      parabolicSum τ (maskSet τ m) q = (ss.map fun s => s.value q).prod
  | [], m, h => by
    simp only [chainCheck, beq_iff_eq] at h
    subst h
    rw [maskSet_zero, Finset.coe_empty, parabolicSum_empty, List.map_nil, List.prod_nil]
  | s :: ss, m, h => by
    simp only [chainCheck, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨rfl, hs⟩, hss⟩ := h
    simp only [ChainStep.check, Bool.and_eq_true, List.all_eq_true, List.mem_finRange,
      true_implies, Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hs
    obtain ⟨⟨hcert, hsub⟩, hperm⟩ := hs
    have hJ : maskSet τ s.prev ⊆ maskSet τ s.mask := fun k hk => by
      rcases hsub k with h | h
      · rw [mem_maskSet] at hk
        rw [hk] at h
        exact absurd h (by simp)
      · exact mem_maskSet.2 h
    rw [parabolicSum_eq_mul (Finset.coe_subset.2 hJ), OrbitCert.cosetSum_eq hJ hcert,
      parabolicSum_eq_of_chainCheck q ss s.prev hss, List.map_cons, List.prod_cons,
      hperm.map _ |>.sum_eq, sum_map_pow_prodExps]
    rfl

theorem maskSet_full {τ : Tag} {m : ℕ} (h : ∀ k : Fin τ.rank, m.testBit k = true) :
    (maskSet τ m : Set (Fin τ.rank)) = Set.univ := by
  ext k
  simp [mem_maskSet, h k]

end CFSG.Timmesfeld.ExceptionalOrders
