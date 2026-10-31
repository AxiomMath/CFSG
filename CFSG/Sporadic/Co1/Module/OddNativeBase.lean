
module

public import CFSG.Sporadic.Co1.Module.FormsBase
public import Certificates.Data.CFSGNative.Co1.Odd
public meta import CFSG.Sporadic.Co1.Module.OrbitsBase
public meta import Certificates.Data.CFSGNative.Co1.Data
public meta import Certificates.Data.CFSGNative.Co1.Odd

@[expose] public section

namespace CFSG.Sporadic.Co1.Module.Odd

open CFSG.Blueprint CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native
  CFSG.Sporadic.Co1.OddNative Matrix

def mat : NativeSporadic.Co1 →* Matrix (Fin 24) (Fin 24) (ZMod 2) where
  toFun g := g.val.val
  map_one' := rfl
  map_mul' _ _ := rfl

theorem mat_injective : Function.Injective mat := fun _ _ e => Units.ext (Subtype.ext e)

theorem co1Act_eq_mulVec (g : NativeSporadic.Co1) (v : Vec24) : co1Act g v = mat g *ᵥ v := rfl

theorem mat_inv_eq {g : NativeSporadic.Co1} {N : Matrix (Fin 24) (Fin 24) (ZMod 2)}
    (h : mat g * N = 1) : mat g⁻¹ = N := by
  calc mat g⁻¹ = mat g⁻¹ * (mat g * N) := by rw [h, Matrix.mul_one]
    _ = (mat g⁻¹ * mat g) * N := by rw [Matrix.mul_assoc]
    _ = N := by rw [← map_mul, inv_mul_cancel, map_one, Matrix.one_mul]

theorem co1Act_mul' (g h : NativeSporadic.Co1) (v : Vec24) :
    co1Act (g * h) v = co1Act g (co1Act h v) := by
  simp only [co1Act_eq_mulVec, map_mul, Matrix.mulVec_mulVec]

theorem co1Act_one' (v : Vec24) : co1Act 1 v = v := by
  simp [co1Act_eq_mulVec]

@[instance_reducible] noncomputable def vecAct : MulAction NativeSporadic.Co1 Vec24 where
  smul g v := co1Act g v
  one_smul v := co1Act_one' v
  mul_smul g h v := co1Act_mul' g h v

noncomputable abbrev vecSMul : SMul NativeSporadic.Co1 Vec24 := vecAct.toSMul

attribute [local instance] vecAct vecSMul

theorem smul_eq_co1Act (g : NativeSporadic.Co1) (v : Vec24) : g • v = co1Act g v := rfl

theorem orbit_eq_range (v : Vec24) :
    MulAction.orbit NativeSporadic.Co1 v = Set.range fun g : NativeSporadic.Co1 => co1Act g v :=
  rfl

section SLP

variable {M : Type*} [Monoid M]

def lineEval (regs : List M) (fac : List (ℕ × ℕ)) : M :=
  (fac.map fun p => regs.getD p.1 1 ^ p.2).prod

def runEval (init : List M) (prog : List (List (ℕ × ℕ))) : List M :=
  prog.foldl (fun regs fac => regs ++ [lineEval regs fac]) init

def RegsRel (φ : M →* Matrix (Fin 24) (Fin 24) (ZMod 2)) (regsG : List M)
    (regsR : Array (Array ℕ)) : Prop :=
  regsR.size = regsG.length ∧
    ∀ i, φ (regsG.getD i 1) = rowsMatrix 24 (regsR[i]?.getD (idRows 24))

theorem lineRows_spec (φ : M →* Matrix (Fin 24) (Fin 24) (ZMod 2)) {regsG : List M}
    {regsR : Array (Array ℕ)} (h : RegsRel φ regsG regsR) (fac : List (ℕ × ℕ)) :
    φ (lineEval regsG fac) = rowsMatrix 24 (lineRows regsR fac) := by
  have key : ∀ (fac : List (ℕ × ℕ)) (acc : Array ℕ),
      rowsMatrix 24 (fac.foldl (fun acc p =>
        mulRows 24 acc (powRows 24 (regsR[p.1]?.getD (idRows 24)) p.2)) acc) =
        rowsMatrix 24 acc * (fac.map fun p => φ (regsG.getD p.1 1) ^ p.2).prod := by
    intro fac
    induction fac with
    | nil => intro acc; simp
    | cons p fac ih =>
      intro acc
      rw [List.foldl_cons, ih, rowsMatrix_mulRows, rowsMatrix_powRows, ← h.2 p.1,
        List.map_cons, List.prod_cons, Matrix.mul_assoc]
  rw [lineEval, map_list_prod, List.map_map, lineRows, key, rowsMatrix_idRows, Matrix.one_mul]
  simp only [Function.comp_def, map_pow]

theorem runRows_spec (φ : M →* Matrix (Fin 24) (Fin 24) (ZMod 2)) (prog : List (List (ℕ × ℕ))) :
    ∀ {regsG : List M} {regsR : Array (Array ℕ)}, RegsRel φ regsG regsR →
      RegsRel φ (runEval regsG prog) (runRows regsR prog) := by
  induction prog with
  | nil => intro regsG regsR h; exact h
  | cons fac prog ih =>
    intro regsG regsR h
    refine ih ?_
    refine ⟨by simp [h.1], fun i => ?_⟩
    have hsz : regsR.size = regsG.length := h.1
    by_cases hi : i < regsG.length
    · have hi' : i < regsR.size := hsz ▸ hi
      rw [List.getD_append _ _ _ _ hi, Array.getElem?_push_lt hi']
      have := h.2 i
      rw [Array.getElem?_eq_getElem hi'] at this
      exact this
    · by_cases hi2 : i = regsG.length
      · subst hi2
        rw [List.getD_append_right _ _ _ _ (le_refl _)]
        simp only [Nat.sub_self, List.getD_cons_zero]
        rw [← hsz, Array.getElem?_push_size]
        exact lineRows_spec φ h fac
      · have hn : regsG.length < i := lt_of_le_of_ne (not_lt.1 hi) (Ne.symm hi2)
        have hsz2 : regsR.size < i := hsz ▸ hn
        have e1 : (regsR.push (lineRows regsR fac))[i]? = none :=
          Array.getElem?_eq_none (by simp; omega)
        rw [e1, List.getD_eq_default _ _ (by simp; omega)]
        simp [rowsMatrix_idRows]

end SLP

theorem rowsKey_eq_ofDigits (x : Array ℕ) : rowsKey x = Nat.ofDigits 16777216 x.toList := by
  unfold rowsKey
  induction x.toList with
  | nil => simp
  | cons a l ih => simp [List.foldr_cons, Nat.ofDigits_cons, ih]

theorem validRows_size {x : Array ℕ} (h : validRows x = true) : x.size = 24 := by
  simp only [validRows, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1

theorem validRows_lt {x : Array ℕ} (h : validRows x = true) {r : ℕ} (hr : r ∈ x.toList) :
    r < 16777216 := by
  simp only [validRows, Bool.and_eq_true, beq_iff_eq, Array.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hr
  have hi' : i < x.size := by simpa using hi
  simpa using h.2 i hi'

theorem rowsKey_inj {x y : Array ℕ} (hx : validRows x = true) (hy : validRows y = true)
    (h : rowsKey x = rowsKey y) : x = y := by
  rw [rowsKey_eq_ofDigits, rowsKey_eq_ofDigits] at h
  have hl : x.toList.length = y.toList.length := by
    rw [Array.length_toList, Array.length_toList, validRows_size hx, validRows_size hy]
  exact Array.toList_inj.1 (Nat.ofDigits_inj_of_len_eq (by norm_num) hl
    (fun l hl' => validRows_lt hx hl') (fun l hl' => validRows_lt hy hl') h)

theorem rowsMatrix_injective_of_valid {x y : Array ℕ} (hx : validRows x = true)
    (hy : validRows y = true) (h : rowsMatrix 24 x = rowsMatrix 24 y) : x = y := by
  have hxs := validRows_size hx
  have hys := validRows_size hy
  apply Array.ext (by rw [hxs, hys])
  intro i hix hiy
  have hi : i < 24 := hxs ▸ hix
  have hrow : toVecD 24 (x[i]?.getD 0) = toVecD 24 (y[i]?.getD 0) := by
    funext j
    exact congrFun (congrFun h ⟨i, hi⟩) j
  have hxi : x[i]?.getD 0 = x[i] := by simp [hix]
  have hyi : y[i]?.getD 0 = y[i] := by simp [hiy]
  rw [hxi, hyi] at hrow
  exact toVecD_injective (validRows_lt hx (by simp)) (validRows_lt hy (by simp)) hrow

theorem strictInc_isChain : ∀ l : List ℕ, strictInc l = true → List.IsChain (· < ·) l
  | [], _ => List.isChain_nil
  | [a], _ => List.isChain_singleton a
  | a :: b :: t, h => by
    simp only [strictInc, Bool.and_eq_true, decide_eq_true_eq] at h
    exact List.IsChain.cons_cons h.1 (strictInc_isChain (b :: t) h.2)

theorem distinctKeys_nodup {keys : List ℕ} (h : distinctKeys keys = true) : keys.Nodup := by
  have hp := List.mergeSort_perm keys keyLe
  have hsorted : (keys.mergeSort keyLe).Pairwise (· < ·) :=
    List.isChain_iff_pairwise.1 (strictInc_isChain _ h)
  exact hp.nodup_iff.1 (List.Pairwise.imp (fun h' => ne_of_lt h') hsorted)

theorem forestOK_sound {P Q roots : Array (Array ℕ)} {F : Forest}
    (h : forestOK P Q roots F = true) (pp qq : ℕ → NativeSporadic.Co1)
    (hp : ∀ l < P.size, mat (pp l) = rowsMatrix 24 P[l]!)
    (hq : ∀ l < Q.size, mat (qq l) = rowsMatrix 24 Q[l]!)
    (rr : ℕ → NativeSporadic.Co1) (hr : ∀ j < roots.size, mat (rr j) = rowsMatrix 24 roots[j]!)
    (Inv : ℕ → NativeSporadic.Co1 → Prop) (hroot : ∀ j < roots.size, Inv j (rr j))
    (hstep : ∀ l < P.size, l < Q.size → ∀ j x, Inv j x → Inv j (pp l * x * qq l)) :
    ∃ f : ℕ → NativeSporadic.Co1,
      (∀ i < F.pts.size, F.rt[i]! < roots.size ∧ Inv F.rt[i]! (f i) ∧
        mat (f i) = rowsMatrix 24 F.pts[i]!) ∧
      ∀ i < F.pts.size, ∀ j < F.pts.size, f i = f j → i = j := by
  unfold forestOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true,
    List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨hroots, hpar⟩, hlab⟩, hrt⟩, hall⟩, hdist⟩ := h
  have hvalid : ∀ i < F.pts.size, validRows F.pts[i]! = true := by
    intro i hi
    have hp := hall i hi
    simp only [forestPointOK, Bool.and_eq_true] at hp
    exact hp.1
  have hmain : ∀ i, i < F.pts.size → ∃ x : NativeSporadic.Co1,
      F.rt[i]! < roots.size ∧ Inv F.rt[i]! x ∧ mat x = rowsMatrix 24 F.pts[i]! := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi
      have hp := hall i hi
      simp only [forestPointOK, Bool.and_eq_true] at hp
      obtain ⟨-, hp2⟩ := hp
      by_cases hir : i < roots.size
      · simp only [hir, ↓reduceIte, Bool.and_eq_true, beq_iff_eq] at hp2
        obtain ⟨hpt, hrti⟩ := hp2
        refine ⟨rr i, ?_, ?_, ?_⟩
        · rw [hrti]; exact hir
        · rw [hrti]; exact hroot i hir
        · rw [hpt, hr i hir]
      · simp only [hir, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hp2
        obtain ⟨⟨⟨⟨hpar', hlab'⟩, hlabQ⟩, hrt'⟩, hpt⟩ := hp2
        obtain ⟨x', hlt', hinv', hmat'⟩ := ih (F.par[i]!) hpar' (by omega)
        refine ⟨pp (F.lab[i]!) * x' * qq (F.lab[i]!), ?_, ?_, ?_⟩
        · rw [hrt']; exact hlt'
        · rw [hrt']; exact hstep _ hlab' hlabQ _ _ hinv'
        · rw [hpt, stepRows, rowsMatrix_mulRows, rowsMatrix_mulRows, map_mul, map_mul,
            hp _ hlab', hq _ hlabQ, hmat']
  choose! x hx using hmain
  refine ⟨x, fun i hi => hx i hi, ?_⟩
  intro i hi j hj hij
  have hm : rowsMatrix 24 F.pts[i]! = rowsMatrix 24 F.pts[j]! := by
    rw [← (hx i hi).2.2, ← (hx j hj).2.2, hij]
  have hpe := rowsMatrix_injective_of_valid (hvalid i hi) (hvalid j hj) hm
  have hnd := distinctKeys_nodup hdist
  have hlen : (F.pts.toList.map rowsKey).length = F.pts.size := by simp
  have hgi : (F.pts.toList.map rowsKey)[i]'(hlen ▸ hi) = rowsKey F.pts[i]! := by
    simp [getElem!_pos F.pts i hi]
  have hgj : (F.pts.toList.map rowsKey)[j]'(hlen ▸ hj) = rowsKey F.pts[j]! := by
    simp [getElem!_pos F.pts j hj]
  exact (List.Nodup.getElem_inj_iff hnd).1 (hgi.trans ((congrArg rowsKey hpe).trans hgj.symm))

theorem vecMulN_lt (R : Array ℕ) (hR : ∀ j : ℕ, R[j]?.getD 0 < 2 ^ 24) (v : ℕ) :
    vecMulN 24 R v < 2 ^ 24 := by
  have key : ∀ (m acc : ℕ), acc < 2 ^ 24 →
      (List.range m).foldl (fun acc j => if v.testBit j then acc ^^^ (R[j]?.getD 0) else acc)
        acc < 2 ^ 24 := by
    intro m
    induction m with
    | zero => intro acc h; simpa using h
    | succ m ih =>
      intro acc h
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      have := ih acc h
      split_ifs
      · exact Nat.xor_lt_two_pow this (hR m)
      · exact this
  exact key 24 0 (by norm_num)

theorem validRows_getD {x : Array ℕ} (h : validRows x = true) (j : ℕ) :
    x[j]?.getD 0 < 2 ^ 24 := by
  by_cases hj : j < x.size
  · simp only [validRows, Bool.and_eq_true, beq_iff_eq, Array.all_eq_true, decide_eq_true_eq] at h
    have := h.2 j hj
    simpa [hj] using this
  · simp [Array.getElem?_eq_none (not_lt.1 hj)]

theorem validRows_mulRows {X Y : Array ℕ} (hX : validRows X = true) (hY : validRows Y = true) :
    validRows (mulRows 24 X Y) = true := by
  have hXs := validRows_size hX
  simp only [validRows, Bool.and_eq_true, beq_iff_eq, Array.all_eq_true, decide_eq_true_eq]
  refine ⟨by simp [mulRows, hXs], fun i hi => ?_⟩
  simp only [mulRows, Array.getElem_map]
  exact vecMulN_lt Y (validRows_getD hY) _

theorem validRows_idRows : validRows (idRows 24) = true := by
  simp only [validRows, Bool.and_eq_true, beq_iff_eq, Array.all_eq_true, decide_eq_true_eq]
  refine ⟨by simp [idRows], fun i hi => ?_⟩
  simp only [idRows, Array.getElem_ofFn]
  rw [Nat.one_shiftLeft]
  have : (i : ℕ) < 24 := by simpa [idRows] using hi
  calc 2 ^ i < 2 ^ 24 := Nat.pow_lt_pow_right (by norm_num) this
    _ = 16777216 := by norm_num

theorem orderLoop_spec {M : Array ℕ} (hM : validRows M = true)
    {X : Matrix (Fin 24) (Fin 24) (ZMod 2)} (hX : rowsMatrix 24 M = X) :
    ∀ (fuel : ℕ) (cur : Array ℕ) (m : ℕ), validRows cur = true → rowsMatrix 24 cur = X ^ m →
      0 < orderLoop M fuel cur m → ∃ n, orderLoop M fuel cur m = n ∧ m ≤ n ∧ X ^ n = 1 ∧
        ∀ j, m ≤ j → j < n → X ^ j ≠ 1 := by
  intro fuel
  induction fuel with
  | zero => intro cur m _ _ h; simp [orderLoop] at h
  | succ fuel ih =>
    intro cur m hcur hmat hpos
    unfold orderLoop at hpos ⊢
    by_cases hid : (cur == idRows 24) = true
    · simp only [hid, ↓reduceIte] at hpos ⊢
      have hid' : cur = idRows 24 := beq_iff_eq.1 hid
      refine ⟨m, rfl, le_refl m, ?_, fun j hj hjm => absurd hj (not_le.2 hjm)⟩
      rw [← hmat, hid', rowsMatrix_idRows]
    · simp only [hid, Bool.false_eq_true, ↓reduceIte] at hpos ⊢
      have hne : X ^ m ≠ 1 := by
        intro h1
        apply hid
        rw [beq_iff_eq]
        apply rowsMatrix_injective_of_valid hcur validRows_idRows
        rw [hmat, h1, rowsMatrix_idRows]
      obtain ⟨n, hn, hmn, hXn, hlt⟩ := ih (mulRows 24 cur M) (m + 1) (validRows_mulRows hcur hM)
        (by rw [rowsMatrix_mulRows, hmat, hX, pow_succ]) hpos
      refine ⟨n, hn, by omega, hXn, fun j hj hjn => ?_⟩
      rcases Nat.eq_or_lt_of_le hj with h | h
      · rw [← h]; exact hne
      · exact hlt j h hjn

theorem orderOf_eq_of_orderN {M : Array ℕ} (hM : validRows M = true) {x : NativeSporadic.Co1}
    (hx : mat x = rowsMatrix 24 M) (hpos : 0 < orderN M) : orderOf x = orderN M := by
  obtain ⟨n, hn, -, hXn, hlt⟩ := orderLoop_spec hM hx.symm 400 M 1 hM
    (by rw [pow_one]; exact hx.symm) hpos
  have hn' : orderN M = n := hn
  rw [hn']
  have hnpos : 0 < n := by rw [← hn']; exact hpos
  rw [orderOf_eq_iff hnpos]
  refine ⟨?_, fun m hm hm0 hxm => ?_⟩
  · apply mat_injective
    rw [map_pow, hXn, map_one]
  · refine hlt m (by omega) hm ?_
    rw [← map_pow, hxm, map_one]

theorem countBelow_eq (p : ℕ → Bool) (n acc : ℕ) :
    countBelow p n acc = acc + ((Finset.range n).filter fun i => p i = true).card := by
  induction n generalizing acc with
  | zero => simp [countBelow]
  | succ n ih =>
    rw [countBelow, ih, Finset.range_add_one, Finset.filter_insert]
    by_cases hp : p n = true
    · simp only [hp, ↓reduceIte]
      rw [Finset.card_insert_of_notMem (by simp)]
      omega
    · simp [hp]

theorem transposeRows_lt (M : Array ℕ) (j : ℕ) : (transposeRows 24 M)[j]?.getD 0 < 2 ^ 24 := by
  unfold transposeRows
  by_cases hj : j < 24
  · simp only [Array.getElem?_ofFn, hj, ↓reduceDIte, Option.getD_some]
    exact ofBits_lt _ _
  · simp [hj]

theorem isFixedN_iff (M : Array ℕ) {x : ℕ} (hx : x < 2 ^ 24) :
    isFixedN (transposeRows 24 M) x = true ↔ rowsMatrix 24 M *ᵥ toVecD 24 x = toVecD 24 x := by
  rw [isFixedN, beq_iff_eq, rowsMatrix_mulVec]
  constructor
  · intro h
    rw [h]
  · intro h
    exact toVecD_injective (vecMulN_lt _ (transposeRows_lt _) _) hx h

theorem toVecD_image_Iio : toVecD 24 '' Set.Iio (2 ^ 24) = Set.univ := by
  have hinj : Set.InjOn (toVecD 24) (Set.Iio (2 ^ 24)) :=
    fun x hx y hy h => toVecD_injective hx hy h
  refine Set.eq_of_subset_of_ncard_le (Set.subset_univ _) ?_ Set.finite_univ
  rw [Set.ncard_univ, Set.InjOn.ncard_image hinj, Set.ncard_Iio_nat]
  simp [Nat.card_eq_fintype_card, ZMod.card]

theorem exists_toVecD (v : Vec24) : ∃ x < 2 ^ 24, toVecD 24 x = v := by
  have : v ∈ toVecD 24 '' Set.Iio (2 ^ 24) := by
    rw [toVecD_image_Iio]
    trivial
  obtain ⟨x, hx, rfl⟩ := this
  exact ⟨x, hx, rfl⟩

theorem ncard_eq_countBelow {P : Vec24 → Prop} {p : ℕ → Bool}
    (h : ∀ x < 2 ^ 24, (p x = true ↔ P (toVecD 24 x))) :
    {v : Vec24 | P v}.ncard = countBelow p 16777216 0 := by
  have hset : {v : Vec24 | P v} = toVecD 24 '' {x | x < 2 ^ 24 ∧ p x = true} := by
    ext v
    constructor
    · intro hv
      obtain ⟨x, hx, rfl⟩ := exists_toVecD v
      exact ⟨x, ⟨hx, (h x hx).2 hv⟩, rfl⟩
    · rintro ⟨x, ⟨hx, hp⟩, rfl⟩
      exact (h x hx).1 hp
  rw [hset, Set.InjOn.ncard_image (fun x hx y hy e => toVecD_injective hx.1 hy.1 e),
    countBelow_eq, zero_add, ← Set.ncard_coe_finset]
  congr 1
  ext x
  simp only [Set.mem_ofPred_eq, Finset.coe_filter, Finset.mem_range]
  norm_num

theorem ncard_fixedSet (Ms : List (Array ℕ)) :
    {v : Vec24 | ∀ M ∈ Ms, rowsMatrix 24 M *ᵥ v = v}.ncard =
      fixCount (Ms.map (transposeRows 24)) := by
  unfold fixCount
  refine ncard_eq_countBelow fun x hx => ?_
  rw [List.all_eq_true]
  constructor
  · intro h M hM
    exact (isFixedN_iff M hx).1 (h _ (List.mem_map_of_mem hM))
  · intro h Mt hMt
    obtain ⟨M, hM, rfl⟩ := List.mem_map.1 hMt
    exact (isFixedN_iff M hx).2 (h M hM)

theorem mem_collectBelow (p : ℕ → Bool) (n : ℕ) (acc : List ℕ) (x : ℕ) :
    x ∈ collectBelow p n acc ↔ x ∈ acc ∨ (x < n ∧ p x = true) := by
  induction n generalizing acc with
  | zero => simp [collectBelow]
  | succ n ih =>
    rw [collectBelow, ih]
    by_cases hp : p n = true
    · simp only [hp, ↓reduceIte, List.mem_cons]
      constructor
      · rintro ((h | h) | ⟨h1, h2⟩)
        · exact Or.inr ⟨by omega, by rw [h]; exact hp⟩
        · exact Or.inl h
        · exact Or.inr ⟨by omega, h2⟩
      · rintro (h | ⟨h1, h2⟩)
        · exact Or.inl (Or.inr h)
        · rcases Nat.lt_succ_iff_lt_or_eq.1 h1 with h | h
          · exact Or.inr ⟨h, h2⟩
          · exact Or.inl (Or.inl h)
    · simp only [hp, Bool.false_eq_true, ↓reduceIte]
      constructor
      · rintro (h | ⟨h1, h2⟩)
        · exact Or.inl h
        · exact Or.inr ⟨by omega, h2⟩
      · rintro (h | ⟨h1, h2⟩)
        · exact Or.inl h
        · rcases Nat.lt_succ_iff_lt_or_eq.1 h1 with h | h
          · exact Or.inr ⟨h, h2⟩
          · subst h; exact absurd h2 hp

theorem mem_fixList (Ms : List (Array ℕ)) (x : ℕ) :
    x ∈ fixList (Ms.map (transposeRows 24)) ↔
      x < 2 ^ 24 ∧ ∀ M ∈ Ms, rowsMatrix 24 M *ᵥ toVecD 24 x = toVecD 24 x := by
  unfold fixList
  rw [mem_collectBelow]
  simp only [List.not_mem_nil, false_or, List.all_eq_true]
  constructor
  · rintro ⟨hx, h⟩
    refine ⟨by omega, fun M hM => (isFixedN_iff M (by omega)).1 (h _ (List.mem_map_of_mem hM))⟩
  · rintro ⟨hx, h⟩
    refine ⟨by omega, fun Mt hMt => ?_⟩
    obtain ⟨M, hM, rfl⟩ := List.mem_map.1 hMt
    exact (isFixedN_iff M hx).2 (h M hM)

theorem foldl_dot_zmod (x y : ℕ) (m : ℕ) (init : Bool) :
    (if (List.range m).foldl (fun acc j => acc ^^ (x.testBit j && y.testBit j)) init = true
        then (1 : ZMod 2) else 0) =
      (if init = true then 1 else 0) +
        ∑ j ∈ Finset.range m,
          (if (x.testBit j && y.testBit j) = true then (1 : ZMod 2) else 0) := by
  induction m with
  | zero => cases init <;> simp
  | succ m ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      Finset.sum_range_succ, ← add_assoc, ← ih]
    generalize (List.range m).foldl (fun acc j => acc ^^ (x.testBit j && y.testBit j)) init = b
    cases b <;> cases x.testBit m <;> cases y.testBit m <;> decide

theorem toVecD_dotProduct (x y : ℕ) :
    toVecD 24 x ⬝ᵥ toVecD 24 y = if dotN x y = true then 1 else 0 := by
  unfold dotN
  rw [foldl_dot_zmod]
  simp only [Bool.false_eq_true, ↓reduceIte, zero_add]
  rw [dotProduct, ← Fin.sum_univ_eq_sum_range
      (fun j => if (x.testBit j && y.testBit j) = true then (1 : ZMod 2) else 0) 24]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [toVecD_apply, toVecD_apply]
  cases x.testBit j.val <;> cases y.testBit j.val <;> simp

theorem q₀_toVecD (x : ℕ) :
    q₀ (toVecD 24 x) = if q0N (transposeRows 24 qRows) x = true then 1 else 0 := by
  unfold q₀ q0N
  rw [show Qm = rowsMatrix 24 qRows from rfl, rowsMatrix_mulVec, toVecD_dotProduct]

theorem bil₀_toVecD (u v : ℕ) :
    bil₀ (toVecD 24 u) (toVecD 24 v) =
      if bilN (transposeRows 24 f0Rows) u v = true then 1 else 0 := by
  unfold bil₀ bilN
  rw [← rowsMatrix_f0Rows, rowsMatrix_mulVec, toVecD_dotProduct]

theorem nondeg_of_gramOK {Ms : List (Array ℕ)}
    (h : gramOK (transposeRows 24 f0Rows) (fixList (Ms.map (transposeRows 24))) = true) :
    ∀ u ∈ {v : Vec24 | ∀ M ∈ Ms, rowsMatrix 24 M *ᵥ v = v},
      (∀ v ∈ {v : Vec24 | ∀ M ∈ Ms, rowsMatrix 24 M *ᵥ v = v}, bil₀ u v = 0) → u = 0 := by
  intro u hu hperp
  obtain ⟨x, hx, rfl⟩ := exists_toVecD u
  by_cases hx0 : x = 0
  · rw [hx0, toVecD_zero]
  · exfalso
    have hxW : x ∈ fixList (Ms.map (transposeRows 24)) := (mem_fixList Ms x).2 ⟨hx, hu⟩
    simp only [gramOK, List.all_eq_true, Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at h
    rcases h x hxW with h0 | ⟨y, hy, hxy⟩
    · exact hx0 h0
    · obtain ⟨hy24, hyfix⟩ := (mem_fixList Ms y).1 hy
      have := hperp (toVecD 24 y) hyfix
      have h1 : bil₀ (toVecD 24 x) (toVecD 24 y) = 1 := by rw [bil₀_toVecD]; simp [hxy]
      rw [h1] at this
      exact absurd this (by decide)

theorem eq_one_of_faithfulOK {Zs : Array (Array ℕ)} {W : List ℕ}
    (h : faithfulOK Zs W = true) (hW : ∀ x ∈ W, x < 2 ^ 24) {z : Array ℕ} (hz : z ∈ Zs)
    {g : NativeSporadic.Co1} (hg : mat g = rowsMatrix 24 z)
    (hfix : ∀ x ∈ W, co1Act g (toVecD 24 x) = toVecD 24 x) : g = 1 := by
  simp only [faithfulOK, Array.all_eq_true, Bool.or_eq_true, beq_iff_eq, List.any_eq_true,
    Bool.not_eq_true'] at h
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 hz
  rcases h i hi with h1 | ⟨x, hx, hfx⟩
  · apply mat_injective
    rw [hg, h1, rowsMatrix_idRows, map_one]
  · exfalso
    have hnot : ¬ isFixedN (transposeRows 24 Zs[i]) x = true := by simpa using hfx
    rw [isFixedN_iff _ (hW x hx)] at hnot
    apply hnot
    rw [← hg]
    exact hfix x hx

end CFSG.Sporadic.Co1.Module.Odd
