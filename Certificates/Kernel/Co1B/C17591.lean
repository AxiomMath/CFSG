module

public import Certificates.Data.TabCo1ThreeD
public meta import Certificates.Data.TabCo1ThreeD
public import Certificates.Kernel.Co1B.Chk17591
public import Certificates.Kernel.Co1B.Lvl17591A
public import Certificates.Kernel.Co1B.Lvl17591B
public import Certificates.Kernel.Co1B.Lvl17591C
public import Certificates.Kernel.Co1B.C17590
public import Certificates.Kernel.Co1B.C2041
public import CFSG.Certificates.Kernel.Co1BSpinSound
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1B.Bound17591

open CFSG.KC.Co1BBound CFSG.KC.Co1BSpin CFSG.KC.Co1B CFSG.KC.Co1F2 CFSG.KC.M1F2 CFSG.KC.F2W
  CFSG.KLie.CT CFSG.KC.Enum CFSG.HardMathSupport.Dickson.I271.TabCo1ThreeD
  CFSG.HardMathSupport.Dickson.I271.TabCo1 CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1Block
  CertificateChecks.KernelCo1B

theorem kT' : eqK (getL 0 K.T 0) (trK 24 (powWK C1 0)) = true ∧
    eqK (getL 0 K.T 1) (trK 24 (powWK C1 1)) = true ∧
    eqK (getL 0 K.T 2) (trK 24 (powWK C1 2)) = true ∧ K.T.length = 3 := by
  have h := kT
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem cs_eq : colsOf (powList (c1Rows ()) 3) = (K.T.map (unpackR 24)).toArray := by
  obtain ⟨h0, h1, h2, hl⟩ := kT'
  obtain ⟨a, b, c, hK⟩ : ∃ a b c, K.T = [a, b, c] := List.length_eq_three.1 hl
  rw [hK] at h0 h1 h2
  have hc : c1Rows () = unpackR 24 C1 := Fix17590.c1_eq
  have hp : ∀ e, transposeRows 24 (CFSG.Sporadic.Co1Schreier.Native.pow (c1Rows ()) e) =
      unpackR 24 (trK 24 (powWK C1 e)) := fun e => by
    rw [hc, pow_unpack', transposeRows_unpackR]
  rw [hK, colsOf, powList, List.map_toArray, List.map_map]
  refine congrArg List.toArray ?_
  have hr : List.range 3 = [0, 1, 2] := rfl
  rw [hr]
  simp only [List.map_cons, List.map_nil, Function.comp_apply, hp]
  rw [← beq_of_eqK h0, ← beq_of_eqK h1, ← beq_of_eqK h2]
  rfl

theorem vecMulN_empty (x : Nat) : vecMulN 24 #[] x = 0 := by
  unfold vecMulN
  have hf : (fun acc j => if x.testBit j = true then acc ^^^ ((#[] : Array Nat)[j]?.getD 0) else acc) =
      fun acc _ => acc := by
    funext acc j
    simp
  rw [hf]
  have : ∀ (l : List Nat) (acc : Nat), l.foldl (fun acc (_ : Nat) => acc) acc = acc := by
    intro l
    induction l with
    | nil => intro acc; rfl
    | cons j l ih => intro acc; exact ih acc
  exact this _ 0

theorem vm_cs {TL : List Nat} (hl : TL.length = 3) (a x : Nat) :
    vecMulN 24 (((TL.map (unpackR 24)).toArray).getD a #[]) x = vmT TL a x := by
  unfold vmT
  by_cases ha : a < 3
  · have hb : Nat.blt a 3 = true := Eq.mpr Nat.blt_eq ha
    rw [hb]
    change _ = vmF 24 (getL 0 TL a) x
    have hlt : a < (TL.map (unpackR 24)).toArray.size := by simpa [hl] using ha
    rw [getL_eq, List.getD_eq_getElem _ _ (by omega : a < TL.length), Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hlt, Option.getD_some,
      List.getElem_toArray, List.getElem_map, vecMulN_unpackR]
  · have hb : Nat.blt a 3 = false := by
      rw [Bool.eq_false_iff]
      intro e
      exact ha (Eq.mp Nat.blt_eq e)
    rw [hb]
    change _ = 0
    have hge : ¬ a < (TL.map (unpackR 24)).toArray.size := by simpa [hl] using ha
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega), Option.getD_none,
      vecMulN_empty]

theorem slot_eq {TL : List Nat} (hl : TL.length = 3) (b : List Nat) (s : Nat × Nat) :
    slotN (TL.map (unpackR 24)).toArray b s = slotK TL b s := by
  unfold slotN slotK
  rw [vm_cs hl, getD_eq_getL]

theorem fN_eq {TL : List Nat} (hl : TL.length = 3) (b : List Nat) (F : List (Nat × Nat)) :
    fN (TL.map (unpackR 24)).toArray b F = fK TL b F := by
  unfold fN fK
  simp only [slot_eq hl]
  rfl

theorem combN_eq {TL : List Nat} (hl : TL.length = 3) (S : List Nat) (F x : Nat) :
    combN (TL.map (unpackR 24)).toArray S F x = combK TL S F x := by
  unfold combN combK
  simp only [vm_cs hl]
  rfl

theorem certVecs_size : certVecs.size = 98280 := by
  unfold certVecs
  simp [CFSG.Monster.B.Co2.Native.hexTable]

theorem xAt_eq {i : Nat} (hi : i < 98280) : xAt CV.F i = certVecs[i]! := by
  have h := certVecs_get (j := i / 840) (k := i % 840) (by omega) (Nat.mod_lt _ (by decide))
  rw [Nat.div_add_mod] at h
  rw [h]
  rfl

theorem entsK_sound {c : Nat} : ∀ {g : List Nat}, entsK CV.F c g = true →
    ∀ e ∈ g, e >>> 12 < 98280 ∧ xAt CV.F (e >>> 12) = c * 4096 + (e &&& 4095)
  | [], _ => by simp
  | e :: g, h => by
    change andB (Nat.blt (Nat.shiftRight e 12) 98280) (andB (Nat.beq (xAt CV.F (Nat.shiftRight e 12))
      (Nat.add (Nat.shiftLeft c 12) (Nat.land e 4095))) (entsK CV.F c g)) = true at h
    obtain ⟨h1, h⟩ := andB_true h
    obtain ⟨h2, h3⟩ := andB_true h
    intro e' he'
    rcases List.mem_cons.1 he' with rfl | he'
    · refine ⟨Eq.mp Nat.blt_eq h1, ?_⟩
      change xAt CV.F (Nat.shiftRight e' 12) = _
      rw [Nat.eq_of_beq_eq_true h2]
      change c <<< 12 + (e' &&& 4095) = _
      rw [Nat.shiftLeft_eq]
    · exact entsK_sound h3 e' he'

theorem chunksK_sound : ∀ {G : List (List Nat)} {c : Nat}, chunksK XB CV.F G c = true →
    ∀ t (ht : t < G.length), XB (c + t) = orBits G[t] ∧ entsK CV.F (c + t) G[t] = true
  | [], _, _ => fun t ht => absurd ht (Nat.not_lt_zero _)
  | g :: G, c, h => by
    change andB (Nat.beq (XB c) (orBits g)) (andB (entsK CV.F c g)
      (CFSG.KC.M1F2.strictB (Nat.succ c) (chunksK XB CV.F G))) = true at h
    obtain ⟨h1, h⟩ := andB_true h
    obtain ⟨h2, h3⟩ := andB_true h
    rw [strictB_eq'] at h3
    intro t ht
    cases t with
    | zero => exact ⟨Nat.eq_of_beq_eq_true h1, h2⟩
    | succ t =>
      have := chunksK_sound h3 t (by simpa using ht)
      have e : c + (t + 1) = Nat.succ c + t := by omega
      rw [List.getElem_cons_succ, e]
      exact this

theorem testBit_orBits (m : Nat) : ∀ (g : List Nat), (orBits g).testBit m = true →
    ∃ e ∈ g, e &&& 4095 = m
  | [], h => by
    change (0 : Nat).testBit m = true at h
    simp at h
  | e :: g, h => by
    change (Nat.lor (Nat.shiftLeft 1 (Nat.land e 4095)) (orBits g)).testBit m = true at h
    change ((1 <<< (e &&& 4095)) ||| orBits g).testBit m = true at h
    rw [Nat.testBit_or, Bool.or_eq_true] at h
    rcases h with h | h
    · rw [Nat.testBit_shiftLeft] at h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨hle, h1⟩ := h
      have : m - (e &&& 4095) = 0 := by
        by_contra hne
        rw [Nat.testBit_one_eq_true_iff_self_eq_zero] at h1
        exact hne h1
      exact ⟨e, List.mem_cons_self, by omega⟩
    · obtain ⟨e', he', h'⟩ := testBit_orBits m g h
      exact ⟨e', List.mem_cons_of_mem _ he', h'⟩

theorem memK_of_mem {v : Nat} (hv : v ∈ certVecs.toList) : memK XB v = true := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hv
  have hi' : i < 98280 := by simpa [certVecs_size] using hi
  have hj : i / 840 < 117 := by omega
  have hk : i % 840 < 840 := Nat.mod_lt _ (by decide)
  have e := certVecs_get hj hk
  rw [Nat.div_add_mod] at e
  have hX : allXK XB CV.F 0 39 = true ∧ allXK XB CV.F 39 39 = true ∧ allXK XB CV.F 78 39 = true :=
    ⟨kX0, kX1, kX2⟩
  have key : ∀ a, allXK XB CV.F a 39 = true → a ≤ i / 840 → i / 840 < a + 39 →
      memK XB (pg 24 (CFSG.KS.mask 24) (CV.F (i / 840)) (i % 840)) = true := by
    intro a ha h1 h2
    have := allN_true' (allN_true' ha (i / 840 - a) (by omega)) (i % 840) hk
    have e : Nat.add a (i / 840 - a) = i / 840 := Nat.add_sub_cancel' h1
    rwa [e] at this
  have hm : memK XB (pg 24 (CFSG.KS.mask 24) (CV.F (i / 840)) (i % 840)) = true := by
    rcases Nat.lt_or_ge (i / 840) 39 with h | h
    · exact key 0 hX.1 (Nat.zero_le _) (by omega)
    rcases Nat.lt_or_ge (i / 840) 78 with h' | h'
    · exact key 39 hX.2.1 h (by omega)
    · exact key 78 hX.2.2 h' (by omega)
  rw [Array.getElem_toList, ← getElem!_pos certVecs i hi, e]
  exact hm

theorem mem_of_memK {v : Nat} (hv : memK XB v = true) : v ∈ certVecs.toList := by
  change andB (Nat.blt v 16777216) (bit (XB (Nat.shiftRight v 12)) (Nat.land v 4095)) = true at hv
  obtain ⟨h1, h2⟩ := andB_true hv
  have hv24 := Eq.mp Nat.blt_eq h1
  have hG := kG
  simp only [Bool.and_eq_true, Nat.beq_eq] at hG
  obtain ⟨hlen, hch⟩ := hG
  have hc : v >>> 12 < K.G.length := by
    rw [hlen, Nat.shiftRight_eq_div_pow]
    omega
  obtain ⟨hx, he⟩ := chunksK_sound hch (v >>> 12) hc
  rw [Nat.zero_add] at hx he
  rw [bit_eq'] at h2
  change (XB (v >>> 12)).testBit (v &&& 4095) = true at h2
  rw [hx] at h2
  obtain ⟨e, hem, hel⟩ := testBit_orBits _ _ h2
  obtain ⟨hlt, hxa⟩ := entsK_sound he e hem
  rw [xAt_eq hlt, hel] at hxa
  have hvv : v >>> 12 * 4096 + (v &&& 4095) = v := by
    rw [Nat.shiftRight_eq_div_pow, Nat.and_two_pow_sub_one_eq_mod v 12]
    omega
  rw [hvv] at hxa
  have hi : e >>> 12 < certVecs.size := by rw [certVecs_size]; exact hlt
  rw [← hxa, getElem!_pos certVecs _ hi]
  exact Array.getElem_mem_toList hi

theorem mem_eq (v : Nat) : (xsSet ()).contains v = memK XB v := by
  rw [xsSet, Std.HashSet.contains_ofList]
  apply Bool.eq_iff_iff.2
  rw [List.contains_iff_mem]
  exact ⟨memK_of_mem, mem_of_memK⟩

theorem typN_eq (v : Nat) : typN (xsSet ()) v = typK XB v := by
  unfold typN typK
  rw [mem_eq]
  by_cases h : v = 0
  · subst h
    rfl
  · have hb : Nat.beq v 0 = false := by
      rw [Bool.eq_false_iff]
      intro e
      exact h (Nat.eq_of_beq_eq_true e)
    rw [hb, if_neg (by simpa using h)]
    cases memK XB v <;> rfl

theorem foldl_filter {α β : Type} (q : β → α → Bool) : ∀ (cs : List β) (l : List α),
    cs.foldl (fun cand c => cand.filter (q c)) l = l.filter (fun x => cs.all fun c => q c x)
  | [], l => by simp
  | c :: cs, l => by
    rw [List.foldl_cons, foldl_filter q cs, List.filter_filter]
    refine congrArg (List.filter · l) (funext fun x => ?_)
    rw [List.all_cons, Bool.and_comm]

theorem andB_eq' (a b : Bool) : andB a b = (a && b) := by cases a <;> rfl

theorem conds_all_eq (b : List Nat) (u x : Nat) : ∀ conds : List Cond,
    conds.all (fun c => typN (xsSet ()) (combN (K.T.map (unpackR 24)).toArray c.1
        (fN (K.T.map (unpackR 24)).toArray b c.2) x) ==
      typN (xsSet ()) (combN (K.T.map (unpackR 24)).toArray c.1
        (fN (K.T.map (unpackR 24)).toArray b c.2) u)) =
      condsK XB K.T (storeK XB K.T b u conds) x
  | [] => rfl
  | c :: conds => by
    have hl := kT'.2.2.2
    have hs : storeK XB K.T b u (c :: conds) =
        (typK XB (combK K.T c.1 (fK K.T b c.2) u) :: fK K.T b c.2 :: c.1) :: storeK XB K.T b u conds :=
      rfl
    rw [List.all_cons, conds_all_eq b u x conds, hs]
    change _ = andB (condK XB K.T x (typK XB (combK K.T c.1 (fK K.T b c.2) u) :: fK K.T b c.2 :: c.1))
      (condsK XB K.T (storeK XB K.T b u conds) x)
    rw [andB_eq', typN_eq, typN_eq, combN_eq hl, combN_eq hl, fN_eq hl, beq_nat]
    rfl

theorem cntChunk_eq (p : Nat → Bool) (P : Nat) :
    cntChunkK p P = cntN (fun k => p (pg 24 (CFSG.KS.mask 24) P k)) 840 := by
  have key : ∀ n, (Nat.rec (motive := fun _ => Nat) 0 (fun k acc => (fun v => Bool.rec
      (motive := fun _ => Nat) acc (Nat.succ acc) (p v))
      (pg 24 (CFSG.KS.mask 24) P k)) n : Nat) = cntN (fun k => p (pg 24 (CFSG.KS.mask 24) P k)) n := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      simp only [cntN]
      rw [← ih]
      by_cases h : p (pg 24 (CFSG.KS.mask 24) P n) = true
      · simp only [h, ↓reduceIte]
      · simp only [h, Bool.false_eq_true, ↓reduceIte]
  unfold cntChunkK
  exact key 840

theorem range_filter_length (p : Nat → Bool) (f : Nat → Nat) : ∀ n,
    (((List.range n).map f).filter p).length = cntN (fun i => p (f i)) n
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.filter_append, List.length_append,
      range_filter_length p f n]
    simp only [cntN, List.map_cons, List.map_nil]
    by_cases h : p (f n) = true
    · simp [h]
    · simp [h]

theorem certVecs_list : certVecs.toList = (List.range 98280).map fun i => certVecs[i]! := by
  apply List.ext_getElem
  · simp [certVecs_size]
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_range, Array.getElem_toList]
    rw [getElem!_pos certVecs i (by simpa using h1)]

theorem filter_length (p : Nat → Bool) :
    (certVecs.toList.filter p).length = cntTabK p CV.F 0 117 := by
  rw [certVecs_list, range_filter_length]
  have h98 : (98280 : Nat) = 840 * 117 := rfl
  rw [h98, cntN_blocks]
  have key : ∀ m ≤ 117, bsum (fun i => p certVecs[i]!) 840 m = cntTabK p CV.F 0 m := by
    intro m
    induction m with
    | zero => intro _; rfl
    | succ m ih =>
      intro hm
      rw [bsum, ih (by omega)]
      change _ = cntChunkK p (CV.F (Nat.add 0 m)) + _
      rw [cntChunk_eq, Nat.add_eq, Nat.zero_add]
      congr 1
      refine cntN_congr 840 fun k hk => ?_
      rw [certVecs_get (by omega) hk]
  exact key 117 le_rfl

theorem cf_get {i : Nat} (hi : i < 9) :
    K.CF.getD i [] = storeK XB K.T (base.take i) (base.getD i 0) (conds.getD i []) := by
  rw [of_decide_eq_true kCF, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range hi]
  rfl

theorem lvl_eq {i : Nat} (hi : i < 9) :
    lvlOK (xsSet ()) (K.T.map (unpackR 24)).toArray base i (conds.getD i []) (cnts.getD i 0) =
      (memK XB (base.getD i 0) &&
        decide (cntTabK (condsK XB K.T (K.CF.getD i [])) CV.F 0 117 ≤ cnts.getD i 0)) := by
  unfold lvlOK candList
  rw [mem_eq, foldl_filter (fun (c : Cond) x =>
    typN (xsSet ()) (combN (K.T.map (unpackR 24)).toArray c.1
      (fN (K.T.map (unpackR 24)).toArray (base.take i) c.2) x) ==
    typN (xsSet ()) (combN (K.T.map (unpackR 24)).toArray c.1
      (fN (K.T.map (unpackR 24)).toArray (base.take i) c.2) (base.getD i 0)))]
  simp only [conds_all_eq]
  rw [filter_length, cf_get hi]

theorem cntTab_add (p : Nat → Bool) (F : Nat → Nat) (a m : Nat) : ∀ n,
    cntTabK p F a (m + n) = cntTabK p F (a + m) n + cntTabK p F a m
  | 0 => by
    change cntTabK p F a m = 0 + cntTabK p F a m
    rw [Nat.zero_add]
  | n + 1 => by
    change Nat.add (cntChunkK p (F (Nat.add a (m + n)))) (cntTabK p F a (m + n)) =
      Nat.add (cntChunkK p (F (Nat.add (a + m) n))) (cntTabK p F (a + m) n) + cntTabK p F a m
    rw [cntTab_add p F a m n, Nat.add_eq, Nat.add_eq, Nat.add_eq, Nat.add_eq, Nat.add_assoc a m n,
      Nat.add_assoc]

theorem cntTab_blocks (p : Nat → Bool) (F : Nat → Nat) : ∀ k,
    cntTabK p F 0 (13 * k) = ((List.range k).map fun c => cntTabK p F (13 * c) 13).sum
  | 0 => rfl
  | k + 1 => by
    rw [Nat.mul_succ, cntTab_add, Nat.zero_add, cntTab_blocks p F k, List.range_succ,
      List.map_append, List.sum_append]
    simp [Nat.add_comm]

theorem sum_getL (l : List Nat) : ((List.range l.length).map fun c => getL 0 l c).sum = l.sum := by
  congr 1
  apply List.ext_getElem (by simp)
  intro c h1 h2
  simp only [List.getElem_map, List.getElem_range]
  rw [getL_eq]
  simp [h2]

theorem chunks : ∀ n < 81, lvlChunkK XB K.T K.CF CV.F K.CN n = true := by
  intro n hn
  rcases Nat.lt_or_ge n 27 with h | h
  · interval_cases n
    exacts [chunkA0, chunkA1, chunkA2, chunkA3, chunkA4, chunkA5, chunkA6, chunkA7, chunkA8,
      chunkA9, chunkA10, chunkA11, chunkA12, chunkA13, chunkA14, chunkA15, chunkA16, chunkA17,
      chunkA18, chunkA19, chunkA20, chunkA21, chunkA22, chunkA23, chunkA24, chunkA25, chunkA26]
  rcases Nat.lt_or_ge n 54 with h' | h'
  · interval_cases n
    exacts [chunkB27, chunkB28, chunkB29, chunkB30, chunkB31, chunkB32, chunkB33, chunkB34,
      chunkB35, chunkB36, chunkB37, chunkB38, chunkB39, chunkB40, chunkB41, chunkB42, chunkB43,
      chunkB44, chunkB45, chunkB46, chunkB47, chunkB48, chunkB49, chunkB50, chunkB51, chunkB52,
      chunkB53]
  · interval_cases n
    exacts [chunkC54, chunkC55, chunkC56, chunkC57, chunkC58, chunkC59, chunkC60, chunkC61,
      chunkC62, chunkC63, chunkC64, chunkC65, chunkC66, chunkC67, chunkC68, chunkC69, chunkC70,
      chunkC71, chunkC72, chunkC73, chunkC74, chunkC75, chunkC76, chunkC77, chunkC78, chunkC79,
      chunkC80]

theorem kNF {i : Nat} (hi : i < 9) : memK XB (base.getD i 0) = true ∧
    (K.CN.getD i []).length = 9 ∧ (K.CN.getD i []).sum ≤ cnts.getD i 0 := by
  have h := kN
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  have h' := allN_true' h.2 i hi
  simp only [Bool.and_eq_true, Nat.beq_eq] at h'
  exact ⟨h'.1.1, h'.1.2, Nat.le_of_ble_eq_true h'.2⟩

theorem lvl_ok {i : Nat} (hi : i < 9) :
    lvlOK (xsSet ()) (K.T.map (unpackR 24)).toArray base i (conds.getD i []) (cnts.getD i 0) =
      true := by
  obtain ⟨hm, hl, hs⟩ := kNF hi
  rw [lvl_eq hi, hm, Bool.true_and, decide_eq_true_iff]
  have h117 : (117 : Nat) = 13 * 9 := rfl
  rw [h117, cntTab_blocks]
  have hb : ∀ c < 9, cntTabK (condsK XB K.T (K.CF.getD i [])) CV.F (13 * c) 13 =
      getL 0 (K.CN.getD i []) c := by
    intro c hc
    have := chunks (9 * i + c) (by omega)
    unfold lvlChunkK at this
    have e1 : Nat.div (9 * i + c) 9 = i := by
      change (9 * i + c) / 9 = i
      omega
    have e2 : Nat.mod (9 * i + c) 9 = c := by
      change (9 * i + c) % 9 = c
      omega
    rw [e1, e2] at this
    exact Nat.eq_of_beq_eq_true this
  rw [List.map_congr_left fun c hc => hb c (List.mem_range.1 hc), ← hl, sum_getL]
  exact hs

theorem slotK_lt (b : List Nat) (s : Nat × Nat) : slotK K.T b s < 2 ^ 24 := by
  unfold slotK vmT
  cases Nat.blt s.2 3
  · exact Nat.two_pow_pos 24
  · exact vmF_lt 24 _ _

theorem span_ok : spanOK (K.T.map (unpackR 24)).toArray 3 base span comb = true := by
  have hl := kT'.2.2.2
  have h := kSpan
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨⟨⟨hs, hc⟩, ha⟩, hv⟩ := h
  unfold spanOK
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range, beq_iff_eq]
  refine ⟨⟨⟨hs, hc⟩, ?_⟩, ?_⟩
  · intro s hm
    have := List.all_eq_true.1 ha s hm
    simp only [Bool.and_eq_true] at this
    exact ⟨Eq.mp Nat.blt_eq this.1, Eq.mp Nat.blt_eq this.2⟩
  · intro l hl'
    have hm : span.map (slotN (K.T.map (unpackR 24)).toArray base) = span.map (slotK K.T base) :=
      List.map_congr_left fun s _ => slot_eq hl base s
    rw [hm, toArray_packL (by rw [List.length_map, hs]) (fun v hv => by
      obtain ⟨s, -, rfl⟩ := List.mem_map.1 hv
      exact slotK_lt base s), vecMulN_unpackR]
    have := allN_true' hv l hl'
    rw [Nat.eq_of_beq_eq_true this]
    rfl

open Certificates in
open CFSG.HardMathSupport.Dickson.I271.TabCo1ThreeD in
theorem c17591 : threeDCheck () = true := by
  have hl := kT'.2.2.2
  rw [threeDCheck, cs_eq]
  unfold boundOK
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range]
  refine ⟨⟨⟨⟨⟨by simp [hl], by decide⟩, by decide⟩, ?_⟩, span_ok⟩, by decide⟩
  intro i hi
  exact lvl_ok hi

end CertificateChecks.KernelCo1B.Bound17591

end
