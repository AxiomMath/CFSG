module

public import Certificates.Kernel.Co2Jc.OffK
public import Certificates.Kernel.Co2Jc.OffStep0
public import Certificates.Kernel.Co2Jc.OffStep1
public import Certificates.Kernel.Co2Jc.OffStep2
public import Certificates.Kernel.Co2Jc.OffStep3
public import Certificates.Kernel.Co2Jc.OffBound0
public import Certificates.Kernel.Co2Jc.OffBound1
public import CFSG.Certificates.Kernel.Co1BMulSound
public import Mathlib.Data.Fintype.Fin
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelCo2Jc

open CFSG.Sporadic.Co2Jc CFSG.Sporadic.Co2Jc.Native CFSG.KC.M1F2

theorem all_congr_mem {α : Type} {l : List α} {f g : α → Bool} (h : ∀ x ∈ l, f x = g x) :
    l.all f = l.all g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.all_cons, List.all_cons, h a List.mem_cons_self,
      ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

theorem foldl_xor_foldr (l : List Nat) (c : Nat → Bool) (g : Nat → Nat) (a : Nat) :
    l.foldl (fun acc i => if c i then acc ^^^ g i else acc) a =
      a ^^^ l.foldr (fun i acc => if c i then g i ^^^ acc else acc) 0 := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih =>
    rw [List.foldl_cons, ih, List.foldr_cons]
    cases c x <;> simp [Nat.xor_assoc]

theorem colsOf_getD (A : Nat) {i : Nat} (hi : i < 10) :
    (colsOf A).getD i 0 = rowF 10 A i := by
  simp [colsOf, List.getD_eq_getElem?_getD, List.getElem?_range, hi]

theorem colAct_cols (A x : Nat) : colAct (tabF (colsOf A)) x = vmF 10 A x := by
  unfold colAct
  rw [CFSG.KC.F2W.vmF_rec, ← CFSG.KC.F2W.foldl_range_xor (rowF 10 A) (tabF (colsOf A)) x.testBit 10
    (fun j hj => colsOf_getD A hj), foldl_xor_foldr, Nat.zero_xor]

theorem compL_cols (A B : Nat) : compL (colsOf A) (colsOf B) = colsOf (mulF 10 B A) := by
  unfold compL
  conv_rhs => unfold colsOf
  refine List.map_congr_left fun i hi => ?_
  have hi' : i < 10 := List.mem_range.1 hi
  rw [colsOf_getD B hi', colAct_cols, CFSG.KC.F2W.mulF_eq_orN,
    CFSG.KC.F2W.rowF_orN 10 (fun i _ => CFSG.KC.F2W.vmF_lt 10 A (rowF 10 B i)) hi']

theorem tabs_eq : tabs = tabsL := beq_iff_eq.1 tabs_k

theorem tabsL_length : tabsL.length = 256 := by simp [tabsL]

theorem tabsL_getD {i : Nat} (hi : i < 256) : tabsL.getD i [] = colsOf (PT i) := by
  simp [tabsL, List.getD_eq_getElem?_getD, List.getElem?_range, hi]

theorem mul_facts {s i : Nat} (hs : s < 256) (hi : i < 256) :
    mulL s i < 256 ∧ PT (mulL s i) = mulF 10 (PT i) (PT s) := by
  have h := mul_k s hs
  unfold mulRowK at h
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨(h i hi).1, Nat.eq_of_beq_eq_true (h i hi).2⟩

theorem compL_get {s i : Nat} (hs : s < 256) (hi : i < 256) :
    compL (tabsL.getD s []) (tabsL.getD i []) = tabsL.getD (mulL s i) [] := by
  rw [tabsL_getD hs, tabsL_getD hi, compL_cols, ← (mul_facts hs hi).2,
    tabsL_getD (mul_facts hs hi).1]

theorem keys_nodup : (tabsL.map enc).Nodup := of_decide_eq_true keys_k

theorem enc_get {j : Nat} (hj : j < 256) :
    enc (tabsL.getD j []) = (tabsL.map enc)[j]'(by simp [tabsL_length, hj]) := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show j < tabsL.length by
    rw [tabsL_length]; exact hj)]

theorem mulIdxC_eq {s i : Nat} (hs : s < 256) (hi : i < 256) : mulIdxC s i = mulL s i := by
  unfold mulIdxC tabKeys
  rw [tabs_eq, compL_get hs hi, enc_get (mul_facts hs hi).1, keys_nodup.idxOf_getElem]

theorem tabsL_inj {i j : Nat} (hi : i < 256) (hj : j < 256)
    (e : tabsL.getD i [] = tabsL.getD j []) : i = j := by
  have := congrArg enc e
  rw [enc_get hi, enc_get hj] at this
  exact keys_nodup.getElem_inj.1 this

theorem gens_facts : gens.length = 4 ∧ ∀ k < 4, gI k < 256 ∧ gens.getD k [] = tabsL.getD (gI k) [] := by
  have h := gens_k
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    decide_eq_true_eq] at h
  exact ⟨h.1, fun k hk => ⟨(h.2 k hk).1, (h.2 k hk).2⟩⟩

theorem getD_mem {j : Nat} (hj : j < 256) : tabsL.getD j [] ∈ tabsL := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [tabsL_length]; exact hj),
    Option.getD_some]
  exact List.getElem_mem _

theorem subs_facts : subs.length = 715 ∧ ∀ l ∈ subs, ∀ i ∈ l, i < 256 := by
  have h := subs_k
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1, fun l hl => (h.2 l hl).1.2⟩

theorem card_filter_range (n : Nat) (p : Nat → Bool) :
    ((Finset.univ : Finset (Fin n)).filter fun m => p m.val = true).card =
      ((List.range n).filter p).length := by
  rw [Finset.card_filter]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc, List.range_succ, List.filter_append, List.length_append, ← ih]
    simp only [Fin.coe_castSucc, Fin.val_last, List.filter_cons, List.filter_nil]
    by_cases hp : p n = true <;> simp [hp]

theorem len_ok : lenOK = true := by
  unfold lenOK
  rw [tabs_eq, tabsL_length]
  rfl

theorem nodup_ok : nodupOK = true := by
  unfold nodupOK
  rw [tabs_eq]
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq]
  intro i hi j hj
  by_cases h : i = j
  · exact Or.inl h
  · exact Or.inr fun e => h (tabsL_inj hi hj e)

theorem tab_ok : tabOK = true := by
  unfold tabOK
  rw [tabs_eq]
  have h := tab_k
  simp only [Bool.and_eq_true] at h
  exact h.2

theorem words_ok : wordsOK = true := by decide +kernel

theorem parent_ok : parentOK = true := by
  have hp := par_k
  have ht := tab_k
  simp only [Bool.and_eq_true] at ht
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true,
    decide_eq_true_eq] at hp
  unfold parentOK
  rw [tabs_eq, tabsL_length]
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq,
    List.any_eq_true]
  refine ⟨beq_iff_eq.1 ht.1, fun i hi => ?_⟩
  rcases hp i hi with h0 | ⟨⟨hpi, hg⟩, hm⟩
  · exact Or.inl h0
  · right
    obtain ⟨hgi, hge⟩ := gens_facts.2 _ hg
    refine ⟨parL i, hpi, parG i, hg, ?_⟩
    rw [hge, compL_get hgi (by omega), Nat.eq_of_beq_eq_true hm]

theorem gens_ok : gensOK = true := by
  unfold gensOK
  rw [tabs_eq]
  decide +kernel

theorem closed_ok : closedOK = true := by
  unfold closedOK
  rw [tabs_eq, gens_facts.1]
  simp only [List.all_eq_true, List.mem_range]
  intro i hi k hk
  obtain ⟨hgi, hge⟩ := gens_facts.2 k hk
  rw [hge, compL_get hgi hi, List.contains_iff_mem]
  exact getD_mem (mul_facts hgi hi).1

theorem mulIdx_ok : mulIdxOK = true := by
  unfold mulIdxOK
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq]
  intro s hs i hi
  rw [mulIdxC_eq hs hi, tabs_eq, compL_get hs hi]
  exact ⟨(mul_facts hs hi).1, beq_self_eq_true _⟩

theorem subs_ok : subsOK = true := subs_k

theorem tab0 : tabsL.getD 0 [] = idTab := by
  have h := tab_k
  simp only [Bool.and_eq_true] at h
  exact beq_iff_eq.1 h.1

theorem ne_idTab {m : Nat} (hm : m < 256) (h0 : m ≠ 0) : tabsL.getD m [] ≠ idTab :=
  fun e => h0 (tabsL_inj hm (by norm_num) (e.trans tab0.symm))

theorem beq_tabs {a b : Nat} (ha : a < 256) (hb : b < 256) :
    (tabsL.getD a [] == tabsL.getD b []) = Nat.beq a b := by
  by_cases h : a = b
  · subst h
    rw [beq_self_eq_true, Nat.beq_refl]
  · rw [beq_false_of_ne (fun e => h (tabsL_inj ha hb e)),
      Bool.eq_false_iff.2 fun e => h (Nat.eq_of_beq_eq_true e)]

theorem subs_getD_mem {j : Nat} (hj : j < 715) : subs.getD j [] ∈ subs := by
  have hj' : j < subs.length := by rw [subs_facts.1]; exact hj
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj', Option.getD_some]
  exact List.getElem_mem _

theorem invol_ok : involOK = true := by
  have h := invol_k
  unfold involOK
  rw [tabs_eq]
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true'] at h ⊢
  intro s hs
  rw [compL_get hs hs]
  rcases h s hs with (h1 | h2) | h3
  · exact Or.inl (Or.inl (Or.inl h1))
  · exact Or.inl (Or.inr (bne_iff_ne.2 (ne_idTab (mul_facts hs hs).1
      (Nat.ne_of_beq_eq_false h2))))
  · exact Or.inr h3

theorem chunk_all {α : Type} {L : List α} {f : α → Bool} (hL : L.length ≤ 736)
    (h : ∀ c < 23, ((L.drop (32 * c)).take 32).all f = true) :
    ∀ j (hj : j < L.length), f L[j] = true := by
  intro j hj
  have hc : j / 32 < 23 := by omega
  have hr : j % 32 < ((L.drop (32 * (j / 32))).take 32).length := by
    simp only [List.length_take, List.length_drop]
    omega
  have e : ((L.drop (32 * (j / 32))).take 32)[j % 32] = L[j] := by
    simp only [List.getElem_take, List.getElem_drop, Nat.div_add_mod]
  rw [← e]
  exact List.all_eq_true.1 (h _ hc) _ (List.getElem_mem hr)

theorem step_all : ∀ c < 23, stepC c = true := by
  intro c hc
  rcases (by omega : c < 6 ∨ (6 ≤ c ∧ c < 12) ∨ (12 ≤ c ∧ c < 18) ∨ 18 ≤ c) with
    h | ⟨h1, h2⟩ | ⟨h1, h2⟩ | h
  · have := step0_k c h; rwa [Nat.zero_add] at this
  · have := step1_k (c - 6) (by omega); rwa [Nat.add_sub_cancel' h1] at this
  · have := step2_k (c - 12) (by omega); rwa [Nat.add_sub_cancel' h1] at this
  · have := step3_k (c - 18) (by omega); rwa [Nat.add_sub_cancel' h] at this

theorem bound_all : ∀ c < 23, boundC c = true := by
  intro c hc
  rcases (by omega : c < 12 ∨ 12 ≤ c) with h | h
  · have := bound0_k c h; rwa [Nat.zero_add] at this
  · have := bound1_k (c - 12) (by omega); rwa [Nat.add_sub_cancel' h] at this

theorem step_ok : stepOK = true := by
  unfold stepOK
  rw [List.all_eq_true]
  intro l hl
  obtain ⟨q, hq, rfl⟩ := List.getElem_of_mem hl
  have hlt : ∀ i ∈ subs[q], i < 256 := subs_facts.2 _ hl
  have ht : stepT subs[q] q = true := by
    have := chunk_all (L := subs.zipIdx) (f := fun p => stepT p.1 p.2)
      (by simp [subs_facts.1]) step_all q (by simpa using hq)
    simpa [List.getElem_zipIdx] using this
  unfold stepT at ht
  rw [List.all_eq_true] at ht ⊢
  intro s hs
  have hs' : s < 256 := List.mem_range.1 hs
  have h := ht s hs
  unfold commutesAll stepL
  rw [tabs_eq]
  have e1 : (subs[q].all fun i => compL (tabsL.getD s []) (tabsL.getD i []) ==
      compL (tabsL.getD i []) (tabsL.getD s [])) =
      subs[q].all fun i => Nat.beq (mulL s i) (mulL i s) :=
    all_congr_mem fun i hi => by
      rw [compL_get hs' (hlt i hi), compL_get (hlt i hi) hs',
        beq_tabs (mul_facts hs' (hlt i hi)).1 (mul_facts (hlt i hi) hs').1]
  have e2 : subs[q].map (mulIdxC s) = subs[q].map (mulL s) :=
    List.map_congr_left fun i hi => mulIdxC_eq hs' (hlt i hi)
  rw [compL_get hs' hs', e1, e2]
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h ⊢
  rcases h with (((h1 | h2) | h3) | h4) | ⟨h5, h6⟩
  · exact Or.inl (Or.inl (Or.inl (Or.inl h1)))
  · rw [Nat.eq_of_beq_eq_true h2]
    exact Or.inl (Or.inl (Or.inl (Or.inr (beq_iff_eq.2 tab0))))
  · exact Or.inl (Or.inl (Or.inr (bne_iff_ne.2 (ne_idTab (mul_facts hs' hs').1
      (Nat.ne_of_beq_eq_false h3)))))
  · exact Or.inl (Or.inr h4)
  · right
    rw [List.contains_iff_mem]
    unfold stepLK at h6
    rw [← beq_iff_eq.1 h6]
    exact subs_getD_mem h5

theorem nat_beq (a b : Nat) : (a == b) = Nat.beq a b := by
  by_cases h : a = b
  · subst h
    rw [beq_self_eq_true, Nat.beq_refl]
  · rw [beq_false_of_ne h, Bool.eq_false_iff.2 fun e => h (Nat.eq_of_beq_eq_true e)]

theorem fix_facts {i m : Nat} (hi : i < 256) (hm : m < 1024) :
    (FX i).testBit m = (vmF 10 (PT i) m == m) := by
  have h := fix_k i hi
  unfold fixRowK at h
  rw [nat_beq]
  exact beq_iff_eq.1 (List.all_eq_true.1 h m (List.mem_range.2 hm))

theorem andM_testBit (l : List Nat) {m : Nat} (hm : m < 1024) :
    (andM l).testBit m = l.all fun i => (FX i).testBit m := by
  have : ∀ (l : List Nat) (a : Nat), (l.foldl (fun acc i => acc &&& FX i) a).testBit m =
      (a.testBit m && l.all fun i => (FX i).testBit m) := by
    intro l
    induction l with
    | nil => intro a; simp
    | cons x l ih =>
      intro a
      rw [List.foldl_cons, ih, Nat.testBit_and, List.all_cons, Bool.and_assoc]
  unfold andM
  rw [this, Nat.testBit_two_pow_sub_one, decide_eq_true hm, Bool.true_and]

theorem strictB_eq (y : Nat) (k : Nat → Bool) : CFSG.KC.M1F2.strictB y k = k y := by
  cases y <;> rfl

theorem bound_ok : boundOK = true := by
  unfold boundOK
  rw [List.all_eq_true]
  intro l hl
  obtain ⟨q, hq, rfl⟩ := List.getElem_of_mem hl
  have hlt : ∀ i ∈ subs[q], i < 256 := subs_facts.2 _ hl
  have h := chunk_all (L := subs) (f := boundT) (by simp [subs_facts.1]) bound_all q hq
  unfold boundT at h
  rw [strictB_eq] at h
  have hf : fixCount subs[q] = ((List.range 1024).filter fun m =>
      (andM subs[q]).testBit m).length := by
    unfold fixCount
    rw [← card_filter_range]
    congr 1
    apply Finset.filter_congr
    intro m _
    unfold fixedB
    rw [tabs_eq, andM_testBit _ m.isLt, all_congr_mem fun i hi => by
      rw [tabsL_getD (hlt i hi), colAct_cols, ← fix_facts (hlt i hi) m.isLt]]
  rw [hf]
  exact h

theorem offenders_ok : offendersOK = true := by
  unfold offendersOK checks
  rw [len_ok, nodup_ok, tab_ok, words_ok, parent_ok, gens_ok, closed_ok, mulIdx_ok, subs_ok,
    invol_ok, step_ok, bound_ok]
  rfl

end CertificateChecks.KernelCo2Jc
