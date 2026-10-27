module

public import Certificates.Kernel.Co2Smith.NJ3K
public import CFSG.Sporadic.Co2Smith.GlNJInputs
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat

public section

namespace CertificateChecks.KernelCo2Smith

open CFSG.Sporadic.Co2Smith.Native CFSG.Certificates.Native

theorem njIns_eq (a : Nat) : ∀ l : List Nat, njIns a l = l.orderedInsert (· ≤ ·) a
  | [] => by
    rw [List.orderedInsert_nil]
    rfl
  | b :: t => by
    have e : njIns a (b :: t) = bif Nat.ble a b then a :: b :: t else b :: njIns a t := rfl
    rw [e, njIns_eq a t, List.orderedInsert_cons]
    by_cases h : a ≤ b
    · have hb : Nat.ble a b = true := by simpa using h
      rw [hb, if_pos h]
      rfl
    · have hb : Nat.ble a b = false := Bool.eq_false_iff.2 fun hh => h (by simpa using hh)
      rw [hb, if_neg h]
      rfl

theorem njSort_eq : ∀ l : List Nat, njSort l = l.insertionSort (· ≤ ·)
  | [] => by
    rw [List.insertionSort_nil]
    rfl
  | a :: l => by
    have e : njSort (a :: l) = njIns a (njSort l) := rfl
    rw [e, njSort_eq l, njIns_eq, List.insertionSort_cons]

theorem sort_eq (l : List Nat) : l.mergeSort (fun a b => decide (a ≤ b)) = njSort l := by
  rw [njSort_eq]
  have e : (fun a b : Nat => decide (a ≤ b)) = fun a b => decide ((· ≤ ·) a b) := rfl
  rw [e, List.mergeSort_eq_insertionSort]

theorem get!_eq_getD {α : Type} [Inhabited α] (l : List α) (i : Nat) :
    l[i]! = l.getD i default := by
  simp only [List.getD_eq_getElem?_getD, getElem!_def]
  cases l[i]? <;> rfl

theorem toArray_get! {α : Type} [Inhabited α] (l : List α) (i : Nat) :
    l.toArray[i]! = l.getD i default := by
  rw [← get!_eq_getD]
  simp [getElem!_def]

theorem card_filter_fin {n : Nat} (l : List Nat) (hn : l.length = n) (p : Nat → Bool) :
    (Finset.univ.filter fun k : Fin n => p (l.getD k.val 0) = true).card = l.countP p := by
  subst hn
  rw [Finset.card_filter, Fin.sum_univ_eq_sum_range (fun i => if p (l.getD i 0) = true then 1 else 0)]
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.length_cons, Finset.sum_range_succ', List.countP_cons, ← ih]
    simp

theorem om_length : glNJOm.length = 77 := by decide

theorem om_mask : ((List.range 1024).all fun y => glNJOm.contains y == njOmM.testBit y) = true := by
  decide +kernel

theorem om_lt : glNJOm.all (· < 1024) = true := by decide

theorem omT_get {y : Nat} (hy : y < 1024) : glNJOmT[y]! = njOmM.testBit y := by
  have h := om_mask
  simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at h
  rw [← h y hy]
  unfold glNJOmT
  rw [getElem!_pos _ y (by simpa using hy)]
  simp

theorem omGet_lt (k : Nat) : glNJOm[k]! < 1024 := by
  by_cases hk : k < 77
  · have h := om_lt
    simp only [List.all_eq_true, decide_eq_true_eq] at h
    rw [getElem!_pos glNJOm k (by rw [om_length]; exact hk)]
    exact h _ (List.getElem_mem _)
  · rw [getElem!_neg glNJOm k (by rw [om_length]; exact hk)]
    decide

theorem N_eq {x : Nat} (hx : x < 1024) : glNJN glNJOmT x = njNK x := by
  unfold glNJN njNK
  have e : ∀ k : Fin 77, glNJOmT[glNJOm[k.val]! ^^^ x]! = true ↔
      (fun m => glNJOmT[m ^^^ x]!) (glNJOm.getD k.val 0) = true := by
    intro k
    rw [get!_eq_getD]
    rfl
  simp only [e]
  refine (card_filter_fin glNJOm om_length (fun m => glNJOmT[m ^^^ x]!)).trans ?_
  apply List.countP_congr
  intro m hm
  have hm' : m < 1024 := by
    have h := om_lt
    simp only [List.all_eq_true, decide_eq_true_eq] at h
    exact h m hm
  rw [omT_get (Nat.xor_lt_two_pow (n := 10) hm' hx)]

theorem nbK_length : njNbK.length = 77 := by simp [njNbK]

theorem nbr_eq : glNJNbr = njNbK.toArray := by
  apply Array.ext
  · simp [glNJNbr, nbK_length]
  · intro i h1 h2
    have hi : i < 77 := by simpa [glNJNbr] using h1
    simp only [glNJNbr, njNbK, Array.getElem_ofFn, List.getElem_toArray, List.getElem_map,
      List.getElem_range]
    apply List.filter_congr
    intro b _
    rw [N_eq (Nat.xor_lt_two_pow (n := 10) (omGet_lt i) (omGet_lt b))]

theorem refineStep_eq (nb : List (List Nat)) (c : List Nat) :
    refineStep 77 nb.toArray c.toArray = (njStepK nb c).toArray := by
  apply Array.ext
  · simp [refineStep, njStepK]
  · intro i h1 h2
    simp only [refineStep, njStepK, nbrColours, Array.getElem_ofFn, List.getElem_toArray,
      List.getElem_map, List.getElem_range, toArray_get!, sort_eq]
    rfl

theorem refineIter_eq (nb : List (List Nat)) (c : List Nat) :
    ∀ k, refineIter 77 nb.toArray c.toArray k = (njIterK nb c k).toArray
  | 0 => rfl
  | k + 1 => by
    change refineStep 77 nb.toArray (refineIter 77 nb.toArray c.toArray k) = _
    rw [refineIter_eq nb c k, refineStep_eq]
    rfl

theorem individualize_eq (s : Nat) : individualize 77 glNJBase s = (njIndK s).toArray := by
  apply Array.ext
  · simp [individualize, njIndK]
  · intro i h1 h2
    simp only [individualize, njIndK, Array.getElem_ofFn, List.getElem_toArray, List.getElem_map,
      List.getElem_range]
    rfl

theorem colour_eq (s : Nat) : glNJColour njNbK.toArray s = (njColK njNbK s).toArray := by
  unfold glNJColour njColK
  rw [individualize_eq, refineIter_eq]

theorem stepK_length (nb : List (List Nat)) (c : List Nat) : (njStepK nb c).length = 77 := by
  simp only [njStepK, List.length_map, List.length_range]

theorem colK_length (nb : List (List Nat)) (s : Nat) : (njColK nb s).length = 77 := by
  change (njStepK nb (njIterK nb (njIndK s) 2)).length = 77
  exact stepK_length _ _

theorem classCount_eq (s v : Nat) :
    glNJClassCount (njColK njNbK s).toArray v = njCntK (njColK njNbK s) v := by
  unfold glNJClassCount njCntK
  have e : ∀ w : Fin 77, (njColK njNbK s).toArray[w.val]! = (njColK njNbK s).toArray[v]! ↔
      (fun x => x == (njColK njNbK s).getD v 0) ((njColK njNbK s).getD w.val 0) = true := by
    intro w
    rw [toArray_get!, toArray_get!, beq_iff_eq]
    rfl
  simp only [e]
  exact card_filter_fin (njColK njNbK s) (colK_length _ _) (fun x => x == (njColK njNbK s).getD v 0)

theorem nj3_ok : glNJ3OK = true := by
  rw [← njRef_k]
  unfold glNJ3OK glNJRefOK njRefK
  dsimp only
  rw [nbr_eq]
  simp only [colour_eq, classCount_eq]
  simp only [List.size_toArray, toArray_get!, List.toList_toArray, colK_length, beq_self_eq_true,
    Bool.and_true]
  rfl

end CertificateChecks.KernelCo2Smith
