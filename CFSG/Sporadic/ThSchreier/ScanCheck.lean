
module

public import CFSG.Sporadic.ThSchreier.UASpaceBase
public import CFSG.Sporadic.ThSchreier.TransporterBase

public section

namespace CFSG.Sporadic.ThSchreier

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native

@[expose] def discOf (pl : ℕ) : ℕ := 2 * treePar pl + (treeLab pl - 1)

@[expose] def bfsOrderAt (n : ℕ) (tA tB tP : Table) (k : ℕ) : Bool :=
  (k == 0 || n ≤ k + 1 || decide (discOf (ap tP k) < discOf (ap tP (k + 1)))) &&
    (ap tA k == 0 || decide (discOf (ap tP (ap tA k)) ≤ 2 * k)) &&
    (ap tB k == 0 || decide (discOf (ap tP (ap tB k)) ≤ 2 * k + 1))

@[expose] def countFixedT (n : ℕ) (t : Table) : ℕ :=
  Nat.fold n (fun i _ c => if ap t i == i then c + 1 else c) 0

@[noinline, expose] def scanChecks (st : BFSState) (fT uT : Array V4) (fl il : Array ℕ)
    (ip : Array Key) (sk : Key) (si : ℕ) : Bool :=
  let n := st.count
  let tA := tblOfBytes n st.alpha
  let tB := tblOfBytes n st.beta
  let tP := tblOfBytes n st.par
  st.alpha.size == 4 * n && allIn 0 n (bfsOrderAt n tA tB tP) &&
    countFixedT n tA == fl.size &&
    allIn 0 fl.size (fun k => decide (fl[k]! < n) && ap tA fl[k]! == fl[k]!) &&
    allIn 0 (fl.size - 1) (fun k => decide (fl[k]! < fl[k + 1]!)) &&
    allIn 0 fl.size (fun k =>
      (inUAT uT (imageKey fT (readKey st.keys fl[k]!)).u &&
        inUAT uT (imageKey fT (readKey st.keys fl[k]!)).v) == il.contains fl[k]!) &&
    allIn 0 il.size (fun k => decide (il[k]! < n) &&
      (imageKey fT (readKey st.keys il[k]!)).beq ip[k]! &&
      inUAT uT ip[k]!.u && inUAT uT ip[k]!.v) &&
    allIn 0 (il.size - 1) (fun k => decide (il[k]! < il[k + 1]!)) &&
    decide (si < n) && (imageKey fT (readKey st.keys si)).beq sk

@[expose] def centFixedArr : Array ℕ := centFixedIdx.toArray

@[expose] def centImageArr : Array ℕ := centImageIdx.toArray

@[expose] def centImageKeys : Array Key :=
  Array.ofFn (n := 120) fun k =>
    ⟨v4OfNat (centImageRows.getD (2 * k.val) 0), v4OfNat (centImageRows.getD (2 * k.val + 1) 0)⟩

theorem countFixedT_eq (n : ℕ) (t : Table) :
    countFixedT n t = ((Finset.range n).filter fun i => ap t i = i).card := by
  unfold countFixedT
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.fold_succ, ih, Finset.range_add_one, Finset.filter_insert]
    by_cases h : ap t n = n
    · rw [ite_eq_left (by simpa using h), ite_eq_left h,
        Finset.card_insert_of_notMem (by simp)]
    · rw [ite_eq_right (by simpa using h), ite_eq_right h]

structure ScanFacts (st : BFSState) (fT uT : Array V4) (fl il : Array ℕ) (ip : Array Key)
    (sk : Key) (si : ℕ) : Prop where
  alphaSize : st.alpha.size = 4 * st.count
  mono : ∀ k, 1 ≤ k → k + 1 < st.count →
    discOf (readU32 st.par k) < discOf (readU32 st.par (k + 1))
  discA : ∀ k < st.count, readU32 st.alpha k < st.count →
    readU32 st.alpha k = 0 ∨ discOf (readU32 st.par (readU32 st.alpha k)) ≤ 2 * k
  discB : ∀ k < st.count, readU32 st.beta k < st.count →
    readU32 st.beta k = 0 ∨ discOf (readU32 st.par (readU32 st.beta k)) ≤ 2 * k + 1
  fixedCount : ((Finset.range st.count).filter fun i => readU32 st.alpha i = i).card = fl.size
  fixedMem : ∀ k < fl.size, fl[k]! < st.count ∧ readU32 st.alpha fl[k]! = fl[k]!
  fixedSorted : ∀ k, k + 1 < fl.size → fl[k]! < fl[k + 1]!
  fixedImage : ∀ k < fl.size,
    (inUAT uT (imageKey fT (readKey st.keys fl[k]!)).u &&
      inUAT uT (imageKey fT (readKey st.keys fl[k]!)).v) = il.contains fl[k]!
  imageMem : ∀ k < il.size, il[k]! < st.count ∧
    imageKey fT (readKey st.keys il[k]!) = ip[k]! ∧ inUAT uT ip[k]!.u = true ∧
    inUAT uT ip[k]!.v = true
  imageSorted : ∀ k, k + 1 < il.size → il[k]! < il[k + 1]!
  star : si < st.count ∧ imageKey fT (readKey st.keys si) = sk

theorem scanChecks_spec {st : BFSState} {fT uT : Array V4} {fl il : Array ℕ} {ip : Array Key}
    {sk : Key} {si : ℕ} (h : scanChecks st fT uT fl il ip sk si = true) :
    ScanFacts st fT uT fl il ip sk si := by
  unfold scanChecks at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hsize, hord⟩, hcnt⟩, hfm⟩, hfs⟩, hfi⟩, him⟩, his⟩, hsi⟩, hsk⟩ := h
  have hord' := allIn_eq_true.1 hord
  have hA (i : ℕ) (hi : i < st.count) :
      ap (tblOfBytes st.count st.alpha) i = readU32 st.alpha i := ap_tblOfBytes _ hi
  have hB (i : ℕ) (hi : i < st.count) :
      ap (tblOfBytes st.count st.beta) i = readU32 st.beta i := ap_tblOfBytes _ hi
  have hP (i : ℕ) (hi : i < st.count) :
      ap (tblOfBytes st.count st.par) i = readU32 st.par i := ap_tblOfBytes _ hi
  refine ⟨hsize, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ⟨hsi, (Key.beq_iff).1 hsk⟩⟩
  · intro k hk1 hk2
    have h1 := hord' k (Nat.zero_le _) (by omega)
    unfold bfsOrderAt at h1
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at h1
    rcases h1.1.1 with (h0 | hle) | hlt
    · omega
    · omega
    · rwa [hP k (by omega), hP (k + 1) hk2] at hlt
  · intro k hk hak
    have h1 := hord' k (Nat.zero_le _) hk
    unfold bfsOrderAt at h1
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at h1
    rw [hA k hk] at h1
    rcases h1.1.2 with h0 | hle
    · exact Or.inl h0
    · right
      rwa [hP _ hak] at hle
  · intro k hk hbk
    have h1 := hord' k (Nat.zero_le _) hk
    unfold bfsOrderAt at h1
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at h1
    rw [hB k hk] at h1
    rcases h1.2 with h0 | hle
    · exact Or.inl h0
    · right
      rwa [hP _ hbk] at hle
  · rw [← hcnt, countFixedT_eq]
    congr 1
    apply Finset.filter_congr
    intro i hi
    rw [hA i (Finset.mem_range.1 hi)]
  · intro k hk
    have h1 := (allIn_eq_true.1 hfm) k (Nat.zero_le _) hk
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h1
    exact ⟨h1.1, by rw [← hA _ h1.1]; exact h1.2⟩
  · intro k hk
    have h1 := (allIn_eq_true.1 hfs) k (Nat.zero_le _) (by omega)
    simpa using h1
  · intro k hk
    have h1 := (allIn_eq_true.1 hfi) k (Nat.zero_le _) hk
    simpa using h1
  · intro k hk
    have h1 := (allIn_eq_true.1 him) k (Nat.zero_le _) hk
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
    exact ⟨h1.1.1.1, (Key.beq_iff).1 h1.1.1.2, h1.1.2, h1.2⟩
  · intro k hk
    have h1 := (allIn_eq_true.1 his) k (Nat.zero_le _) (by omega)
    simpa using h1

@[noinline, expose] def suborbitChecks (st : BFSState) (reps : List ℕ) : Bool :=
  let n := st.count
  let aT := tblOfBytes n st.alpha
  let bT := tblOfBytes n st.beta
  let biT := invT n bT
  (components n (wordT n (wordLetters aT bT biT) xWord)
    (wordT n (wordLetters aT bT biT) yWord)).reps.toList == reps

@[expose] def suborbitReps : List ℕ := [0, 1, 3, 4, 24, 29, 33, 121, 231, 1385, 10771]

@[noinline, expose] def thFullChecks (st : BFSState) (fT uT : Array V4) (fl il : Array ℕ)
    (ip : Array Key) (sk : Key) (si : ℕ) (reps : List ℕ) : Bool :=
  scanChecks st fT uT fl il ip sk si && suborbitChecks st reps

theorem suborbitChecks_spec (h : suborbitChecks (thBFS ()) suborbitReps = true) :
    compsT.reps.toList = suborbitReps := by
  unfold suborbitChecks at h
  rw [beq_iff_eq] at h
  unfold compsT mxT myT nT alphaT betaT betaInvT
  exact h

abbrev ThScanFacts : Prop :=
  ScanFacts (thBFS ()) (frTable (transposeRows fcRows)) (frTable rowsUAQ) centFixedArr
    centImageArr centImageKeys starKey 120754

end CFSG.Sporadic.ThSchreier
