module

public import CFSG.OddTranspositions.PartThree.Twelve.ElevenFiveForm

public section

namespace CFSG.OddTranspositions.PartThree

open Matrix

@[expose] def e11G3 : Matrix (Fin 3) (Fin 3) (ZMod 5) :=
  !![1, 1, 0;
     1, 1, 2;
     0, 2, 1]

@[expose] def e11G3inv : Matrix (Fin 3) (Fin 3) (ZMod 5) :=
  !![2, 4, 2;
     4, 1, 3;
     2, 3, 0]

theorem e11G3_inv_mul : e11G3inv * e11G3 = 1 := by decide

theorem e11G3_symm (i j : Fin 3) : e11G3 i j = e11G3 j i := by
  fin_cases i <;> fin_cases j <;> rfl

theorem e11G3_self (i : Fin 3) : e11G3 i i = 1 := by
  fin_cases i <;> rfl

theorem e11G3_mulVec_apply (c : Fin 3 → ZMod 5) (j : Fin 3) :
    e11G3.mulVec c j = ∑ i, e11G3 j i * c i :=
  rfl

@[expose] def e11G (a : ZMod 5) : Matrix (Fin 4) (Fin 4) (ZMod 5) :=
  !![1, 1, 0, a;
     1, 1, 2, 0;
     0, 2, 1, 0;
     a, 0, 0, 1]

@[expose] def e11M (a : ZMod 5) (i : Fin 4) : Matrix (Fin 4) (Fin 4) (ZMod 5) :=
  fun r c => (if r = c then 1 else 0) - 2 * (if r = i then 1 else 0) * e11G a i c

@[expose] def e11Norm (a : ZMod 5) (v : Fin 4 → ZMod 5) : ZMod 5 :=
  v ⬝ᵥ (e11G a).mulVec v

@[expose] def e11Decode (c : Nat) : Fin 4 → ZMod 5 :=
  fun i => ((c / 5 ^ (i : Nat) % 5 : Nat) : ZMod 5)

@[expose] def e11Code (v : Fin 4 → ZMod 5) : Nat :=
  ∑ i : Fin 4, ZMod.val (v i) * 5 ^ (i : Nat)

@[expose] def e11MCode (a : ZMod 5) (i : Fin 4) (c : Nat) : Nat :=
  e11Code ((e11M a i).mulVec (e11Decode c))

@[expose] def e11SmulCode (lam : ZMod 5) (c : Nat) : Nat :=
  e11Code (lam • e11Decode c)

@[expose] def e11ImageMask (f : Nat → Nat) (m : Nat) : Nat :=
  (List.range 625).foldl (fun acc v => if m.testBit v then acc ||| (1 <<< f v) else acc) 0

@[expose] def e11ImageFuns (a : ZMod 5) : List (Nat → Nat) :=
  [e11MCode a 0, e11MCode a 1, e11MCode a 2, e11MCode a 3,
   e11SmulCode 1, e11SmulCode 2, e11SmulCode 3, e11SmulCode 4]

@[expose] def e11StepMask (a : ZMod 5) (m : Nat) : Nat :=
  m ||| (e11ImageFuns a).foldl (fun acc f => acc ||| e11ImageMask f m) 0

@[expose] def e11Reach (a : ZMod 5) : Nat :=
  (e11StepMask a)^[15] (1 <<< e11Code (Pi.single (0 : Fin 4) (1 : ZMod 5)))

@[expose] def e11Check (a : ZMod 5) : Bool :=
  let R := e11Reach a
  (List.range 625).all fun c =>
    !(e11Norm a (e11Decode c) == 1 || e11Norm a (e11Decode c) == 4) || R.testBit c

theorem e11Decode_code : ∀ v : Fin 4 → ZMod 5, e11Decode (e11Code v) = v := by
  decide +kernel

theorem e11Code_lt : ∀ v : Fin 4 → ZMod 5, e11Code v < 625 := by
  decide +kernel

theorem e11Check_ne_zero : ∀ a : ZMod 5, a ≠ 0 → e11Check a = true := by
  decide +kernel

@[expose] def e11StepSet (a : ZMod 5) (S : Set (Fin 4 → ZMod 5)) : Set (Fin 4 → ZMod 5) :=
  S ∪ ({w | ∃ i v, v ∈ S ∧ w = (e11M a i).mulVec v}
    ∪ {w | ∃ lam : ZMod 5, ∃ v, lam ≠ 0 ∧ v ∈ S ∧ w = lam • v})

@[expose] def e11ReachSet (a : ZMod 5) : Set (Fin 4 → ZMod 5) :=
  ⋃ n, (e11StepSet a)^[n] {Pi.single (0 : Fin 4) (1 : ZMod 5)}

theorem e11StepSet_mono {a : ZMod 5} {S T : Set (Fin 4 → ZMod 5)} (h : S ⊆ T) :
    e11StepSet a S ⊆ e11StepSet a T := by
  intro w hw
  simp only [e11StepSet, Set.mem_union, Set.mem_setOf_eq] at hw ⊢
  rcases hw with hw | hw | hw
  · exact Or.inl (h hw)
  · rcases hw with ⟨i, v, hv, rfl⟩
    exact Or.inr (Or.inl ⟨i, v, h hv, rfl⟩)
  · rcases hw with ⟨lam, v, hlam, hv, rfl⟩
    exact Or.inr (Or.inr ⟨lam, v, hlam, h hv, rfl⟩)

theorem e11ReachSet_subset {a : ZMod 5} {S : Set (Fin 4 → ZMod 5)}
    (h0 : Pi.single (0 : Fin 4) (1 : ZMod 5) ∈ S) (hclosed : e11StepSet a S ⊆ S) :
    e11ReachSet a ⊆ S := by
  intro w hw
  rcases Set.mem_iUnion.mp hw with ⟨n, hw⟩
  have hlay : ∀ n, (e11StepSet a)^[n] {Pi.single (0 : Fin 4) (1 : ZMod 5)} ⊆ S := by
    intro n
    induction n with
    | zero =>
        intro w hw
        simp only [Function.iterate_zero] at hw
        rw [hw]; exact h0
    | succ n ih =>
        rw [Function.iterate_succ_apply']
        exact fun w hw => hclosed (e11StepSet_mono ih hw)
  exact hlay n hw

theorem testBit_one_shiftLeft (k w : Nat) : (1 <<< k).testBit w = true ↔ w = k := by
  rw [Nat.one_shiftLeft, Nat.testBit_two_pow, decide_eq_true_eq]
  exact eq_comm

theorem e11ImageMask_foldl_testBit {f : Nat → Nat} {m : Nat} (l : List Nat) (acc : Nat) {w : Nat}
    (h : (l.foldl (fun acc v => if m.testBit v then acc ||| (1 <<< f v) else acc) acc).testBit w =
      true) :
    acc.testBit w = true ∨ ∃ v ∈ l, m.testBit v = true ∧ f v = w := by
  induction l generalizing acc with
  | nil => exact Or.inl h
  | cons a t ih =>
      simp only [List.foldl_cons] at h
      rcases ih (if m.testBit a then acc ||| (1 <<< f a) else acc) h with hacc | ⟨v, hv, hm, hf⟩
      · by_cases ha : m.testBit a
        · rw [if_pos ha] at hacc
          rw [Nat.testBit_lor, Bool.or_eq_true] at hacc
          rcases hacc with hacc | hshift
          · exact Or.inl hacc
          · exact Or.inr ⟨a, List.mem_cons_self, ha,
              ((testBit_one_shiftLeft (f a) w).mp hshift).symm⟩
        · rw [if_neg ha] at hacc
          exact Or.inl hacc
      · exact Or.inr ⟨v, List.mem_cons_of_mem a hv, hm, hf⟩

theorem e11ImageMask_testBit {f : Nat → Nat} {m w : Nat}
    (h : (e11ImageMask f m).testBit w = true) :
    ∃ v, m.testBit v = true ∧ f v = w := by
  rw [e11ImageMask] at h
  rcases e11ImageMask_foldl_testBit (List.range 625) 0 h with h0 | ⟨v, _, hm, hf⟩
  · simp at h0
  · exact ⟨v, hm, hf⟩

theorem e11FoldMask_testBit {fs : List (Nat → Nat)} {m : Nat} (acc : Nat) {w : Nat}
    (h : (fs.foldl (fun acc f => acc ||| e11ImageMask f m) acc).testBit w = true) :
    acc.testBit w = true ∨ ∃ f ∈ fs, ∃ v, m.testBit v = true ∧ f v = w := by
  induction fs generalizing acc with
  | nil => exact Or.inl h
  | cons f t ih =>
      simp only [List.foldl_cons] at h
      rcases ih (acc ||| e11ImageMask f m) h with hacc | ⟨g, hg, v, hm, hf⟩
      · rw [Nat.testBit_lor, Bool.or_eq_true] at hacc
        rcases hacc with hacc | himg
        · exact Or.inl hacc
        · rcases e11ImageMask_testBit himg with ⟨v, hm, hf⟩
          exact Or.inr ⟨f, List.mem_cons_self, v, hm, hf⟩
      · exact Or.inr ⟨g, List.mem_cons_of_mem f hg, v, hm, hf⟩

theorem e11StepMask_testBit (a : ZMod 5) (m w : Nat)
    (h : (e11StepMask a m).testBit w = true) :
    m.testBit w = true ∨
      (∃ i v, m.testBit v = true ∧ e11MCode a i v = w) ∨
      (∃ lam v, lam ≠ 0 ∧ m.testBit v = true ∧ e11SmulCode lam v = w) := by
  rw [e11StepMask] at h
  rw [Nat.testBit_lor, Bool.or_eq_true] at h
  rcases h with hm | hf
  · exact Or.inl hm
  · rcases e11FoldMask_testBit (m := m) 0 hf with h0 | ⟨f, hfmem, v, hm, hfv⟩
    · simp at h0
    · simp only [e11ImageFuns, List.mem_cons, List.mem_nil_iff, or_false] at hfmem
      rcases hfmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact Or.inr (Or.inl ⟨0, v, hm, hfv⟩)
      · exact Or.inr (Or.inl ⟨1, v, hm, hfv⟩)
      · exact Or.inr (Or.inl ⟨2, v, hm, hfv⟩)
      · exact Or.inr (Or.inl ⟨3, v, hm, hfv⟩)
      · exact Or.inr (Or.inr ⟨1, v, by decide, hm, hfv⟩)
      · exact Or.inr (Or.inr ⟨2, v, by decide, hm, hfv⟩)
      · exact Or.inr (Or.inr ⟨3, v, by decide, hm, hfv⟩)
      · exact Or.inr (Or.inr ⟨4, v, by decide, hm, hfv⟩)

theorem e11ReachSet_closed (a : ZMod 5) : e11StepSet a (e11ReachSet a) ⊆ e11ReachSet a := by
  intro w hw
  simp only [e11StepSet, Set.mem_union, Set.mem_setOf_eq] at hw
  rcases hw with hw | hw | hw
  · exact hw
  · rcases hw with ⟨i, v, hv, rfl⟩
    rcases Set.mem_iUnion.mp hv with ⟨n, hn⟩
    exact Set.mem_iUnion.mpr ⟨n + 1, by
      rw [Function.iterate_succ_apply']
      exact Or.inr (Or.inl ⟨i, v, hn, rfl⟩)⟩
  · rcases hw with ⟨lam, v, hlam, hv, rfl⟩
    rcases Set.mem_iUnion.mp hv with ⟨n, hn⟩
    exact Set.mem_iUnion.mpr ⟨n + 1, by
      rw [Function.iterate_succ_apply']
      exact Or.inr (Or.inr ⟨lam, v, hlam, hn, rfl⟩)⟩

theorem e11Reach_testBit (a : ZMod 5) (c : Nat)
    (h : (e11Reach a).testBit c = true) : e11Decode c ∈ e11ReachSet a := by
  rw [e11Reach] at h
  suffices ∀ n, ∀ c, ((e11StepMask a)^[n]
      (1 <<< e11Code (Pi.single (0 : Fin 4) (1 : ZMod 5)))).testBit c = true →
      e11Decode c ∈ e11ReachSet a by
    exact this 15 c h
  intro n
  induction n with
  | zero =>
      intro c hc
      have hceq : c = e11Code (Pi.single (0 : Fin 4) (1 : ZMod 5)) :=
        (testBit_one_shiftLeft _ _).mp hc
      rw [hceq, e11Decode_code]
      exact Set.mem_iUnion.mpr ⟨0, by simp⟩
  | succ n ih =>
      intro c hc
      rw [Function.iterate_succ_apply'] at hc
      rcases e11StepMask_testBit a _ _ hc with hm | ⟨i, v, hv, hvc⟩ | ⟨lam, v, hlam, hv, hvc⟩
      · exact ih c hm
      · have hvS : e11Decode v ∈ e11ReachSet a := ih v hv
        have : e11Decode c = (e11M a i).mulVec (e11Decode v) := by
          rw [← hvc, e11MCode, e11Decode_code]
        rw [this]
        exact e11ReachSet_closed a (Or.inr (Or.inl ⟨i, e11Decode v, hvS, rfl⟩))
      · have hvS : e11Decode v ∈ e11ReachSet a := ih v hv
        have : e11Decode c = lam • e11Decode v := by
          rw [← hvc, e11SmulCode, e11Decode_code]
        rw [this]
        exact e11ReachSet_closed a (Or.inr (Or.inr ⟨lam, e11Decode v, hlam, hvS, rfl⟩))

theorem e11Reach_mem (a : ZMod 5) (ha : a ≠ 0) (S : Set (Fin 4 → ZMod 5))
    (h0 : Pi.single (0 : Fin 4) (1 : ZMod 5) ∈ S)
    (hM : ∀ i v, v ∈ S → (e11M a i).mulVec v ∈ S)
    (hs : ∀ lam : ZMod 5, ∀ v, lam ≠ 0 → v ∈ S → lam • v ∈ S)
    (v : Fin 4 → ZMod 5) (hv : e11Norm a v = 1 ∨ e11Norm a v = 4) : v ∈ S := by
  have hclosed : e11StepSet a S ⊆ S := by
    intro w hw
    simp only [e11StepSet, Set.mem_union, Set.mem_setOf_eq] at hw
    rcases hw with hw | hw | hw
    · exact hw
    · rcases hw with ⟨i, u, hu, rfl⟩
      exact hM i u hu
    · rcases hw with ⟨lam, u, hlam, hu, rfl⟩
      exact hs lam u hlam hu
  have hcheck := e11Check_ne_zero a ha
  rw [e11Check] at hcheck
  have hmem : e11Code v ∈ List.range 625 := List.mem_range.mpr (e11Code_lt v)
  have hbit := (List.all_eq_true.mp hcheck) (e11Code v) hmem
  have hp : (e11Norm a (e11Decode (e11Code v)) == 1 ||
      e11Norm a (e11Decode (e11Code v)) == 4) = true := by
    rw [e11Decode_code]
    rcases hv with hv | hv <;> simp [hv]
  have : (e11Reach a).testBit (e11Code v) = true := by
    simpa [hp] using hbit
  have := e11ReachSet_subset h0 hclosed (e11Reach_testBit a _ this)
  rwa [e11Decode_code] at this

@[expose] def e11Phi {k : ℕ} (b : Fin 4 → Fin (k + 1) → ZMod 5) (c : Fin 4 → ZMod 5) :
    Fin (k + 1) → ZMod 5 :=
  ∑ i, c i • b i

theorem e11Phi_add {k : ℕ} (b : Fin 4 → Fin (k + 1) → ZMod 5) (c d : Fin 4 → ZMod 5) :
    e11Phi b (c + d) = e11Phi b c + e11Phi b d := by
  simp only [e11Phi, Pi.add_apply, add_smul, Finset.sum_add_distrib]

theorem e11Phi_smul {k : ℕ} (b : Fin 4 → Fin (k + 1) → ZMod 5) (r : ZMod 5)
    (c : Fin 4 → ZMod 5) : e11Phi b (r • c) = r • e11Phi b c := by
  simp only [e11Phi, Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]

theorem e11Phi_sub {k : ℕ} (b : Fin 4 → Fin (k + 1) → ZMod 5) (c d : Fin 4 → ZMod 5) :
    e11Phi b (c - d) = e11Phi b c - e11Phi b d := by
  have h : c - d = c + (-1 : ZMod 5) • d := by
    ext x
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [show (-1 : ZMod 5) * d x = -d x from neg_one_mul (d x), sub_eq_add_neg]
  rw [h, e11Phi_add, e11Phi_smul]
  have hneg : (-1 : ZMod 5) • e11Phi b d = -e11Phi b d := by
    ext i
    simp only [Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
    exact neg_one_mul _
  rw [hneg, sub_eq_add_neg]

theorem e11Phi_single {k : ℕ} (b : Fin 4 → Fin (k + 1) → ZMod 5) (i : Fin 4) :
    e11Phi b (Pi.single i 1) = b i := by
  rw [e11Phi]
  simp

theorem e11Phi_eq_zero {k : ℕ} (b : Fin 4 → Fin (k + 1) → ZMod 5) :
    e11Phi b (Pi.single (0 : Fin 4) (1 : ZMod 5)) = b 0 :=
  e11Phi_single b 0

theorem e11G_symm (a : ZMod 5) (i j : Fin 4) : e11G a i j = e11G a j i := by
  fin_cases i <;> fin_cases j <;> rfl

theorem e11G_self (a : ZMod 5) (i : Fin 4) : e11G a i i = 1 := by
  fin_cases i <;> rfl

theorem e11G_mulVec_apply (a : ZMod 5) (c : Fin 4 → ZMod 5) (j : Fin 4) :
    (e11G a).mulVec c j = ∑ i, e11G a j i * c i :=
  rfl

theorem fiveForm_sum_smul_left {ι : Type*} (s : Finset ι) (k : ℕ) (ε : Bool)
    (c : ι → ZMod 5) (b : ι → Fin (k + 1) → ZMod 5) (y : Fin (k + 1) → ZMod 5) :
    fiveForm k ε (∑ i ∈ s, c i • b i) y = ∑ i ∈ s, c i * fiveForm k ε (b i) y := by
  have hfive : ∀ a b : Fin (k + 1) → ZMod 5, fiveForm k ε a b = fiveBilin k ε true a b := by
    intro a b
    rw [fiveBilin_apply]
    simp [fiveSignRep]
  rw [hfive, LinearMap.BilinForm.sum_left]
  exact Finset.sum_congr rfl fun i _ => by
    rw [LinearMap.BilinForm.smul_left, hfive]

theorem fiveForm_sum_smul_right {ι : Type*} (s : Finset ι) (k : ℕ) (ε : Bool)
    (x : Fin (k + 1) → ZMod 5) (c : ι → ZMod 5) (b : ι → Fin (k + 1) → ZMod 5) :
    fiveForm k ε x (∑ i ∈ s, c i • b i) = ∑ i ∈ s, c i * fiveForm k ε x (b i) := by
  have hfive : ∀ a b : Fin (k + 1) → ZMod 5, fiveForm k ε a b = fiveBilin k ε true a b := by
    intro a b
    rw [fiveBilin_apply]
    simp [fiveSignRep]
  rw [hfive, LinearMap.BilinForm.sum_right]
  exact Finset.sum_congr rfl fun i _ => by
    rw [LinearMap.BilinForm.smul_right, hfive]

theorem fiveForm_e11Phi_single {k : ℕ} {ε : Bool} {q a : ZMod 5}
    {b : Fin 4 → Fin (k + 1) → ZMod 5}
    (hgram : ∀ i j, fiveForm k ε (b i) (b j) = q * e11G a i j) (c : Fin 4 → ZMod 5)
    (j : Fin 4) :
    fiveForm k ε (e11Phi b c) (b j) = q * (e11G a).mulVec c j := by
  rw [e11Phi]
  rw [show (∑ i, c i • b i) = ∑ i ∈ Finset.univ, c i • b i from rfl]
  rw [fiveForm_sum_smul_left, e11G_mulVec_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hgram i j, e11G_symm a i j]
  ring

theorem fiveForm_e11Phi {k : ℕ} {ε : Bool} {q a : ZMod 5} {b : Fin 4 → Fin (k + 1) → ZMod 5}
    (hgram : ∀ i j, fiveForm k ε (b i) (b j) = q * e11G a i j) (c d : Fin 4 → ZMod 5) :
    fiveForm k ε (e11Phi b c) (e11Phi b d) = q * (c ⬝ᵥ (e11G a).mulVec d) := by
  rw [e11Phi]
  rw [show (∑ i, c i • b i) = ∑ i ∈ Finset.univ, c i • b i from rfl]
  rw [fiveForm_sum_smul_left]
  have h2 : ∀ i, fiveForm k ε (b i) (e11Phi b d) = ∑ j, d j * (q * e11G a i j) := by
    intro i
    rw [e11Phi]
    rw [show (∑ j, d j • b j) = ∑ j ∈ Finset.univ, d j • b j from rfl]
    rw [fiveForm_sum_smul_right]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hgram i j]
  rw [show (∑ i, c i * fiveForm k ε (b i) (e11Phi b d)) =
      ∑ i, c i * ∑ j, d j * (q * e11G a i j) by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [h2 i]]
  rw [dotProduct]
  simp only [Finset.mul_sum, e11G_mulVec_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem e11M_mulVec (a : ZMod 5) (i : Fin 4) (c : Fin 4 → ZMod 5) :
    (e11M a i).mulVec c = c - (2 * (e11G a).mulVec c i) • Pi.single i 1 := by
  ext l
  fin_cases i <;> fin_cases l <;>
    simp [e11M, Matrix.mulVec, dotProduct, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      Fin.sum_univ_four] <;>
    ring

theorem e11Phi_refl {k : ℕ} {ε : Bool} {q a : ZMod 5} {b : Fin 4 → Fin (k + 1) → ZMod 5}
    (hq : q ≠ 0) (hgram : ∀ i j, fiveForm k ε (b i) (b j) = q * e11G a i j)
    (c : Fin 4 → ZMod 5) (i : Fin 4) :
    e11Phi b ((e11M a i).mulVec c) =
      (fiveReflOf k ε (b i) : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ e11Phi b c := by
  rw [e11M_mulVec, fiveReflOf_mulVec, e11Phi_sub, e11Phi_smul, e11Phi_single]
  have hQ : fiveForm k ε (b i) (b i) = q := by rw [hgram i i, e11G_self, mul_one]
  have hB : fiveForm k ε (e11Phi b c) (b i) = q * (e11G a).mulVec c i :=
    fiveForm_e11Phi_single hgram c i
  rw [hQ, hB]
  congr 1
  rw [show (2 * (q * (e11G a).mulVec c i)) * q⁻¹ = 2 * (e11G a).mulVec c i by
    field_simp]

theorem isSquare_of_isSquare_mul {q s : ZMod 5} (hq : q ≠ 0)
    (h : IsSquare (q * s) ↔ IsSquare q) : IsSquare s := by
  revert q s
  decide

theorem eq_one_or_eq_four_of_isSquare {s : ZMod 5} (hs : s ≠ 0) (h : IsSquare s) :
    s = 1 ∨ s = 4 := by
  revert s
  decide

theorem e11ReflectionGroup_eq {k : ℕ} {ε π : Bool}
    {W : Submodule (ZMod 5) (Fin (k + 1) → ZMod 5)}
    {b : Fin 4 → Fin (k + 1) → ZMod 5} (a : ZMod 5) (ha : a ≠ 0)
    (hbW : ∀ i, b i ∈ W)
    (hspan : Submodule.span (ZMod 5) (Set.range b) = W)
    (hgram : ∀ i j, fiveForm k ε (b i) (b j) = fiveSignRep π * e11G a i j) :
    Subgroup.closure (Set.range fun i => fiveReflOf k ε (b i)) =
      fiveReflectionGroupIn k ε π W := by
  have hq : fiveSignRep π ≠ 0 := fiveSignRep_ne_zero π
  have hqsq : IsSquare (fiveSignRep π) ↔ π = true := isSquare_fiveSignRep_iff π
  have hQi : ∀ i, fiveForm k ε (b i) (b i) = fiveSignRep π := by
    intro i; rw [hgram i i, e11G_self, mul_one]
  apply le_antisymm
  · rw [fiveReflectionGroupIn]
    apply Subgroup.closure_mono
    rintro g ⟨i, rfl⟩
    exact ⟨b i, hbW i, by rw [hQi i]; exact hq,
      by rw [hQi i]; exact hqsq, fun x => fiveReflOf_mulVec k ε (b i) x⟩
  · rw [fiveReflectionGroupIn]
    refine (Subgroup.closure_le
      (Subgroup.closure (Set.range fun i => fiveReflOf k ε (b i)))).mpr ?_
    intro g hg
    rcases hg with ⟨v, hvW, hvQ, hvπ, hvform⟩
    have hgv : g = fiveReflOf k ε v := by
      apply Units.ext
      apply Matrix.ext_of_mulVec_single
      intro i
      rw [hvform (Pi.single i 1), fiveReflOf_mulVec]
    rw [hgv]
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (R := ZMod 5)).mp
      (by rw [hspan]; exact hvW)
    have hcphi : e11Phi b c = v := hc
    have hqv : fiveForm k ε v v = fiveSignRep π * e11Norm a c := by
      rw [← hcphi, fiveForm_e11Phi hgram c c]
      rfl
    have hsquare : IsSquare (e11Norm a c) := by
      apply isSquare_of_isSquare_mul hq
      rw [← hqv, hvπ, hqsq]
    have hne : e11Norm a c ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hqv
      exact hvQ hqv
    have hmem : e11Norm a c = 1 ∨ e11Norm a c = 4 :=
      eq_one_or_eq_four_of_isSquare hne hsquare
    have hSc : fiveReflOf k ε (e11Phi b c) ∈
        Subgroup.closure (Set.range fun i => fiveReflOf k ε (b i)) := by
      refine e11Reach_mem a ha {c : Fin 4 → ZMod 5 | fiveReflOf k ε (e11Phi b c) ∈
        Subgroup.closure (Set.range fun i => fiveReflOf k ε (b i))} ?_ ?_ ?_ c hmem
      · simp only [Set.mem_setOf_eq]
        rw [e11Phi_eq_zero]
        exact Subgroup.subset_closure ⟨0, rfl⟩
      · intro i c' hc'
        simp only [Set.mem_setOf_eq] at hc' ⊢
        have hgen : fiveReflOf k ε (b i) ∈
            Subgroup.closure (Set.range fun i => fiveReflOf k ε (b i)) :=
          Subgroup.subset_closure ⟨i, rfl⟩
        have hpres : ∀ x y, fiveForm k ε
            ((fiveReflOf k ε (b i) : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ x)
            ((fiveReflOf k ε (b i) : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ y) =
            fiveForm k ε x y :=
          fiveForm_mulVec_of_mem (Subgroup.subset_closure (fiveReflOf_mem
            (by rw [hQi i]; exact hq) (by rw [hQi i]; exact hqsq)))
        rw [e11Phi_refl hq hgram c' i, ← conj_fiveReflOf hpres (e11Phi b c')]
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hgen hc') (Subgroup.inv_mem _ hgen)
      · intro lam c' hlam hc'
        simp only [Set.mem_setOf_eq] at hc' ⊢
        rw [e11Phi_smul, fiveReflOf_smul k ε (e11Phi b c') hlam]
        exact hc'
    rw [hcphi] at hSc
    exact hSc

end CFSG.OddTranspositions.PartThree

end
