module

public import CFSG.LocalAnalysis.StandardType.GGHalfE6CertDefs

public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Minuscule

@[expose] def ggHalfApplyBits (A : List ℕ) (v : ℕ) : ℕ :=
  (List.range 27).foldl (fun acc j => acc ^^^ (if v.testBit j then A.getD j 0 else 0)) 0

@[expose] def ggHalfMulBits (A B : List ℕ) : List ℕ := B.map (ggHalfApplyBits A)

@[expose] def ggHalfIdBits : List ℕ := (List.range 27).map fun a => 2 ^ a

@[expose] def ggHalfRootBits (k : ℕ) : List ℕ :=
  (List.range 27).map fun a =>
    2 ^ a ^^^ (if 2 ≤ dig (e6Data.op k) a then 2 ^ (dig (e6Data.op k) a / 2 - 1) else 0)

@[expose] def ggHalfMulRoot (A : List ℕ) (k : ℕ) : List ℕ :=
  (List.range 27).map fun a =>
    if 2 ≤ dig (e6Data.op k) a then A.getD a 0 ^^^ A.getD (dig (e6Data.op k) a / 2 - 1) 0
    else A.getD a 0

@[expose] def ggHalfWordBits (w : List ℕ) : List ℕ := w.foldl ggHalfMulRoot ggHalfIdBits

noncomputable def ggHalfVecBits (v : Fin 27 →₀ GaloisField 2 1) : ℕ :=
  by classical exact ∑ a ∈ v.support, 2 ^ (a : ℕ)

noncomputable def ggHalfVecOfBits (m : ℕ) : Fin 27 →₀ GaloisField 2 1 :=
  Finsupp.equivFunOnFinite.symm fun a => if m.testBit (a : ℕ) then 1 else 0

private noncomputable def ggE6Endo
    (g : GGE6Two) :
    Module.End (GaloisField 2 1) (Fin 27 →₀ GaloisField 2 1) :=
  e6Data_valid.endo (GaloisField 2 1) g

private noncomputable def ggE6RootOp (γ : GGE6Root) :
    Module.End (GaloisField 2 1) (Fin 27 →₀ GaloisField 2 1) :=
  e6Data.rootOp (GaloisField 2 1) γ

private noncomputable def ggE6E (k : ℕ) :
    Module.End (GaloisField 2 1) (Fin 27 →₀ GaloisField 2 1) :=
  toEnd (GaloisField 2 1) 27 (e6Data.op k)

noncomputable def ggE6Bits
    (g : GGE6Two) : List ℕ :=
  (List.finRange 27).map fun a => ggHalfVecBits (ggE6Endo g (Finsupp.single a 1))

private theorem gf2_eq_zero_or_one (x : GaloisField 2 1) : x = 0 ∨ x = 1 := by
  classical
  have hF : Nat.card (GaloisField 2 1) = 2 := by
    simpa using GaloisField.card 2 1 (by norm_num)
  haveI : Fintype (GaloisField 2 1) := Fintype.ofFinite _
  have h2 : Fintype.card (GaloisField 2 1) = 2 := by
    rw [← Nat.card_eq_fintype_card]; exact hF
  have hc : ({(0 : GaloisField 2 1), 1} : Finset (GaloisField 2 1)).card = 2 :=
    Finset.card_pair zero_ne_one
  have hun : ({(0 : GaloisField 2 1), 1} : Finset (GaloisField 2 1)) = Finset.univ := by
    apply Finset.eq_univ_of_card; rw [hc, h2]
  have : x ∈ ({(0 : GaloisField 2 1), 1} : Finset (GaloisField 2 1)) := by
    rw [hun]; exact Finset.mem_univ x
  simpa using this

private theorem charTwo_self (x : GaloisField 2 1) : x + x = 0 := by
  have h2 : (2 : GaloisField 2 1) = 0 := CharTwo.two_eq_zero
  calc x + x = (2 : ℕ) • x := (two_nsmul x).symm
    _ = (2 : GaloisField 2 1) • x := nsmul_eq_mul 2 x
    _ = 0 := by rw [h2, zero_smul]

private noncomputable def bitOf (x : GaloisField 2 1) : Bool :=
  by classical exact if x = 0 then false else true

private theorem bitOf_zero : bitOf 0 = false := by
  classical
  simp [bitOf]

private theorem bitOf_one : bitOf 1 = true := by
  classical
  simp [bitOf]

private theorem bitOf_add (x y : GaloisField 2 1) :
    bitOf (x + y) = (bitOf x ^^ bitOf y) := by
  classical
  rcases gf2_eq_zero_or_one x with rfl | rfl <;> rcases gf2_eq_zero_or_one y with rfl | rfl
  · simp [bitOf]
  · simp [bitOf]
  · simp [bitOf]
  · rw [charTwo_self]; simp [bitOf]

private theorem bitOf_eq_true {x : GaloisField 2 1} : bitOf x = true ↔ x ≠ 0 := by
  classical
  by_cases h : x = 0 <;> simp [bitOf, h]

private theorem ite_bitOf (x : GaloisField 2 1) :
    (if bitOf x then (1 : GaloisField 2 1) else 0) = x := by
  rcases gf2_eq_zero_or_one x with rfl | rfl
  · rw [bitOf_zero]; rfl
  · rw [bitOf_one]; rfl

private theorem sum_range_two_pow (n : ℕ) :
    (∑ i ∈ Finset.range n, 2 ^ i) = 2 ^ n - 1 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih, pow_succ]; omega

private theorem testBit_sum_two_pow (s : Finset ℕ) (j : ℕ) :
    (∑ i ∈ s, 2 ^ i).testBit j = decide (j ∈ s) := by
  classical
  set L := s.sort (· ≤ ·) with hL
  have hsum : ∑ i ∈ s, 2 ^ i = (L.map (fun i => 2 ^ i)).sum := by
    rw [Finset.sum_eq_multiset_sum, ← Finset.sort_eq s (· ≤ ·)]
    rw [hL, Multiset.map_coe, Multiset.sum_coe]
  rw [hsum]
  have hbit : ((L.map (fun i => 2 ^ i)).sum).bitIndices = L :=
    Nat.bitIndices_sum_map_two_pow (Finset.sortedLT_sort s)
  apply Bool.eq_iff_iff.2
  rw [decide_eq_true_iff]
  rw [← Nat.mem_bitIndices, hbit, Finset.mem_sort]

private theorem testBit_ggHalfVecBits (v : Fin 27 →₀ GaloisField 2 1) (a : Fin 27) :
    (ggHalfVecBits v).testBit (a : ℕ) = bitOf (v a) := by
  classical
  have hs : ggHalfVecBits v =
      ∑ i ∈ v.support.image (fun a : Fin 27 => (a : ℕ)), 2 ^ i := by
    unfold ggHalfVecBits
    exact (Finset.sum_image (f := fun i : ℕ => 2 ^ i)
      (g := fun a : Fin 27 => (a : ℕ)) (s := v.support)
      (fun a _ b _ h => Fin.ext h)).symm
  rw [hs, testBit_sum_two_pow]
  apply Bool.eq_iff_iff.2
  rw [decide_eq_true_iff, Finset.mem_image]
  constructor
  · rintro ⟨b, hb, hba⟩
    have hba' : b = a := Fin.ext hba
    subst hba'
    exact bitOf_eq_true.2 (Finsupp.mem_support_iff.1 hb)
  · intro hx
    exact ⟨a, Finsupp.mem_support_iff.2 (bitOf_eq_true.1 hx), rfl⟩

private theorem ggHalfVecBits_zero : ggHalfVecBits (0 : Fin 27 →₀ GaloisField 2 1) = 0 := by
  classical
  unfold ggHalfVecBits
  rw [Finsupp.support_zero, Finset.sum_empty]

theorem ggHalfVecBits_lt (v : Fin 27 →₀ GaloisField 2 1) : ggHalfVecBits v < 2 ^ 27 := by
  classical
  have hle : ggHalfVecBits v ≤ ∑ a : Fin 27, 2 ^ (a : ℕ) := by
    unfold ggHalfVecBits
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun i _ _ => Nat.zero_le _)
  have huniv : (∑ a : Fin 27, 2 ^ (a : ℕ)) = 2 ^ 27 - 1 := by
    rw [Fin.sum_univ_eq_sum_range]; exact sum_range_two_pow 27
  omega

theorem ggHalfVecBits_single (a : Fin 27) :
    ggHalfVecBits (Finsupp.single a 1) = 2 ^ (a : ℕ) := by
  classical
  unfold ggHalfVecBits
  rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.sum_singleton]

private theorem ggHalfVecBits_smul (c : GaloisField 2 1) (w : Fin 27 →₀ GaloisField 2 1) :
    ggHalfVecBits (c • w) = if bitOf c then ggHalfVecBits w else 0 := by
  rcases gf2_eq_zero_or_one c with rfl | rfl
  · rw [zero_smul, ggHalfVecBits_zero, bitOf_zero]; rfl
  · rw [one_smul, bitOf_one]; rfl

theorem ggHalfVecBits_add (v w : Fin 27 →₀ GaloisField 2 1) :
    ggHalfVecBits (v + w) = ggHalfVecBits v ^^^ ggHalfVecBits w := by
  classical
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_xor]
  by_cases hj : j < 27
  · let a : Fin 27 := ⟨j, hj⟩
    have han : j = (a : ℕ) := rfl
    rw [han, testBit_ggHalfVecBits, testBit_ggHalfVecBits, testBit_ggHalfVecBits,
      Finsupp.add_apply, bitOf_add]
  · have hpow : 2 ^ 27 ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h1 : (ggHalfVecBits (v + w)).testBit j = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le (ggHalfVecBits_lt (v + w)) hpow)
    have h2 : (ggHalfVecBits v).testBit j = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le (ggHalfVecBits_lt v) hpow)
    have h3 : (ggHalfVecBits w).testBit j = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le (ggHalfVecBits_lt w) hpow)
    rw [h1, h2, h3]; rfl

private theorem ggHalfVecOfBits_apply (m : ℕ) (a : Fin 27) :
    ggHalfVecOfBits m a = if m.testBit (a : ℕ) then 1 else 0 := by
  unfold ggHalfVecOfBits
  have h := Finsupp.equivFunOnFinite_apply (Finsupp.equivFunOnFinite.symm
    (fun a : Fin 27 => if m.testBit (a : ℕ) then (1 : GaloisField 2 1) else 0)) a
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

theorem ggHalfVecBits_ofBits {m : ℕ} (hm : m < 2 ^ 27) :
    ggHalfVecBits (ggHalfVecOfBits m) = m := by
  classical
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < 27
  · let a : Fin 27 := ⟨j, hj⟩
    have han : j = (a : ℕ) := rfl
    rw [han, testBit_ggHalfVecBits, ggHalfVecOfBits_apply]
    cases hb : m.testBit (a : ℕ) <;> simp [hb, bitOf]
  · have hpow : 2 ^ 27 ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h1 : (ggHalfVecBits (ggHalfVecOfBits m)).testBit j = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le (ggHalfVecBits_lt _) hpow)
    have h2 : m.testBit j = false := Nat.testBit_lt_two_pow (lt_of_lt_of_le hm hpow)
    rw [h1, h2]

theorem ggHalfVecOfBits_bits (v : Fin 27 →₀ GaloisField 2 1) :
    ggHalfVecOfBits (ggHalfVecBits v) = v := by
  classical
  apply Finsupp.ext
  intro a
  rw [ggHalfVecOfBits_apply, testBit_ggHalfVecBits]
  exact ite_bitOf (v a)

theorem ggHalfVecBits_injective : Function.Injective ggHalfVecBits := by
  intro v w h
  have hv := ggHalfVecOfBits_bits v
  have hw := ggHalfVecOfBits_bits w
  rw [← hv, h, hw]

private theorem zero_testBit (j : ℕ) : (0 : ℕ).testBit j = false :=
  Nat.testBit_lt_two_pow (by positivity)

private theorem testBit_foldl_xor (l : List ℕ) (f : ℕ → ℕ) (init j : ℕ) :
    (l.foldl (fun acc i => acc ^^^ f i) init).testBit j =
      (l.map (fun i => (f i).testBit j)).foldl (fun a b => a ^^ b) (init.testBit j) := by
  induction l generalizing init with
  | nil => simp
  | cons a t ih =>
    rw [List.foldl_cons, List.map_cons, List.foldl_cons, ih, Nat.testBit_xor]

private theorem testBit_ggHalfApplyBits (A : List ℕ) (v j : ℕ) :
    (ggHalfApplyBits A v).testBit j =
      ((List.range 27).map (fun i =>
        if v.testBit i then (A.getD i 0).testBit j else false)).foldl
          (fun a b => a ^^ b) false := by
  unfold ggHalfApplyBits
  rw [testBit_foldl_xor, zero_testBit]
  congr 1
  apply List.map_congr_left
  intro i _
  cases hv : v.testBit i <;> simp [hv, zero_testBit]

private theorem ggHalfApplyBits_zero (A : List ℕ) : ggHalfApplyBits A 0 = 0 := by
  simp [ggHalfApplyBits, zero_testBit]

private theorem foldl_range_false (g : ℕ → Bool) (n : ℕ) (h : ∀ i < n, g i = false) :
    (List.range n).foldl (fun acc i => acc ^^ g i) false = false := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [ih (fun i hi => h i (by omega)), h n (by omega)]
    rfl

private theorem foldl_range_ite (b : Bool) (j n : ℕ) (hj : j < n) :
    (List.range n).foldl (fun acc i => acc ^^ (if i = j then b else false)) false = b := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    by_cases hjn : j < n
    · rw [ih hjn, if_neg (by omega)]; simp
    · have hje : j = n := by omega
      subst hje
      rw [foldl_range_false (fun i => if i = j then b else false) j
        (fun i hi => by rw [if_neg (by omega)])]
      simp

private theorem ggHalfApplyBits_two_pow (A : List ℕ) {j : ℕ} (hj : j < 27) :
    ggHalfApplyBits A (2 ^ j) = A.getD j 0 := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [testBit_ggHalfApplyBits]
  have hmap : (List.range 27).map (fun i =>
        if (2 ^ j).testBit i then (A.getD i 0).testBit k else false) =
      (List.range 27).map (fun i => if i = j then (A.getD j 0).testBit k else false) := by
    apply List.map_congr_left
    intro i _
    rw [Nat.testBit_two_pow]
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij, Ne.symm hij]
  rw [hmap, List.foldl_map]
  exact foldl_range_ite ((A.getD j 0).testBit k) j 27 hj

private theorem ggHalfApplyBits_two_pow_ite (A : List ℕ) (b : Bool) (j : ℕ) (hj : j < 27) :
    ggHalfApplyBits A (if b then 2 ^ j else 0) = if b then A.getD j 0 else 0 := by
  cases b <;> simp [ggHalfApplyBits_zero, ggHalfApplyBits_two_pow A hj]

private theorem foldl_xor_eq (l : List Bool) (x : Bool) :
    l.foldl (fun a b => a ^^ b) x = (x ^^ l.foldl (fun a b => a ^^ b) false) := by
  induction l generalizing x with
  | nil => simp
  | cons a t ih =>
    rw [List.foldl_cons, ih (x ^^ a), List.foldl_cons, ih (false ^^ a)]
    simp [Bool.xor_assoc, Bool.xor_left_comm, Bool.xor_comm]

private theorem foldl_map_xor_false (l : List ℕ) (f g : ℕ → Bool) :
    (l.map (fun i => f i ^^ g i)).foldl (fun a b => a ^^ b) false =
      (((l.map f).foldl (fun a b => a ^^ b) false) ^^
        ((l.map g).foldl (fun a b => a ^^ b) false)) := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.map_cons, List.map_cons, List.map_cons, List.foldl_cons, List.foldl_cons,
      List.foldl_cons]
    simp only [Bool.false_xor]
    rw [foldl_xor_eq (List.map (fun i => f i ^^ g i) t) (f a ^^ g a),
      foldl_xor_eq (List.map f t) (f a), foldl_xor_eq (List.map g t) (g a), ih]
    simp [Bool.xor_assoc, Bool.xor_left_comm, Bool.xor_comm]

theorem ggHalfApplyBits_xor (A : List ℕ) (u v : ℕ) :
    ggHalfApplyBits A (u ^^^ v) = ggHalfApplyBits A u ^^^ ggHalfApplyBits A v := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [Nat.testBit_xor, testBit_ggHalfApplyBits, testBit_ggHalfApplyBits, testBit_ggHalfApplyBits]
  have hmap : (List.range 27).map (fun i =>
        if (u ^^^ v).testBit i then (A.getD i 0).testBit k else false) =
      (List.range 27).map (fun i =>
        (if u.testBit i then (A.getD i 0).testBit k else false) ^^
          (if v.testBit i then (A.getD i 0).testBit k else false)) := by
    apply List.map_congr_left
    intro i _
    cases hu : u.testBit i <;> cases hv : v.testBit i <;> simp [Nat.testBit_xor, hu, hv]
  rw [hmap]
  exact foldl_map_xor_false _ _ _

private theorem ggE6Bits_getD
    (g : GGE6Two) (a : Fin 27) :
    (ggE6Bits g).getD (a : ℕ) 0 =
      ggHalfVecBits (ggE6Endo g (Finsupp.single a 1)) := by
  unfold ggE6Bits
  rw [List.getD_eq_getElem _ _ (by rw [List.length_map, List.length_finRange]; exact a.2),
    List.getElem_map, List.getElem_finRange]
  congr 1

theorem ggE6Bits_apply
    (g : GGE6Two)
    (v : Fin 27 →₀ GaloisField 2 1) :
    ggHalfVecBits (e6Data_valid.endo (GaloisField 2 1) g v) =
      ggHalfApplyBits (ggE6Bits g) (ggHalfVecBits v) := by
  change ggHalfVecBits (ggE6Endo g v) = ggHalfApplyBits (ggE6Bits g) (ggHalfVecBits v)
  classical
  refine Finsupp.induction_linear v ?_ ?_ ?_
  · rw [map_zero, ggHalfVecBits_zero, ggHalfApplyBits_zero]
  · intro f h hf hh
    have hr : ggHalfVecBits (f + h) = ggHalfVecBits f ^^^ ggHalfVecBits h :=
      ggHalfVecBits_add f h
    rw [map_add, ggHalfVecBits_add, hr, ggHalfApplyBits_xor, hf, hh]
  · intro a b
    have hsb : Finsupp.single a b = b • Finsupp.single a 1 := by
      rw [Finsupp.smul_single', mul_one]
    rw [hsb]
    simp only [map_smul, ggHalfVecBits_smul, ggHalfVecBits_single]
    rw [ggHalfApplyBits_two_pow_ite (ggE6Bits g) (bitOf b) (a : ℕ) a.2, ggE6Bits_getD]

theorem ggE6Bits_injective
    {g g' : GGE6Two} (h : ggE6Bits g = ggE6Bits g') : g = g' := by
  apply e6Data_valid.endo_injective
  change ggE6Endo g = ggE6Endo g'
  apply ext_single
  intro a
  have hget : (ggE6Bits g).getD (a : ℕ) 0 = (ggE6Bits g').getD (a : ℕ) 0 := by rw [h]
  rw [ggE6Bits_getD, ggE6Bits_getD] at hget
  exact ggHalfVecBits_injective hget

private theorem ggE6Endo_eq
    (g : GGE6Two) :
    ggE6Endo g = e6Data_valid.endo (GaloisField 2 1) g := rfl

theorem ggE6Bits_one :
    ggE6Bits (1 : GGE6Two) = ggHalfIdBits := by
  classical
  unfold ggE6Bits ggHalfIdBits
  have h1 : ggE6Endo (1 : GGE6Two) = 1 := by
    rw [ggE6Endo_eq]
    exact e6Data_valid.endo_one (GaloisField 2 1)
  rw [h1]
  simp only [Module.End.one_apply, ggHalfVecBits_single]
  rfl

theorem ggE6Bits_mul
    (g g' : GGE6Two) :
    ggE6Bits (g * g') = ggHalfMulBits (ggE6Bits g) (ggE6Bits g') := by
  unfold ggE6Bits ggHalfMulBits
  rw [List.map_map]
  apply List.map_congr_left
  intro a _
  rw [Function.comp_apply]
  have hcomp : ggE6Endo (g * g') = ggE6Endo g * ggE6Endo g' := by
    rw [ggE6Endo_eq, ggE6Endo_eq, ggE6Endo_eq]
    exact e6Data_valid.endo_mul (GaloisField 2 1) g g'
  rw [hcomp, Module.End.mul_apply]
  exact ggE6Bits_apply g (ggE6Endo g' (Finsupp.single a 1))

private theorem finRange_map_range_map (f : ℕ → ℕ) :
    (List.finRange 27).map (fun a : Fin 27 => f (a : ℕ)) = (List.range 27).map f := rfl

private theorem ggHalfRootBits_finRange (k : ℕ) :
    ggHalfRootBits k = (List.finRange 27).map (fun a : Fin 27 =>
      2 ^ (a : ℕ) ^^^
        (if 2 ≤ dig (e6Data.op k) a then 2 ^ (dig (e6Data.op k) a / 2 - 1) else 0)) := by
  unfold ggHalfRootBits
  exact (finRange_map_range_map _).symm

private theorem ggHalfMulRoot_finRange (A : List ℕ) (k : ℕ) :
    ggHalfMulRoot A k = (List.finRange 27).map (fun a : Fin 27 =>
      if 2 ≤ dig (e6Data.op k) a then
        A.getD (a : ℕ) 0 ^^^ A.getD (dig (e6Data.op k) a / 2 - 1) 0
      else A.getD (a : ℕ) 0) := by
  unfold ggHalfMulRoot
  exact (finRange_map_range_map _).symm

private theorem ggHalfVecBits_digVec
    (c : ℕ) (hc : 2 ≤ c) (hlt : c / 2 - 1 < 27) :
    ggHalfVecBits (digVec (GaloisField 2 1) 27 c) = 2 ^ (c / 2 - 1) := by
  classical
  rw [digVec_of_le (R := GaloisField 2 1) (d := 27) hc hlt, ggHalfVecBits_smul]
  have hc' : bitOf ((-1 : GaloisField 2 1) ^ c) = true := by
    rw [CharTwo.neg_eq]
    simp [bitOf]
  rw [hc', ggHalfVecBits_single]
  simp

private theorem ggE6E_single
    (k : ℕ) (a : Fin 27) :
    ggE6E k (Finsupp.single a 1) = digVec (GaloisField 2 1) 27 (dig (e6Data.op k) a) :=
  toEnd_single (R := GaloisField 2 1) (d := 27) (M := e6Data.op k) a

private theorem ggE6RootOp_root
    {k : ℕ} (hk : k < 72) :
    ggE6RootOp (e6Certificate.root k) = ggE6E k := by
  have h : e6Data.rootOp (GaloisField 2 1) (e6Certificate.root k) =
      e6Data.E (GaloisField 2 1) k :=
    MinData.rootOp_root (D := e6Data) (R := GaloisField 2 1)
      (by rw [Tag.rootCertificate_length]; exact hk)
  exact h

private theorem ggE6Endo_xm
    (γ : GGE6Root) :
    ggE6Endo (ggE6x γ) = 1 + ggE6RootOp γ := by
  rw [ggE6Endo_eq]
  change e6Data_valid.endo (GaloisField 2 1) (ggE6x γ) = 1 + e6Data.rootOp (GaloisField 2 1) γ
  rw [show ggE6x γ = e6Data_valid.xm (GaloisField 2 1) γ 1 from rfl, e6Data_valid.endo_xm,
    one_smul]

private theorem ggHalfMulBits_root
    (A : List ℕ) {k : ℕ}
    (hk : k < 72) :
    ggHalfMulBits A (ggHalfRootBits k) = ggHalfMulRoot A k := by
  classical
  rw [ggHalfRootBits_finRange, ggHalfMulRoot_finRange]
  unfold ggHalfMulBits
  rw [List.map_map]
  apply List.map_congr_left
  intro a _
  rw [Function.comp_apply, ggHalfApplyBits_xor, ggHalfApplyBits_two_pow (A := A) a.2]
  have hwf := e6Data_valid.wf_op k a a.2
  by_cases hc : 2 ≤ dig (e6Data.op k) a
  · have hlt : dig (e6Data.op k) a / 2 - 1 < 27 := by
      rcases hwf with h0 | ⟨h2, hlt⟩
      · omega
      · exact hlt
    rw [if_pos hc, ggHalfApplyBits_two_pow (A := A) hlt, if_pos hc]
  · rw [if_neg hc, ggHalfApplyBits_zero, if_neg hc]; simp

theorem ggE6Bits_x
    {k : ℕ} (hk : k < 72) :
    ggE6Bits (ggE6x (e6Certificate.root k)) = ggHalfRootBits k := by
  classical
  rw [ggHalfRootBits_finRange]
  unfold ggE6Bits
  apply List.map_congr_left
  intro a _
  rw [ggE6Endo_xm, LinearMap.add_apply, Module.End.one_apply, ggE6RootOp_root hk,
    ggE6E_single, ggHalfVecBits_add, ggHalfVecBits_single]
  by_cases hc : 2 ≤ dig (e6Data.op k) a
  · have hlt : dig (e6Data.op k) a / 2 - 1 < 27 := by
      rcases e6Data_valid.wf_op k a a.2 with h0 | ⟨h2, hlt⟩
      · omega
      · exact hlt
    rw [ggHalfVecBits_digVec _ hc hlt, if_pos hc]
  · rw [digVec_of_lt_two (R := GaloisField 2 1) (d := 27) (by omega),
      ggHalfVecBits_zero, if_neg hc]

theorem ggE6Bits_mulRoot
    (g : GGE6Two) {k : ℕ}
    (hk : k < 72) :
    ggE6Bits (g * ggE6x (e6Certificate.root k)) =
      ggHalfMulRoot (ggE6Bits g) k := by
  rw [ggE6Bits_mul, ggE6Bits_x hk, ggHalfMulBits_root _ hk]

noncomputable def ggHalfWord
    (w : List ℕ) : GGE6Two :=
  (w.map fun k => ggE6x (e6Certificate.root k)).prod

theorem ggHalfWord_append
    (w w' : List ℕ) :
    ggHalfWord (w ++ w') = ggHalfWord w * ggHalfWord w' := by
  unfold ggHalfWord
  rw [List.map_append, List.prod_append]

private theorem ggE6Bits_mul_word
    (g : GGE6Two) {w : List ℕ}
    (hw : ∀ k ∈ w, k < 72) :
    ggE6Bits (g * ggHalfWord w) = w.foldl ggHalfMulRoot (ggE6Bits g) := by
  induction w generalizing g with
  | nil => simp [ggHalfWord]
  | cons k t ih =>
    have hk : k < 72 := hw k (List.mem_cons_self ..)
    have ht : ∀ j ∈ t, j < 72 := fun j hj => hw j (List.mem_cons_of_mem _ hj)
    have hstep : g * ggHalfWord (k :: t) =
        (g * ggE6x (e6Certificate.root k)) * ggHalfWord t := by
      unfold ggHalfWord
      rw [List.map_cons, List.prod_cons]
      group
    rw [hstep, ih (g * ggE6x (e6Certificate.root k)) ht, List.foldl_cons,
      ggE6Bits_mulRoot g hk]

theorem ggE6Bits_word
    {w : List ℕ}
    (hw : ∀ k ∈ w, k < 72) :
    ggE6Bits (ggHalfWord w) = ggHalfWordBits w := by
  have h := ggE6Bits_mul_word (1 : GGE6Two) hw
  rw [one_mul] at h
  rw [h, ggE6Bits_one]
  rfl

end CFSG.StandardType

end
