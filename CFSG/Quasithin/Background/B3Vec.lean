module

public import CFSG.Quasithin.Background.B3Tab
public import CFSG.Quasithin.Background.B3Defs
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Tactic.ENatToNat
public import Std.Tactic.BVDecide.Normalize.BitVec

public section

namespace CFSG.Quasithin.B3

@[expose] def vecOfNat (n m : ℕ) : U n := ⟨fun i => if m.testBit i.val then 1 else 0⟩

@[expose] def actM (n : ℕ) (t : Tab) (m : ℕ) : ℕ :=
  (List.range n).foldl (fun acc i => if m.testBit i then acc ||| 2 ^ (t.getD i 0) else acc) 0

theorem testBit_foldl_aux (t : Tab) (m j : ℕ) (l : List ℕ) (acc : ℕ) :
    (l.foldl (fun acc i => if m.testBit i then acc ||| 2 ^ (t.getD i 0) else acc) acc).testBit j
      = (acc.testBit j || l.any (fun i => m.testBit i && decide (t.getD i 0 = j))) := by
  induction l generalizing acc with
  | nil => simp
  | cons a l ih =>
    rw [List.foldl_cons, ih, List.any_cons]
    by_cases h : m.testBit a = true
    · simp [h, Nat.testBit_or, Nat.testBit_two_pow, Bool.or_assoc]
    · simp [h]

variable {n : ℕ}

theorem testBit_actM (σ : Gp n) (m : ℕ) (j : ℕ) (hj : j < n) :
    (actM n (tab σ) m).testBit j = m.testBit (σ.symm ⟨j, hj⟩) := by
  unfold actM
  rw [testBit_foldl_aux, Nat.zero_testBit, Bool.false_or, Bool.eq_iff_iff]
  simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨i, hi, hbit, hgd⟩
    have h1 := getD_tab σ ⟨i, hi⟩
    rw [hgd] at h1
    have h2 : σ ⟨i, hi⟩ = ⟨j, hj⟩ := Fin.ext h1.symm
    have h3 : (⟨i, hi⟩ : Fin n) = σ.symm ⟨j, hj⟩ := by rw [← h2]; simp
    rw [← h3]
    exact hbit
  · intro h
    refine ⟨(σ.symm ⟨j, hj⟩ : ℕ), (σ.symm ⟨j, hj⟩).isLt, h, ?_⟩
    rw [getD_tab]
    simp

theorem vecOfNat_actM (σ : Gp n) (m : ℕ) :
    vecOfNat n (actM n (tab σ) m) = permAct n σ (vecOfNat n m) := by
  ext i
  rw [permAct_val]
  simp only [vecOfNat]
  rw [testBit_actM σ m i.val i.isLt]

theorem vecOfNat_xor (a b : ℕ) : vecOfNat n (a ^^^ b) = vecOfNat n a * vecOfNat n b := by
  ext i
  simp only [vecOfNat, U.val_mul, Nat.testBit_xor]
  cases a.testBit i <;> cases b.testBit i <;> decide

@[expose] def popPar (n m : ℕ) : Bool :=
  ((List.range n).map (fun i => if m.testBit i then 1 else 0)).sum % 2 == 0

theorem list_sum_range (f : ℕ → ℕ) (n : ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

theorem vecOfNat_mem_U0 (m : ℕ) : vecOfNat n m ∈ U0 n ↔ popPar n m = true := by
  have h1 : vecOfNat n m ∈ U0 n ↔ ∑ i, (vecOfNat n m).val i = 0 := by
    show wt n (vecOfNat n m) = 1 ↔ _
    have h2 : wt n (vecOfNat n m) = Multiplicative.ofAdd (∑ i, (vecOfNat n m).val i) := rfl
    rw [h2]
    exact ofAdd_eq_one
  rw [h1, popPar, beq_iff_eq, list_sum_range, ← Fin.sum_univ_eq_sum_range
    (fun i => if m.testBit i then 1 else 0) n]
  have h3 : ∑ i : Fin n, (vecOfNat n m).val i
      = ((∑ i : Fin n, if m.testBit i.val then 1 else 0 : ℕ) : ZMod 2) := by
    rw [Nat.cast_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [vecOfNat]
    split_ifs <;> simp
  rw [h3, ZMod.natCast_eq_zero_iff, Nat.dvd_iff_mod_eq_zero]

@[expose] def inWk (n : ℕ) : Mod → ℕ → Bool
  | .u, _ => true
  | .u0, m => popPar n m
  | .ut, _ => true
  | .ut0, m => popPar n m

@[expose] def inNk (n : ℕ) : Mod → ℕ → Bool
  | .u, x => x % 2 ^ n == 0
  | .u0, x => x % 2 ^ n == 0
  | .ut, x => x % 2 ^ n == 0 || x % 2 ^ n == 2 ^ n - 1
  | .ut0, x => x % 2 ^ n == 0 || x % 2 ^ n == 2 ^ n - 1

theorem vecOfNat_mem_W (k : Mod) (m : ℕ) : vecOfNat n m ∈ k.W n ↔ inWk n k m = true := by
  cases k
  · simp [Mod.W, inWk]
  · exact vecOfNat_mem_U0 m
  · simp [Mod.W, inWk]
  · exact vecOfNat_mem_U0 m

theorem vecOfNat_eq_one_iff (x : ℕ) : vecOfNat n x = 1 ↔ x % 2 ^ n = 0 := by
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_mod_two_pow, Nat.zero_testBit]
    by_cases hi : i < n
    · have := congrArg (fun w : U n => w.val ⟨i, hi⟩) h
      simp only [vecOfNat, U.val_one] at this
      rw [decide_eq_true hi, Bool.true_and]
      by_contra hc
      have hc' : x.testBit i = true := by simpa using hc
      simp [hc'] at this
    · simp [hi]
  · intro h
    ext i
    have h1 := Nat.testBit_mod_two_pow x n i
    rw [h, Nat.zero_testBit, decide_eq_true i.isLt, Bool.true_and] at h1
    simp [vecOfNat, ← h1]

theorem vecOfNat_eq_eVec_iff (x : ℕ) : vecOfNat n x = eVec n ↔ x % 2 ^ n = 2 ^ n - 1 := by
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_mod_two_pow, Nat.testBit_two_pow_sub_one]
    by_cases hi : i < n
    · have := congrArg (fun w : U n => w.val ⟨i, hi⟩) h
      simp only [vecOfNat, eVec] at this
      rw [decide_eq_true hi, Bool.true_and]
      by_contra hc
      have hc' : x.testBit i = false := by simpa using hc
      simp [hc'] at this
    · simp [hi]
  · intro h
    ext i
    have h1 := Nat.testBit_mod_two_pow x n i
    rw [h, Nat.testBit_two_pow_sub_one, decide_eq_true i.isLt, Bool.true_and] at h1
    simp [vecOfNat, eVec, ← h1]

theorem eVec_mul_self : eVec n * eVec n = 1 := by
  ext i
  simp only [eVec, U.val_mul, U.val_one]
  decide

theorem mem_Esub_iff (w : U n) : w ∈ Esub n ↔ w = 1 ∨ w = eVec n := by
  constructor
  · intro h
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 h
    have h2 : eVec n ^ (2 : ℤ) = 1 := by rw [zpow_two, eVec_mul_self]
    have h3 : eVec n ^ k = eVec n ^ (k % 2) := by
      conv_lhs => rw [← Int.mul_ediv_add_emod k 2, zpow_add, zpow_mul, h2, one_zpow, one_mul]
    rw [h3]
    rcases Int.emod_two_eq_zero_or_one k with h4 | h4
    · left; rw [h4]; simp
    · right; rw [h4]; simp
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _

theorem vecOfNat_mem_N (k : Mod) (x : ℕ) : vecOfNat n x ∈ k.N n ↔ inNk n k x = true := by
  cases k
  · simp [Mod.N, inNk, Subgroup.mem_bot, vecOfNat_eq_one_iff]
  · simp [Mod.N, inNk, Subgroup.mem_bot, vecOfNat_eq_one_iff]
  · simp [Mod.N, inNk, mem_Esub_iff, vecOfNat_eq_one_iff, vecOfNat_eq_eVec_iff]
  · simp [Mod.N, inNk, mem_Esub_iff, vecOfNat_eq_one_iff, vecOfNat_eq_eVec_iff]

theorem card_U (n : ℕ) : Fintype.card (U n) = 2 ^ n := by
  have e : U n ≃ (Fin n → ZMod 2) := ⟨fun w => w.val, fun f => ⟨f⟩, fun _ => rfl, fun _ => rfl⟩
  rw [Fintype.card_congr e]
  simp [ZMod.card]

theorem vecOfNat_injective {a b : ℕ} (ha : a < 2 ^ n) (hb : b < 2 ^ n)
    (h : vecOfNat n a = vecOfNat n b) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < n
  · have := congrArg (fun w : U n => w.val ⟨i, hi⟩) h
    simp only [vecOfNat] at this
    cases ha' : a.testBit i <;> cases hb' : b.testBit i <;> simp_all
  · have hi' : n ≤ i := by omega
    have h1 : a.testBit i = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by norm_num) hi'))
    have h2 : b.testBit i = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hb (Nat.pow_le_pow_right (by norm_num) hi'))
    rw [h1, h2]

@[expose] noncomputable def vecEquiv (n : ℕ) : Fin (2 ^ n) ≃ U n :=
  Equiv.ofBijective (fun m => vecOfNat n m.val)
    ((Fintype.bijective_iff_injective_and_card _).2
      ⟨fun a b h => Fin.ext (vecOfNat_injective a.isLt b.isLt h), by simp [card_U]⟩)

theorem vecEquiv_apply (m : Fin (2 ^ n)) : vecEquiv n m = vecOfNat n m.val := rfl

theorem length_filter_range (q : ℕ → Bool) (n : ℕ) :
    ((List.range n).filter q).length = ∑ i ∈ Finset.range n, if q i = true then 1 else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.filter_append, List.length_append, ih, Finset.sum_range_succ]
    by_cases h : q n = true <;> simp [h]

theorem card_subtype_range (N : ℕ) (q : ℕ → Bool) :
    Nat.card {m : Fin N // q m.val = true} = ((List.range N).filter q).length := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter,
    length_filter_range]
  exact Fin.sum_univ_eq_sum_range (fun i => if q i = true then 1 else 0) N

theorem vecOfNat_inv (m : ℕ) : (vecOfNat n m)⁻¹ = vecOfNat n m := by
  ext i
  simp only [U.val_inv, vecOfNat]
  split_ifs <;> decide

@[expose] def cntF (n : ℕ) (k : Mod) (A : List Tab) : ℕ :=
  ((List.range (2 ^ n)).filter
    (fun m => inWk n k m && A.all (fun t => inNk n k (actM n t m ^^^ m)))).length

theorem card_fix_cnt (k : Mod) (K : Subgroup (Gp n)) (A : List Tab)
    (hAv : ∀ t ∈ A, isTab n t = true) (hA : ∀ x : Gp n, x ∈ K ↔ tab x ∈ A) :
    Nat.card (fixV (K.map (Mod.act n k))) * Nat.card ↥(k.N n ⊓ k.W n) = cntF n k A := by
  have h1 := card_fixV_sec (permAct n) (k.isInv_W n) (k.isInv_N n) K
  have h0 : Mod.act n k = secAct (permAct n) (k.isInv_W n) (k.isInv_N n) := rfl
  rw [h0, h1]
  have h2 : Nat.card {m : Fin (2 ^ n) //
        (inWk n k m.val && A.all (fun t => inNk n k (actM n t m.val ^^^ m.val))) = true} =
      Nat.card {w : U n // w ∈ k.W n ∧ ∀ b ∈ K, permAct n b w * w⁻¹ ∈ k.N n} := by
    refine Nat.card_congr ((vecEquiv n).subtypeEquiv fun m => ?_)
    rw [vecEquiv_apply, Bool.and_eq_true, vecOfNat_mem_W]
    refine and_congr Iff.rfl ?_
    rw [List.all_eq_true]
    constructor
    · intro h b hb
      have hbA : tab b ∈ A := (hA b).1 hb
      have := h _ hbA
      rw [← vecOfNat_mem_N, vecOfNat_xor] at this
      rw [vecOfNat_inv, ← vecOfNat_actM]
      exact this
    · intro h t ht
      obtain ⟨b, rfl⟩ := exists_tab_eq (hAv t ht)
      have := h b ((hA b).2 ht)
      rw [vecOfNat_inv] at this
      rw [← vecOfNat_mem_N, vecOfNat_xor, vecOfNat_actM]
      exact this
  rw [← h2]
  exact card_subtype_range (2 ^ n)
    (fun m => inWk n k m && A.all (fun t => inNk n k (actM n t m ^^^ m)))

end CFSG.Quasithin.B3
