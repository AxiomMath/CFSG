module

public import CFSG.Permutation.FinPack
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Data.Fintype.BigOperators

public section

namespace CFSG.Permutation.FinPack

open Equiv Finset

@[expose] noncomputable def allLtK (f : ℕ → Bool) (m : ℕ) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun j r => Bool.rec (motive := fun _ => Bool) false r (f j)) m

theorem allLtK_iff {f : ℕ → Bool} {m : ℕ} : allLtK f m = true ↔ ∀ j < m, f j = true := by
  induction m with
  | zero => exact ⟨fun _ j hj => absurd hj (Nat.not_lt_zero j), fun _ => rfl⟩
  | succ m ih =>
    change Bool.rec (motive := fun _ => Bool) false (allLtK f m) (f m) = true ↔ _
    constructor
    · intro hc j hj
      cases hfm : f m <;> rw [hfm] at hc
      · exact absurd hc Bool.false_ne_true
      · rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        · exact ih.1 hc j hj
        · exact hfm
    · intro H
      rw [H m (Nat.lt_succ_self m)]
      exact ih.2 fun j hj => H j (Nat.lt_succ_of_lt hj)

@[expose] noncomputable def walkK (n : ℕ) (Q : ℕ → Bool) (r : ℕ) : ℕ → ℕ → ℕ → Bool :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ → Bool) (fun _ _ c => Q c)
    (fun _ w d u c => allLtK (fun j => Bool.rec (motive := fun _ => Bool)
      (w (Nat.succ d) (Nat.lor u (Nat.shiftLeft 1 j)) (Nat.add c (Nat.shiftLeft j (Nat.mul 4 d))))
      true (Nat.blt 0 (Nat.land u (Nat.shiftLeft 1 j)))) n) r

theorem walkK_succ (n : ℕ) (Q : ℕ → Bool) (r d u c : ℕ) : walkK n Q (r + 1) d u c =
    allLtK (fun j => Bool.rec (motive := fun _ => Bool)
      (walkK n Q r (Nat.succ d) (Nat.lor u (Nat.shiftLeft 1 j))
        (Nat.add c (Nat.shiftLeft j (Nat.mul 4 d))))
      true (Nat.blt 0 (Nat.land u (Nat.shiftLeft 1 j)))) n := rfl

variable {n : ℕ}

@[expose] noncomputable def valF (σ : Perm (Fin n)) (i : ℕ) : ℕ :=
  if h : i < n then (σ ⟨i, h⟩ : ℕ) else 0

@[expose] noncomputable def maskF (σ : Perm (Fin n)) (d : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0 (fun i m => Nat.lor m (Nat.shiftLeft 1 (valF σ i))) d

theorem valF_lt (σ : Perm (Fin n)) {i : ℕ} (hi : i < n) : valF σ i < n := by
  rw [valF, dif_pos hi]
  exact Fin.isLt _

theorem valF_inj (σ : Perm (Fin n)) {i j : ℕ} (hi : i < n) (hj : j < n)
    (h : valF σ i = valF σ j) : i = j := by
  rw [valF, valF, dif_pos hi, dif_pos hj] at h
  have e := σ.injective (Fin.ext h)
  exact congrArg Fin.val e

theorem testBit_maskF (σ : Perm (Fin n)) (d k : ℕ) :
    (maskF σ d).testBit k = true ↔ ∃ i < d, valF σ i = k := by
  induction d with
  | zero =>
    change (0 : ℕ).testBit k = true ↔ _
    rw [Nat.zero_testBit]
    exact ⟨fun h => absurd h Bool.false_ne_true, fun ⟨i, hi, _⟩ => absurd hi (Nat.not_lt_zero i)⟩
  | succ d ih =>
    change (maskF σ d ||| 1 <<< valF σ d).testBit k = true ↔ _
    rw [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow, Bool.or_eq_true, ih,
      decide_eq_true_iff]
    constructor
    · rintro (⟨i, hi, h⟩ | h)
      · exact ⟨i, by omega, h⟩
      · exact ⟨d, by omega, h⟩
    · rintro ⟨i, hi, h⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · exact Or.inl ⟨i, hi, h⟩
      · exact Or.inr h

theorem land_maskF (σ : Perm (Fin n)) {d : ℕ} (hd : d < n) :
    Nat.land (maskF σ d) (Nat.shiftLeft 1 (valF σ d)) = 0 := by
  change maskF σ d &&& 1 <<< valF σ d = 0
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_and, Nat.one_shiftLeft, Nat.testBit_two_pow, Nat.zero_testBit]
  by_cases hj : valF σ d = j
  · subst hj
    have hb : (maskF σ d).testBit (valF σ d) = false := by
      rw [← Bool.not_eq_true, testBit_maskF]
      rintro ⟨i, hi, h⟩
      have := valF_inj σ (by omega) hd h
      omega
    rw [hb, Bool.false_and]
  · rw [decide_eq_false hj, Bool.and_false]

theorem walkK_sound_aux (Q : ℕ → Bool) (σ : Perm (Fin n)) : ∀ r d, d + r = n →
    walkK n Q r d (maskF σ d) (encF (valF σ) d) = true → Q (enc σ) = true := by
  intro r
  induction r with
  | zero =>
    intro d hd hw
    subst hd
    exact hw
  | succ r ih =>
    intro d hd hw
    rw [walkK_succ] at hw
    have hdn : d < n := by omega
    have h2 : Bool.rec (motive := fun _ => Bool)
        (walkK n Q r (d + 1) (maskF σ (d + 1)) (encF (valF σ) (d + 1))) true
        (Nat.blt 0 (Nat.land (maskF σ d) (Nat.shiftLeft 1 (valF σ d)))) = true :=
      allLtK_iff.1 hw _ (valF_lt σ hdn)
    rw [land_maskF σ hdn] at h2
    exact ih (d + 1) (by omega) h2

theorem walkK_sound {Q : ℕ → Bool} (h : walkK n Q n 0 0 0 = true) (σ : Perm (Fin n)) :
    Q (enc σ) = true :=
  walkK_sound_aux Q σ n 0 (by omega) h

@[expose] noncomputable def rowK (c a m : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0
    (fun b acc => Nat.add acc (Bool.rec (motive := fun _ => ℕ) 0 1 (Nat.ble (rd c a) (rd c b)))) m

@[expose] noncomputable def invK (n c : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0 (fun a acc => Nat.add acc (rowK c a a)) n

@[expose] noncomputable def evenK (n c : ℕ) : Bool := Nat.beq (invK n c % 2) 0

theorem bitK_eq (x y : ℕ) :
    (Bool.rec (motive := fun _ => ℕ) 0 1 (Nat.ble x y) : ℕ) = if x ≤ y then 1 else 0 := by
  cases h : Nat.ble x y
  · have hn : ¬ x ≤ y := by
      rw [← Nat.ble_eq, h]
      exact Bool.false_ne_true
    exact (if_neg hn).symm
  · exact (if_pos (Nat.le_of_ble_eq_true h)).symm

theorem rowK_eq (c a m : ℕ) : rowK c a m = ∑ b ∈ range m, if rd c a ≤ rd c b then 1 else 0 := by
  induction m with
  | zero => rw [Finset.sum_range_zero]; rfl
  | succ m ih =>
    rw [Finset.sum_range_succ, ← ih, ← bitK_eq]
    rfl

theorem invK_eq (n c : ℕ) :
    invK n c = ∑ a ∈ range n, ∑ b ∈ range a, if rd c a ≤ rd c b then 1 else 0 := by
  induction n with
  | zero => rw [Finset.sum_range_zero]; rfl
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih, ← rowK_eq]
    rfl

theorem sign_eq_signAuxK (σ : Perm (Fin n)) : Perm.sign σ = Perm.signAux σ := by
  induction σ using Equiv.Perm.swap_induction_on with
  | one => rw [map_one, Perm.signAux_one]
  | swap_mul f x y hxy ih =>
    rw [Perm.sign_mul, Perm.signAux_mul, ih, Perm.sign_swap hxy, Perm.signAux_swap hxy]

theorem signAux_eq_powK (σ : Perm (Fin n)) : Perm.signAux σ =
    (-1) ^ (Finset.filter (fun x : (Σ _ : Fin n, Fin n) => σ x.1 ≤ σ x.2) (Perm.finPairsLT n)).card := by
  rw [Perm.signAux, ← Finset.prod_filter, Finset.prod_const]

theorem card_invK (hn : n ≤ 16) (σ : Perm (Fin n)) :
    (Finset.filter (fun x : (Σ _ : Fin n, Fin n) => σ x.1 ≤ σ x.2) (Perm.finPairsLT n)).card =
      invK n (enc σ) := by
  rw [invK_eq, Finset.card_eq_sum_ones, Finset.sum_filter, Perm.finPairsLT, Finset.sum_sigma,
    ← Fin.sum_univ_eq_sum_range (fun a => ∑ b ∈ range a,
      if rd (enc σ) a ≤ rd (enc σ) b then 1 else 0) n]
  refine Finset.sum_congr rfl fun a _ => ?_
  dsimp only
  refine Finset.sum_bij (fun b _ => (b : ℕ)) ?_ ?_ ?_ ?_
  · intro b hb
    rw [Finset.mem_attachFin] at hb
    exact hb
  · intro b _ b' _ h
    exact Fin.ext h
  · intro m hm
    refine ⟨⟨m, (Finset.mem_range.1 hm).trans a.2⟩, ?_, rfl⟩
    rw [Finset.mem_attachFin]
    exact hm
  · intro b _
    simp only [rd_enc hn σ, Fin.le_iff_val_le_val]

theorem sign_eq_one_iff_evenK (hn : n ≤ 16) (σ : Perm (Fin n)) :
    Perm.sign σ = 1 ↔ evenK n (enc σ) = true := by
  have hne : (-1 : ℤˣ) ≠ 1 := by decide
  rw [sign_eq_signAuxK, signAux_eq_powK, card_invK hn, neg_one_pow_eq_one_iff_even hne,
    Nat.even_iff, evenK, Nat.beq_eq]

theorem beq_enc_iff (hn : n ≤ 16) {σ τ : Perm (Fin n)} :
    Nat.beq (enc σ) (enc τ) = true ↔ σ = τ := by
  rw [Nat.beq_eq]
  exact ⟨enc_inj hn, congrArg enc⟩

theorem beq_enc_false (hn : n ≤ 16) {σ τ : Perm (Fin n)} (h : σ ≠ τ) :
    Nat.beq (enc σ) (enc τ) = false :=
  Bool.eq_false_iff.2 fun e => h ((beq_enc_iff hn).1 e)

theorem comm_enc_iff (hn : n ≤ 16) {σ τ : Perm (Fin n)} :
    Nat.beq (mulK n (enc σ) (enc τ)) (mulK n (enc τ) (enc σ)) = true ↔ σ * τ = τ * σ := by
  rw [← enc_mul hn, ← enc_mul hn, beq_enc_iff hn]

end CFSG.Permutation.FinPack
