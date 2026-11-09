module

public import Certificates.Data.Kernel.MonsterB.FischerK

public section

namespace CFSG.KC.FischerK

open CFSG.KLie.CT

@[expose] noncomputable def vecMulCT (T : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun t _ ih v => Nat.xor (fget t (Nat.succ (Nat.land v 63)) 78) (ih (Nat.shiftRight v 6))) T

@[expose] noncomputable def chTabOK (T : List Nat) : List Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Bool) (fun A => Nat.beq A.length 0)
    (fun t _ ih A => andB (allN 64 fun k => Nat.beq (fget t (Nat.succ k) 78) (vecMulL (A.take 6) k))
      (ih (A.drop 6))) T

theorem vecMulL_consC (r : Nat) (a : List Nat) (v : Nat) :
    vecMulL (r :: a) v =
      Bool.rec (motive := fun _ => Nat) 0 r (Nat.beq (v &&& 1) 1) ^^^ vecMulL a (v >>> 1) :=
  rfl

theorem vecMulL_appendC (a b : List Nat) (v : Nat) :
    vecMulL (a ++ b) v = vecMulL a v ^^^ vecMulL b (v >>> a.length) := by
  induction a generalizing v with
  | nil =>
    change vecMulL b v = 0 ^^^ vecMulL b (v >>> 0)
    rw [Nat.zero_xor, Nat.shiftRight_zero]
  | cons r a ih =>
    rw [List.cons_append, vecMulL_consC, vecMulL_consC, ih, Nat.xor_assoc, List.length_cons,
      Nat.add_comm, Nat.shiftRight_add]

theorem vecMulL_modC (a : List Nat) (v n : Nat) (h : a.length ≤ n) :
    vecMulL a v = vecMulL a (v % 2 ^ n) := by
  induction a generalizing v n with
  | nil => rfl
  | cons r a ih =>
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp at h; omega⟩
    have h1 : v % 2 ^ (m + 1) &&& 1 = v &&& 1 := by
      rw [Nat.and_one_is_mod, Nat.and_one_is_mod,
        Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (Nat.succ_le_succ (Nat.zero_le m)))]
    have h2 : (v % 2 ^ (m + 1)) >>> 1 = (v >>> 1) % 2 ^ m := by
      rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, Nat.pow_one, Nat.pow_succ',
        Nat.mod_mul_right_div_self]
    rw [vecMulL_consC, vecMulL_consC, h1, h2, ← ih (v >>> 1) m (by simp at h; omega)]

theorem andB_trueC {a b : Bool} (h : andB a b = true) : a = true ∧ b = true := by
  cases a
  · exact absurd h Bool.false_ne_true
  · exact ⟨rfl, h⟩

theorem allN_trueC {f : Nat → Bool} {n : Nat} (h : allN n f = true) : ∀ i < n, f i = true := by
  induction n with
  | zero => intro i hi; omega
  | succ n ih =>
    intro i hi
    obtain ⟨h1, h2⟩ := andB_trueC h
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · exact ih h2 i hi
    · exact h1

theorem vecMulCT_eq : ∀ (T A : List Nat), chTabOK T A = true → ∀ v, vecMulCT T v = vecMulL A v
  | [], A, h, v => by
    rw [List.eq_nil_of_length_eq_zero (Nat.eq_of_beq_eq_true h)]
    rfl
  | t :: T, A, h, v => by
    obtain ⟨h1, h2⟩ := andB_trueC h
    have hk := allN_trueC h1
    have ih := vecMulCT_eq T (A.drop 6) h2
    have hv : v &&& 63 = v % 2 ^ 6 := Nat.and_two_pow_sub_one_eq_mod v 6
    change fget t (Nat.succ (v &&& 63)) 78 ^^^ vecMulCT T (v >>> 6) = vecMulL A v
    rw [ih, Nat.eq_of_beq_eq_true (hk _ (by rw [hv]; exact Nat.mod_lt _ (by decide))), hv,
      ← vecMulL_modC _ _ _ (List.length_take_le 6 A)]
    conv => rhs; rw [← List.take_append_drop 6 A]
    rw [vecMulL_appendC]
    by_cases hl : (A.take 6).length = 6
    · rw [hl]
    · have hd : A.drop 6 = [] := List.drop_eq_nil_of_le (by rw [List.length_take] at hl; omega)
      rw [hd]
      rfl

theorem vecMulL_zeroC (a : List Nat) : vecMulL a 0 = 0 := by
  induction a with
  | nil => rfl
  | cons r a ih =>
    rw [vecMulL_consC, Nat.zero_shiftRight, ih, Nat.zero_and, Nat.xor_zero]
    rfl

@[expose] def pow11C : List Nat := (List.range 11).map (2 ^ ·)

theorem vecMulL_unitC (hP : (List.range 2048).all (fun m => vecMulL pow11C m == m) = true)
    (a : Array Nat) (h : ∀ q < 11, a[q]! = 2 ^ q) (m : Nat) (hm : m < 2048) :
    vecMulL a.toList m = m := by
  have hs : 11 ≤ a.size := by
    rcases Nat.lt_or_ge 10 a.size with hl | hl
    · omega
    · have h10 := h 10 (by omega)
      rw [getElem!_neg a 10 (by omega)] at h10
      exact absurd h10 (by decide)
  have ht : a.toList.take 11 = pow11C := by
    apply List.ext_getElem
    · simp [pow11C, List.length_take]
      omega
    · intro q h1 h2
      have hq : q < 11 := by simpa [pow11C] using h2
      rw [List.getElem_take, Array.getElem_toList, ← getElem!_pos a q (by omega), h q hq]
      simp [pow11C]
  have hm' : m >>> (a.toList.take 11).length = 0 := by
    rw [Nat.shiftRight_eq_div_pow, ht]
    exact Nat.div_eq_of_lt (by simpa [pow11C] using hm)
  rw [← List.take_append_drop 11 a.toList, vecMulL_appendC, hm', vecMulL_zeroC, Nat.xor_zero, ht]
  exact Nat.eq_of_beq_eq_true (List.all_eq_true.1 hP m (List.mem_range.2 hm))

end CFSG.KC.FischerK

end
