module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11OrthFrLine

public section

open scoped Matrix Pointwise

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup

@[expose] def s16c11_fr_bit (m : ℕ) : S16C11FrIdx m → ℕ
  | Sum.inl i => i.1
  | Sum.inr (Sum.inl j) => (m - 1) + j.1
  | Sum.inr (Sum.inr k) => 2 * (m - 1) + k.1

@[expose] def s16c11_fr_ofNat (m : ℕ) (n : ℕ) : S16C11FrVec m :=
  fun c => if n.testBit (s16c11_fr_bit m c) then 1 else 0

@[expose] def s16c11_fr_nat (m : ℕ) (v : S16C11FrVec m) : ℕ :=
  ∑ c, (v c).val * 2 ^ (s16c11_fr_bit m c)

@[expose] def s16c11_fr_sort3 (a b c : ℕ) : ℕ × ℕ × ℕ :=
  if a ≤ b then
    if b ≤ c then (a, b, c)
    else if a ≤ c then (a, c, b) else (c, a, b)
  else
    if a ≤ c then (b, a, c)
    else if b ≤ c then (b, c, a) else (c, b, a)

@[expose] def s16c11_fr_decode (m : ℕ) (t : ℕ × ℕ × ℕ) : Finset (S16C11FrVec m) :=
  {s16c11_fr_ofNat m t.1, s16c11_fr_ofNat m t.2.1, s16c11_fr_ofNat m t.2.2}

@[expose] def s16c11_fr_validCode (m : ℕ) (i j : ℕ) : Prop :=
  s16c11_fr_ofNat m i ≠ 0 ∧ s16c11_fr_ofNat m j ≠ 0 ∧
    s16c11_fr_ofNat m i + s16c11_fr_ofNat m j ≠ 0 ∧
    S16C11FrQ m (s16c11_fr_ofNat m i) = 0 ∧ S16C11FrQ m (s16c11_fr_ofNat m j) = 0 ∧
    S16C11FrQ m (s16c11_fr_ofNat m i + s16c11_fr_ofNat m j) = 0

instance s16c11_fr_validCode_decidable (m : ℕ) (i j : ℕ) :
    Decidable (s16c11_fr_validCode m i j) := by
  unfold s16c11_fr_validCode
  infer_instance

instance s16c11_fr_mulAction (m : ℕ) : MulAction ↥(S16C11FrO m) (S16C11FrVec m) where
  smul g v := ((g : Matrix.GeneralLinearGroup (S16C11FrIdx m) (ZMod 2)) :
    Matrix (S16C11FrIdx m) (S16C11FrIdx m) (ZMod 2)) *ᵥ v
  one_smul v := by
    show (((1 : ↥(S16C11FrO m)) : Matrix.GeneralLinearGroup (S16C11FrIdx m) (ZMod 2)) :
      Matrix (S16C11FrIdx m) (S16C11FrIdx m) (ZMod 2)) *ᵥ v = v
    simp
  mul_smul g h v := by
    show (((g * h : ↥(S16C11FrO m)) : Matrix.GeneralLinearGroup (S16C11FrIdx m) (ZMod 2)) :
      Matrix (S16C11FrIdx m) (S16C11FrIdx m) (ZMod 2)) *ᵥ v =
      ((g : Matrix.GeneralLinearGroup (S16C11FrIdx m) (ZMod 2)) :
        Matrix (S16C11FrIdx m) (S16C11FrIdx m) (ZMod 2)) *ᵥ
        (((h : Matrix.GeneralLinearGroup (S16C11FrIdx m) (ZMod 2)) :
          Matrix (S16C11FrIdx m) (S16C11FrIdx m) (ZMod 2)) *ᵥ v)
    rw [Subgroup.coe_mul, Units.val_mul, Matrix.mulVec_mulVec]

theorem s16c11_fr_ofNat_nat {m : ℕ} (hm : m = 3 ∨ m = 4) (v : S16C11FrVec m) :
    s16c11_fr_ofNat m (s16c11_fr_nat m v) = v := by
  rcases hm with rfl | rfl <;> revert v <;> decide +kernel

theorem s16c11_fr_nat_lt {m : ℕ} (hm : m = 3 ∨ m = 4) (v : S16C11FrVec m) :
    s16c11_fr_nat m v < 2 ^ (2 * m) := by
  rcases hm with rfl | rfl <;> revert v <;> decide +kernel

theorem s16c11_fr_nat_ofNat {m : ℕ} (hm : m = 3 ∨ m = 4) :
    ∀ n < 2 ^ (2 * m), s16c11_fr_nat m (s16c11_fr_ofNat m n) = n := by
  rcases hm with rfl | rfl <;> decide +kernel

theorem s16c11_fr_nat_add {m : ℕ} (hm : m = 3 ∨ m = 4) (u v : S16C11FrVec m) :
    s16c11_fr_nat m (u + v) = s16c11_fr_nat m u ^^^ s16c11_fr_nat m v := by
  rcases hm with rfl | rfl <;> revert u v <;> decide +kernel

theorem s16c11_fr_Q_E {m : ℕ} (hm : m = 3 ∨ m = 4) (i : Fin 2) :
    S16C11FrQ m (s16c11FrE m i.1) = 0 := by
  rcases hm with rfl | rfl <;> fin_cases i <;> decide +kernel

theorem s16c11_fr_E_ne_zero {m : ℕ} (hm : m = 3 ∨ m = 4) (i : Fin 2) :
    s16c11FrE m i.1 ≠ 0 := by
  rcases hm with rfl | rfl <;> fin_cases i <;> decide +kernel

theorem s16c11_fr_decode_sort3 (m : ℕ) (a b c : ℕ) :
    s16c11_fr_decode m (s16c11_fr_sort3 a b c) =
      {s16c11_fr_ofNat m a, s16c11_fr_ofNat m b, s16c11_fr_ofNat m c} := by
  unfold s16c11_fr_sort3 s16c11_fr_decode
  by_cases hab : a ≤ b <;> by_cases hbc : b ≤ c <;> by_cases hac : a ≤ c <;>
    (ext x; simp only [hab, hbc, hac, Finset.mem_insert, Finset.mem_singleton]; tauto)

theorem s16c11_fr_Q_E_add {m : ℕ} (hm : m = 3 ∨ m = 4) :
    S16C11FrQ m (s16c11FrE m 0 + s16c11FrE m 1) = 0 := by
  rcases hm with rfl | rfl <;> decide +kernel

theorem s16c11_fr_E_add_ne_zero {m : ℕ} (hm : m = 3 ∨ m = 4) :
    s16c11FrE m 0 + s16c11FrE m 1 ≠ 0 := by
  rcases hm with rfl | rfl <;> decide +kernel

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
