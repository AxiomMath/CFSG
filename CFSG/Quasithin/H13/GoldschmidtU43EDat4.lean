module

public import CFSG.Quasithin.H13.GoldschmidtU43EDat3
public import CFSG.Quasithin.H13.GoldschmidtU43EDat2

public section

namespace CFSG.Quasithin.H13.U43

@[expose] def Lset : Set Mat3 := {X | ∃ a ∈ Ltab, M16.toMat a = X}

theorem toMat_gen (k : ℕ) : M16.toMat (genL k) = Umat ∨ M16.toMat (genL k) = Vmat ∨
    M16.toMat (genL k) = Amat1 ∨ M16.toMat (genL k) = Bmat3 := by
  match k with
  | 0 => exact Or.inl toMat_gen_zero
  | 1 => exact Or.inr (Or.inl toMat_gen_one)
  | 2 => exact Or.inr (Or.inr (Or.inl toMat_gen_two))
  | k + 3 => exact Or.inr (Or.inr (Or.inr (by
      have : genL (k + 3) = genL 3 := rfl
      rw [this]
      exact toMat_gen_three)))

theorem Lset_subset_of_closed {Γ : Set Mat3} (hmul : ∀ x ∈ Γ, ∀ y ∈ Γ, x * y ∈ Γ)
    (h1 : (1 : Mat3) ∈ Γ) (hU : Umat ∈ Γ) (hV : Vmat ∈ Γ) (hA : Amat1 ∈ Γ) (hB : Bmat3 ∈ Γ) :
    Lset ⊆ Γ := by
  have hgen : ∀ k, M16.toMat (genL k) ∈ Γ := by
    intro k
    rcases toMat_gen k with h | h | h | h <;> rw [h] <;> assumption
  have hb := bfsOk_eq
  unfold bfsOk at hb
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq,
    decide_eq_true_eq] at hb
  obtain ⟨h0, hall⟩ := hb
  have key : ∀ i, i < 360 → M16.toMat (Ltab.getD i M16.one) ∈ Γ := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi
      rcases hall i hi with h | ⟨hlt, hmul'⟩
      · subst h
        rw [h0, M16.toMat_one]
        exact h1
      · rw [← hmul', M16.toMat_mul]
        exact hmul _ (ih _ hlt (hlt.trans hi)) _ (hgen _)
  rintro _ ⟨a, ha, rfl⟩
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ha
  have hi' : i < 360 := by rw [← Ltab_length]; exact hi
  have := key i hi'
  rwa [List.getD_eq_getElem _ _ hi] at this

theorem ncard_Lset : Lset.ncard = 360 := by
  have hnd : (Ltab.map M16.toMat).Nodup :=
    List.Nodup.map_on (fun a ha b hb h => M16.toMat_inj (Ltab_valid a ha) (Ltab_valid b hb) h)
      Ltab_nodup
  have hset : Lset = ↑(Ltab.map M16.toMat).toFinset := by
    ext X
    simp [Lset]
  rw [hset, Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd, List.length_map, Ltab_length]

theorem valid_one : M16.Valid M16.one := by decide

theorem toMat_pow_three (a : M16) :
    M16.toMat (M16.mul a (M16.mul a a)) = M16.toMat a ^ 3 := by
  rw [M16.toMat_mul, M16.toMat_mul, pow_three]

@[expose] def ord3 : List M16 :=
  Ltab.filter fun a => (M16.mul a (M16.mul a a) == M16.one) && !(a == M16.one)

set_option maxRecDepth 100000 in
theorem fixCnt_le_nine : ∀ a ∈ ord3, V4.fixCnt a ≤ 9 := by decide +kernel

set_option maxRecDepth 100000 in
theorem fixCnt2_le_three : ∀ a ∈ ord3, ∀ b ∈ ord3, M16.mul a b = M16.mul b a → b ≠ a →
    b ≠ M16.mul a a → V4.fixCnt2 a b ≤ 3 := by decide +kernel

theorem mem_ord3 {X : Mat3} (hX : X ∈ Lset) (h3 : X ^ 3 = 1) (h1 : X ≠ 1) :
    ∃ a ∈ ord3, M16.toMat a = X := by
  obtain ⟨a, ha, rfl⟩ := hX
  refine ⟨a, List.mem_filter.mpr ⟨ha, ?_⟩, rfl⟩
  have e : M16.mul a (M16.mul a a) = M16.one :=
    M16.toMat_inj (M16.valid_mul _ _) valid_one (by rw [toMat_pow_three, h3, M16.toMat_one])
  have e2 : a ≠ M16.one := fun h => h1 (by rw [h, M16.toMat_one])
  simp [e, e2]

theorem card_fix_Lset_le {X : Mat3} (hX : X ∈ Lset) (h3 : X ^ 3 = 1) (h1 : X ≠ 1) :
    Nat.card {v : Fin 4 → ZMod 3 // X.mulVec v = v} ≤ 9 := by
  obtain ⟨a, ha, rfl⟩ := mem_ord3 hX h3 h1
  exact (V4.card_fix_le a).trans (fixCnt_le_nine a ha)

theorem card_fix2_Lset_le {X Y : Mat3} (hX : X ∈ Lset) (hY : Y ∈ Lset) (hX3 : X ^ 3 = 1)
    (hY3 : Y ^ 3 = 1) (hXY : X * Y = Y * X) (hX1 : X ≠ 1) (hY1 : Y ≠ 1) (hYX : Y ≠ X)
    (hYX2 : Y ≠ X * X) :
    Nat.card {v : Fin 4 → ZMod 3 // X.mulVec v = v ∧ Y.mulVec v = v} ≤ 3 := by
  obtain ⟨a, ha, rfl⟩ := mem_ord3 hX hX3 hX1
  obtain ⟨b, hb, rfl⟩ := mem_ord3 hY hY3 hY1
  have h1 : M16.mul a b = M16.mul b a :=
    M16.toMat_inj (M16.valid_mul _ _) (M16.valid_mul _ _)
      (by rw [M16.toMat_mul, M16.toMat_mul, hXY])
  have h2 : b ≠ a := fun h => hYX (by rw [h])
  have h3 : b ≠ M16.mul a a := fun h => hYX2 (by rw [h, M16.toMat_mul])
  exact (V4.card_fix2_le a b).trans (fixCnt2_le_three a ha b hb h1 h2 h3)

end CFSG.Quasithin.H13.U43
