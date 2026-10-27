module

public import CFSG.LocalAnalysis.StandardType.GGQTwoS5Defs

public section

namespace CFSG.StandardType

open Module

namespace ggQ2sb

private def bondNo (m : ℕ) (i j : Fin m) : ZMod 3 :=
  (CartanMatrix.B m i j : ZMod 3) * (CartanMatrix.B m j i : ZMod 3)

private lemma bondNo_eq (m : ℕ) (i j : Fin m) (hij : i ≠ j) :
    bondNo m i j =
      if i.val + 1 = j.val then (if j.val = m - 1 then 2 else 1)
      else if j.val + 1 = i.val then (if i.val = m - 1 then 2 else 1) else 0 := by
  have hji : j ≠ i := hij ∘ Eq.symm
  simp only [bondNo, CartanMatrix.B, Matrix.of_apply, Int.cast_ite]
  simp only [if_neg hij, if_neg hji]
  by_cases h1 : i.val + 1 = j.val
  · have h2 : ¬ j.val + 1 = i.val := by omega
    simp only [if_pos h1, if_neg h2]
    by_cases hj : j.val = m - 1
    · simp only [if_pos hj]
      decide
    · simp only [if_neg hj]
      decide
  · by_cases h2 : j.val + 1 = i.val
    · simp only [if_neg h1, if_pos h2]
      by_cases hi : i.val = m - 1
      · simp only [if_pos hi]
        decide
      · simp only [if_neg hi]
        decide
    · simp only [if_neg h1, if_neg h2]
      decide

private lemma bondNo_ne_zero_iff {m : ℕ} {i j : Fin m} (hij : i ≠ j) :
    bondNo m i j ≠ 0 ↔ i.val + 1 = j.val ∨ j.val + 1 = i.val := by
  rw [bondNo_eq m i j hij]
  by_cases h1 : i.val + 1 = j.val
  · simp only [if_pos h1]
    constructor
    · intro _; exact Or.inl h1
    · intro _; split <;> decide
  · by_cases h2 : j.val + 1 = i.val
    · simp only [if_neg h1, if_pos h2]
      constructor
      · intro _; exact Or.inr h2
      · intro _; split <;> decide
    · simp only [if_neg h1, if_neg h2]
      simp [h1, h2]

private lemma bondNo_two_iff {m : ℕ} (hm : 2 ≤ m) {i j : Fin m} (hij : i ≠ j) :
    bondNo m i j = 2 ↔
      (i.val = m - 2 ∧ j.val = m - 1) ∨ (i.val = m - 1 ∧ j.val = m - 2) := by
  have him := i.isLt
  have hjm := j.isLt
  rw [bondNo_eq m i j hij]
  by_cases h1 : i.val + 1 = j.val
  · simp only [if_pos h1]
    have h2 : ¬ j.val + 1 = i.val := by omega
    by_cases hj : j.val = m - 1
    · simp only [if_pos hj]
      have hi : i.val = m - 2 := by omega
      constructor
      · intro _; exact Or.inl ⟨hi, hj⟩
      · intro _; trivial
    · simp only [if_neg hj]
      constructor
      · intro hh; exact absurd hh (by decide : (1 : ZMod 3) ≠ 2)
      · intro hh
        rcases hh with ⟨-, h⟩ | ⟨h, -⟩
        · exact absurd h hj
        · omega
  · by_cases h2 : j.val + 1 = i.val
    · simp only [if_neg h1, if_pos h2]
      by_cases hi : i.val = m - 1
      · simp only [if_pos hi]
        have hj : j.val = m - 2 := by omega
        constructor
        · intro _; exact Or.inr ⟨hi, hj⟩
        · intro _; trivial
      · simp only [if_neg hi]
        constructor
        · intro hh; exact absurd hh (by decide : (1 : ZMod 3) ≠ 2)
        · intro hh
          rcases hh with ⟨h, h'⟩ | ⟨h, h'⟩
          · omega
          · exact absurd h hi
    · simp only [if_neg h1, if_neg h2]
      constructor
      · intro hh; exact absurd hh (by decide : (0 : ZMod 3) ≠ 2)
      · intro hh
        rcases hh with ⟨h, h'⟩ | ⟨h, h'⟩ <;> omega

private lemma bondNo_last {m : ℕ} (hm : 2 ≤ m) :
    bondNo m ⟨m - 2, by omega⟩ ⟨m - 1, by omega⟩ = 2 := by
  have hne : (⟨m - 2, by omega⟩ : Fin m) ≠ ⟨m - 1, by omega⟩ := by
    intro h; have := congrArg Fin.val h; simp at this; omega
  rw [bondNo_eq m _ _ hne]
  rw [if_pos (by simp [Fin.val_mk]; omega)]
  rw [if_pos (by simp)]

private lemma perm_eq_id {m : ℕ} (hm : 3 ≤ m) (P : Fin m ≃ Fin m)
    (hP : ∀ i j, bondNo m (P i) (P j) = bondNo m i j) : ∀ i, P i = i := by
  have hm2 : 2 ≤ m := by omega
  have hadj : ∀ i j : Fin m, i ≠ j →
      ((i.val + 1 = j.val ∨ j.val + 1 = i.val) ↔
        ((P i).val + 1 = (P j).val ∨ (P j).val + 1 = (P i).val)) := by
    intro i j hij
    have hPiPj : P i ≠ P j := fun h => hij (P.injective h)
    rw [← bondNo_ne_zero_iff hij, ← bondNo_ne_zero_iff hPiPj, hP i j]
  let a0 : Fin m := ⟨m - 2, by omega⟩
  let a1 : Fin m := ⟨m - 1, by omega⟩
  have ha0val : a0.val = m - 2 := rfl
  have ha1val : a1.val = m - 1 := rfl
  have hne01 : a0 ≠ a1 := by
    intro h; have := congrArg Fin.val h; simp [ha0val, ha1val] at this; omega
  have hbb2 : bondNo m (P a0) (P a1) = 2 := by
    rw [hP a0 a1]; exact bondNo_last hm2
  have hPa0a1 : P a0 ≠ P a1 := fun h => hne01 (P.injective h)
  have hcases := (bondNo_two_iff hm2 hPa0a1).mp hbb2
  have hP1val : (P a1).val = m - 1 := by
    rcases hcases with ⟨-, h⟩ | ⟨h, h'⟩
    · exact h
    · exfalso
      let c : Fin m := ⟨m - 3, by omega⟩
      have hcval : c.val = m - 3 := rfl
      have hac : a0 ≠ c := by
        intro hh; have := congrArg Fin.val hh; simp [ha0val, hcval] at this; omega
      have hadjac : a0.val + 1 = c.val ∨ c.val + 1 = a0.val := by
        right; rw [ha0val, hcval]; omega
      have hj := (hadj a0 c hac).mp hadjac
      have hPcval : (P c).val = m - 2 := by
        rcases hj with hh | hh
        · have := (P c).isLt; omega
        · omega
      have heq : P c = P a1 := by
        apply Fin.ext
        rw [hPcval, h']
      have := congrArg Fin.val (P.injective heq)
      simp [hcval, ha1val] at this
      omega
  have hP0val : (P a0).val = m - 2 := by
    rcases hcases with ⟨h, -⟩ | ⟨h, h'⟩
    · exact h
    · exfalso
      omega
  have hfix : ∀ k (hk : k < m), P ⟨k, hk⟩ = ⟨k, hk⟩ := by
    intro k hk
    have hmain : ∀ t (k : ℕ) (hk : k < m), m - 1 - k = t → P ⟨k, hk⟩ = ⟨k, hk⟩ := by
      intro t
      induction t using Nat.strong_induction_on with
      | _ t ih =>
        intro k hk heq
        by_cases hk1 : k = m - 1
        · subst hk1
          apply Fin.ext
          have hval : (P ⟨m - 1, hk⟩).val = m - 1 := by
            have heqa : (⟨m - 1, hk⟩ : Fin m) = a1 := Fin.ext rfl
            rw [heqa]; exact hP1val
          exact hval
        · by_cases hk2 : k = m - 2
          · subst hk2
            apply Fin.ext
            have hval : (P ⟨m - 2, hk⟩).val = m - 2 := by
              have heqa : (⟨m - 2, hk⟩ : Fin m) = a0 := Fin.ext rfl
              rw [heqa]; exact hP0val
            exact hval
          · have hlt1 : k + 1 < m := by omega
            have hlt2 : k + 2 < m := by omega
            have hP1' : P ⟨k + 1, hlt1⟩ = ⟨k + 1, hlt1⟩ :=
              ih (m - 1 - (k + 1)) (by omega) (k + 1) hlt1 rfl
            have hP2' : P ⟨k + 2, hlt2⟩ = ⟨k + 2, hlt2⟩ :=
              ih (m - 1 - (k + 2)) (by omega) (k + 2) hlt2 rfl
            have hne : (⟨k, hk⟩ : Fin m) ≠ ⟨k + 1, hlt1⟩ := by
              intro hh; have := congrArg Fin.val hh; simp at this
            have hadj1 := (hadj ⟨k, hk⟩ ⟨k + 1, hlt1⟩ hne).mp (Or.inl (by simp))
            rw [hP1'] at hadj1
            rcases hadj1 with hh | hh
            · have hv : (P ⟨k, hk⟩).val = k := by
                simp only [Fin.val_mk] at hh
                omega
              exact Fin.ext hv
            · exfalso
              have hv : (P ⟨k, hk⟩).val = k + 2 := by
                simp only [Fin.val_mk] at hh
                omega
              have hPk : P ⟨k, hk⟩ = ⟨k + 2, hlt2⟩ := Fin.ext hv
              have heq2 : (⟨k, hk⟩ : Fin m) = ⟨k + 2, hlt2⟩ := by
                apply P.injective
                rw [hPk, hP2']
              have hval := congrArg Fin.val heq2
              simp only [Fin.val_mk] at hval
              omega
    exact hmain (m - 1 - k) k hk rfl
  intro i
  have := hfix i.val i.isLt
  simpa using this

private lemma zmod3_eq_one_or_neg_one {x : ZMod 3} (hx : x ≠ 0) : x = 1 ∨ x = -1 :=
  (by decide : ∀ y : ZMod 3, y ≠ 0 → y = 1 ∨ y = -1) x hx

end ggQ2sb

theorem ggQ2s5_of_BC (D : GGQ2Lin 3) {m : ℕ} (hm : 3 ≤ m) (f : Fin m ≃ {k // k ≠ D.a})
    (hf : (∀ i j, D.cartan (f i) (f j) = CartanMatrix.B m i j) ∨
      (∀ i j, D.cartan (f i) (f j) = CartanMatrix.C m i j))
    {π : {k // k ≠ D.a} ≃ {k // k ≠ D.a}} {μ : {k // k ≠ D.a} → ZMod 3}
    (h : D.ScaledAut D.a π μ) : D.ScalarModW D.a π μ := by
  let π' : Fin m ≃ Fin m := (f.trans π).trans f.symm
  let μ' : Fin m → ZMod 3 := fun i => μ (f i)
  have hπ : ∀ i : Fin m, π (f i) = f (π' i) := by
    intro i; simp [π']
  have hE : ∀ i j : Fin m, μ' i * ((D.cartan (f i) (f j) : ℤ) : ZMod 3)
      = μ' j * ((D.cartan (f (π' i)) (f (π' j)) : ℤ) : ZMod 3) := by
    intro i j
    simpa [μ', hπ i, hπ j] using h.2 (f i) (f j)
  have hb : ∀ i j : Fin m,
      ((D.cartan (f i) (f j) : ℤ) : ZMod 3) * ((D.cartan (f j) (f i) : ℤ) : ZMod 3)
        = ggQ2sb.bondNo m i j := by
    intro i j
    rcases hf with hB | hC
    · rw [hB i j, hB j i]; rfl
    · have hCij : CartanMatrix.C m i j = CartanMatrix.B m j i := by
        rw [← CartanMatrix.B_transpose m, Matrix.transpose_apply]
      have hCji : CartanMatrix.C m j i = CartanMatrix.B m i j := by
        rw [← CartanMatrix.B_transpose m, Matrix.transpose_apply]
      rw [hC i j, hC j i, hCij, hCji]
      unfold ggQ2sb.bondNo
      exact mul_comm _ _
  have hP : ∀ i j : Fin m, ggQ2sb.bondNo m (π' i) (π' j) = ggQ2sb.bondNo m i j := by
    intro i j
    have h1 := hE i j
    have h2 := hE j i
    have hmul : (μ' i * μ' j) *
        (((D.cartan (f i) (f j) : ℤ) : ZMod 3) * ((D.cartan (f j) (f i) : ℤ) : ZMod 3))
        = (μ' i * μ' j) *
          (((D.cartan (f (π' i)) (f (π' j)) : ℤ) : ZMod 3)
            * ((D.cartan (f (π' j)) (f (π' i)) : ℤ) : ZMod 3)) := by
      calc (μ' i * μ' j) *
            (((D.cartan (f i) (f j) : ℤ) : ZMod 3) * ((D.cartan (f j) (f i) : ℤ) : ZMod 3))
          = (μ' i * ((D.cartan (f i) (f j) : ℤ) : ZMod 3))
              * (μ' j * ((D.cartan (f j) (f i) : ℤ) : ZMod 3)) := by ring
        _ = (μ' j * ((D.cartan (f (π' i)) (f (π' j)) : ℤ) : ZMod 3))
              * (μ' i * ((D.cartan (f (π' j)) (f (π' i)) : ℤ) : ZMod 3)) := by rw [h1, h2]
        _ = (μ' i * μ' j) *
              (((D.cartan (f (π' i)) (f (π' j)) : ℤ) : ZMod 3)
                * ((D.cartan (f (π' j)) (f (π' i)) : ℤ) : ZMod 3)) := by ring
    have hcancel : μ' i * μ' j ≠ 0 := mul_ne_zero (h.1 (f i)) (h.1 (f j))
    have hXX := mul_left_cancel₀ hcancel hmul
    rw [hb i j, hb (π' i) (π' j)] at hXX
    exact hXX.symm
  have hid : ∀ i : Fin m, π' i = i := ggQ2sb.perm_eq_id hm π' hP
  have hπfix : ∀ i : {k // k ≠ D.a}, π i = i := by
    intro i
    have h := hid (f.symm i)
    have h2 : f (π' (f.symm i)) = i := by rw [h]; simp
    have h3 : f (π' (f.symm i)) = π i := by simp [π']
    rw [h3] at h2
    exact h2
  let z : Fin m := ⟨0, by omega⟩
  have hz : ∀ i : Fin m, μ' i = μ' z := by
    have hstep : ∀ (k : ℕ) (hk : k + 1 < m),
        μ' ⟨k, by omega⟩ = μ' ⟨k + 1, hk⟩ := by
      intro k hk
      have hk' : k < m := by omega
      have hne : (⟨k, hk'⟩ : Fin m) ≠ ⟨k + 1, hk⟩ := by
        intro hh; have := congrArg Fin.val hh; simp at this
      have hc : ((D.cartan (f ⟨k, hk'⟩) (f ⟨k + 1, hk⟩) : ℤ) : ZMod 3) ≠ 0 := by
        intro hc0
        have hbadj : ggQ2sb.bondNo m ⟨k, hk'⟩ ⟨k + 1, hk⟩ ≠ 0 := by
          rw [ggQ2sb.bondNo_ne_zero_iff hne]
          left; simp
        apply hbadj
        rw [← hb ⟨k, hk'⟩ ⟨k + 1, hk⟩, hc0, zero_mul]
      have h1 := hE ⟨k, hk'⟩ ⟨k + 1, hk⟩
      rw [hid ⟨k, hk'⟩, hid ⟨k + 1, hk⟩] at h1
      exact mul_right_cancel₀ hc h1
    have hall : ∀ (k : ℕ) (hk : k < m), μ' ⟨k, hk⟩ = μ' z := by
      intro k
      induction k with
      | zero =>
        intro hk
        have : (⟨0, hk⟩ : Fin m) = z := Fin.ext rfl
        rw [this]
      | succ k ih =>
        intro hk
        have hk' : k < m := by omega
        rw [← hstep k hk]
        exact ih hk'
    intro i
    have h := hall i.val i.isLt
    simpa using h
  have hμfix : ∀ i : {k // k ≠ D.a}, μ i = μ' z := by
    intro i
    have := hz (f.symm i)
    simpa [μ'] using this
  refine ⟨μ' z, ggQ2sb.zmod3_eq_one_or_neg_one (h.1 (f z)), 1, ?_, ?_⟩
  · exact Subgroup.one_mem _
  · intro i
    rw [hπfix i, hμfix i]
    rfl

end CFSG.StandardType

end

