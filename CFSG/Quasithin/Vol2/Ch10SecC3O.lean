module

public import CFSG.Quasithin.Vol2.Ch10SecC3G

public section

namespace CFSG.Quasithin.Vol2.Ch10.C3.Om

open CFSG.Quasithin CFSG.Assembly.LowTwoRank
open scoped Matrix

variable {K : Type} [Field K]

theorem fin_two_ne (j : Fin 2) : ∃ j' : Fin 2, j' ≠ j ∧ ∀ l : Fin 2, l = j ∨ l = j' := by
  fin_cases j
  · exact ⟨1, by decide, by decide⟩
  · exact ⟨0, by decide, by decide⟩

theorem eq_zero_of_fix_row {N M D : Matrix (Fin 2) (Fin 2) K} (hND : N * D = D * M)
    (hM : M * M = 0) {i j j' : Fin 2} (hj : j' ≠ j) (hall : ∀ l : Fin 2, l = j ∨ l = j')
    (hij : N i j ≠ 0) (hrow : ∀ k, D j' k = 0) : D = 0 := by
  have hl : ∀ k, (N * D) i k = N i j * D j k := by
    intro k
    rw [Matrix.mul_apply, Finset.sum_eq_single j]
    · intro l _ hl
      rcases hall l with h | h
      · exact absurd h hl
      · rw [h, hrow k, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ j) h
  have hrowj : ∀ k, D j k = 0 := by
    rcases hall i with hi | hi
    ·
      subst hi
      have hDM : ∀ k, (D * M) i k = N i i * D i k := fun k => by rw [← hND, hl]
      intro l
      have h1 : (D * M * M) i l = N i i * (N i i * D i l) := by
        rw [Matrix.mul_apply]
        simp_rw [hDM, mul_assoc, ← Finset.mul_sum]
        rw [← Matrix.mul_apply, hDM]
      rw [Matrix.mul_assoc, hM, Matrix.mul_zero, Matrix.zero_apply] at h1
      have h2 : N i i * N i i ≠ 0 := mul_ne_zero hij hij
      rw [← mul_assoc] at h1
      exact (mul_eq_zero.mp h1.symm).resolve_left h2
    ·
      subst hi
      intro k
      have h1 : N i j * D j k = 0 := by
        rw [← hl, hND, Matrix.mul_apply]
        exact Finset.sum_eq_zero fun m _ => by rw [hrow m, zero_mul]
      exact (mul_eq_zero.mp h1).resolve_left hij
  ext r k
  rcases hall r with h | h
  · rw [h]
    exact hrowj k
  · rw [h]
    exact hrow k

theorem eq_zero_of_fix_two {c d D : Matrix (Fin 2) (Fin 2) K} (hcD : c * D = D)
    (hDd : D * dᵀ = D) {i j i' j' : Fin 2} (hij : (c - 1) i j ≠ 0) (hij' : (d - 1) i' j' ≠ 0)
    (hD : ∀ r k, r ≠ j → k ≠ j' → D r k = 0) : D = 0 := by
  have hN : (c - 1) * D = 0 := by rw [Matrix.sub_mul, hcD, Matrix.one_mul, sub_self]
  have hN' : D * (d - 1)ᵀ = 0 := by
    rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.mul_sub, hDd, Matrix.mul_one, sub_self]
  have hrow : ∀ k, k ≠ j' → D j k = 0 := by
    intro k hk
    have h := congrFun (congrFun hN i) k
    rw [Matrix.mul_apply, Finset.sum_eq_single j (fun l _ hl => by rw [hD l k hl hk, mul_zero])
      (fun h => absurd (Finset.mem_univ j) h), Matrix.zero_apply] at h
    exact (mul_eq_zero.mp h).resolve_left hij
  have hcol : ∀ r k, k ≠ j' → D r k = 0 := by
    intro r k hk
    by_cases hr : r = j
    · rw [hr]
      exact hrow k hk
    · exact hD r k hr hk
  have hcol' : ∀ r, D r j' = 0 := by
    intro r
    have h := congrFun (congrFun hN' r) i'
    rw [Matrix.mul_apply, Finset.sum_eq_single j' (fun k _ hk => by rw [hcol r k hk, zero_mul])
      (fun h => absurd (Finset.mem_univ j') h), Matrix.transpose_apply, Matrix.zero_apply] at h
    exact (mul_eq_zero.mp h).resolve_right hij'
  ext r k
  by_cases hk : k = j'
  · rw [hk]
    exact hcol' r
  · exact hcol r k hk

theorem exists_ne_zero_entry {c : SL K} (hc : c ≠ 1) :
    ∃ i j, ((c : Matrix (Fin 2) (Fin 2) K) - 1) i j ≠ 0 := by
  by_contra h
  push Not at h
  apply hc
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_one]
  exact sub_eq_zero.mp (Matrix.ext h)

variable [CharP K 2]

theorem sub_one_mul_self {d : Matrix (Fin 2) (Fin 2) K} (hd : d * d = 1) :
    (d - 1) * (d - 1) = 0 := by
  have h2 : ∀ A : Matrix (Fin 2) (Fin 2) K, A + A = 0 := fun A => CharTwo.add_self_eq_zero A
  rw [sub_mul, mul_sub, mul_sub, hd, mul_one, one_mul, mul_one]
  simp only [sub_eq_add_neg, CharTwo.neg_eq]
  calc 1 + d + (d + 1) = (1 + 1) + (d + d) := by abel
    _ = 0 := by rw [h2, h2, add_zero]

variable [Finite K]

theorem card_fixSet_le {c d : SL K} (hc : c ≠ 1) (hd2 : d * d = 1)
    (S : Set (Matrix (Fin 2) (Fin 2) K))
    (hS : ∀ X ∈ S, (c : Matrix (Fin 2) (Fin 2) K) * X * (d : Matrix (Fin 2) (Fin 2) K)ᵀ = X)
    (hsub : ∀ X ∈ S, ∀ Y ∈ S, X - Y ∈ S) : Nat.card S ≤ Nat.card K ^ 2 := by
  obtain ⟨i, j, hij⟩ := exists_ne_zero_entry hc
  obtain ⟨j', hj', hall⟩ := fin_two_ne j
  set N := (c : Matrix (Fin 2) (Fin 2) K) - 1 with hN
  set M := (d : Matrix (Fin 2) (Fin 2) K)ᵀ - 1 with hMdef
  have hdd : (d : Matrix (Fin 2) (Fin 2) K)ᵀ * (d : Matrix (Fin 2) (Fin 2) K)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, ← Matrix.SpecialLinearGroup.coe_mul, hd2,
      Matrix.SpecialLinearGroup.coe_one, Matrix.transpose_one]
  have hM : M * M = 0 := sub_one_mul_self hdd
  have hNM : ∀ X ∈ S, N * X = X * M := by
    intro X hX
    have h1 : (c : Matrix (Fin 2) (Fin 2) K) * X = X * (d : Matrix (Fin 2) (Fin 2) K)ᵀ := by
      calc (c : Matrix (Fin 2) (Fin 2) K) * X =
            (c : Matrix (Fin 2) (Fin 2) K) * X * ((d : Matrix (Fin 2) (Fin 2) K)ᵀ *
              (d : Matrix (Fin 2) (Fin 2) K)ᵀ) := by rw [hdd, Matrix.mul_one]
        _ = X * (d : Matrix (Fin 2) (Fin 2) K)ᵀ := by rw [← Matrix.mul_assoc, hS X hX]
    rw [hN, hMdef, Matrix.sub_mul, Matrix.mul_sub, h1, Matrix.one_mul, Matrix.mul_one]
  let φ : S → (Fin 2 → K) := fun X => (X : Matrix (Fin 2) (Fin 2) K) j'
  have hφ : Function.Injective φ := by
    intro X Y hXY
    have hD := hsub X X.2 Y Y.2
    have h0 := eq_zero_of_fix_row (hNM _ hD) hM hj' hall hij (fun k => by
      rw [Matrix.sub_apply]
      exact sub_eq_zero.mpr (congrFun hXY k))
    exact Subtype.ext (sub_eq_zero.mp h0)
  have h1 := Nat.card_le_card_of_injective φ hφ
  rwa [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin 2), Fintype.card_fin] at h1

omit [CharP K 2] in
theorem card_fixSet_pair_le {c d : SL K} (hc : c ≠ 1) (hd : d ≠ 1)
    (S : Set (Matrix (Fin 2) (Fin 2) K))
    (hS : ∀ X ∈ S, (c : Matrix (Fin 2) (Fin 2) K) * X = X ∧
      X * (d : Matrix (Fin 2) (Fin 2) K)ᵀ = X)
    (hsub : ∀ X ∈ S, ∀ Y ∈ S, X - Y ∈ S) : Nat.card S ≤ Nat.card K := by
  obtain ⟨i, j, hij⟩ := exists_ne_zero_entry hc
  obtain ⟨i', j', hij'⟩ := exists_ne_zero_entry hd
  obtain ⟨r₀, hr₀, hallr⟩ := fin_two_ne j
  obtain ⟨k₀, hk₀, hallk⟩ := fin_two_ne j'
  let φ : S → K := fun X => (X : Matrix (Fin 2) (Fin 2) K) r₀ k₀
  have hφ : Function.Injective φ := by
    intro X Y hXY
    have hD := hsub X X.2 Y Y.2
    have h0 := eq_zero_of_fix_two (hS _ hD).1 (hS _ hD).2 hij hij' (fun r k hr hk => by
      rcases hallr r with h | h
      · exact absurd h hr
      rcases hallk k with h' | h'
      · exact absurd h' hk
      rw [h, h', Matrix.sub_apply]
      exact sub_eq_zero.mpr hXY)
    exact Subtype.ext (sub_eq_zero.mp h0)
  exact Nat.card_le_card_of_injective φ hφ

end CFSG.Quasithin.Vol2.Ch10.C3.Om
