module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.Data.Rat.Floor

public section

namespace CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.H1SL3

theorem odd_natCard_of_no_involution (H : Type*) [Group H] [Finite H]
    (h : ∀ x : H, x ^ 2 = 1 → x = 1) : Odd (Nat.card H) := by
  classical
  have : Fintype H := Fintype.ofFinite H
  rw [Nat.card_eq_fintype_card]
  by_contra hodd
  rw [Nat.not_odd_iff_even] at hodd
  have h2 : 2 ∣ Fintype.card H := even_iff_two_dvd.mp hodd
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card 2 h2
  have hx2 : x ^ 2 = 1 := by
    rw [← hx]
    exact pow_orderOf_eq_one x
  have hx1 : x = 1 := h x hx2
  rw [hx1, orderOf_one] at hx
  exact absurd hx (by norm_num)

variable {F : Type*} [Field F]

@[expose] def IsDiagSL (g : Matrix.SpecialLinearGroup (Fin 3) F) : Prop :=
  ∀ i j : Fin 3, i ≠ j → (g : Matrix (Fin 3) (Fin 3) F) i j = 0

theorem isDiagSL_mul {g h : Matrix.SpecialLinearGroup (Fin 3) F}
    (hg : IsDiagSL g) (hh : IsDiagSL h) : IsDiagSL (g * h) := by
  intro i j hij
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : k = i
  · subst hk
    rw [hh _ _ hij, mul_zero]
  · rw [hg _ _ (Ne.symm hk), zero_mul]

theorem isDiagSL_one : IsDiagSL (1 : Matrix.SpecialLinearGroup (Fin 3) F) := by
  intro i j hij
  simp [hij]

theorem isDiagSL_inv {g : Matrix.SpecialLinearGroup (Fin 3) F} (hg : IsDiagSL g) :
    IsDiagSL g⁻¹ := by
  intro i j hij
  rw [Matrix.SpecialLinearGroup.coe_inv]
  fin_cases i <;> fin_cases j <;> simp_all [Matrix.adjugate_fin_three, IsDiagSL]

@[expose] def diagSL : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F) where
  carrier := {g | IsDiagSL g}
  mul_mem' := fun {_ _} hg hh => isDiagSL_mul hg hh
  one_mem' := isDiagSL_one
  inv_mem' := fun {_} hg => isDiagSL_inv hg

theorem diagSL_involution [CharP F 2] (x : diagSL (F := F)) (hx : x ^ 2 = 1) : x = 1 := by
  have hd : IsDiagSL (x : Matrix.SpecialLinearGroup (Fin 3) F) := x.2
  have hA : (x : Matrix (Fin 3) (Fin 3) F) * (x : Matrix (Fin 3) (Fin 3) F) = 1 := by
    have h1 : (x : Matrix.SpecialLinearGroup (Fin 3) F) * (x : Matrix.SpecialLinearGroup (Fin 3) F)
        = 1 := by
      have := congrArg Subtype.val hx
      simpa [sq] using this
    have := congrArg Subtype.val h1
    simpa using this
  have hsq : ∀ i : Fin 3, (x : Matrix (Fin 3) (Fin 3) F) i i *
      (x : Matrix (Fin 3) (Fin 3) F) i i = 1 := by
    intro i
    have h := congrArg (fun A : Matrix (Fin 3) (Fin 3) F => A i i) hA
    rw [Matrix.mul_apply, Finset.sum_eq_single i] at h
    · simpa [Matrix.one_apply] using h
    · intro k _ hk
      rw [hd _ _ (Ne.symm hk), zero_mul]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  have hdiag : ∀ i : Fin 3, ((x : Matrix.SpecialLinearGroup (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) i i = 1 := by
    intro i
    have h := hsq i
    have h2' : (2 : F) = 0 := CharTwo.two_eq_zero
    have h2 : ((x : Matrix (Fin 3) (Fin 3) F) i i - 1) ^ 2 = 0 := by
      have e : ((x : Matrix (Fin 3) (Fin 3) F) i i - 1) ^ 2 =
          (x : Matrix (Fin 3) (Fin 3) F) i i * (x : Matrix (Fin 3) (Fin 3) F) i i - 2 *
            (x : Matrix (Fin 3) (Fin 3) F) i i + 1 := by ring
      rw [e, h2', zero_mul, sub_zero, h, one_add_one_eq_two, h2']
    have h3 := (pow_eq_zero_iff two_ne_zero).mp h2
    exact sub_eq_zero.mp h3
  apply Subtype.ext
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  by_cases hij : i = j
  · subst hij
    simp [hdiag]
  · simp [hij, hd i j hij]

theorem odd_natCard_diagSL [Finite F] [CharP F 2] : Odd (Nat.card (diagSL (F := F))) :=
  odd_natCard_of_no_involution _ fun x hx => diagSL_involution x hx

end CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.H1SL3
