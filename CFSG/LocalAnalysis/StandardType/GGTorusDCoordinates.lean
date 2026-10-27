module

public import CFSG.LocalAnalysis.StandardType.GGTorusScalar
public import CFSG.LocalAnalysis.ComponentInitial.LinearMonomial
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentySpCoord

@[expose] public noncomputable section

namespace CFSG.StandardType.DScalarTorus

open CFSG.LocalAnalysis.ComponentInitial
open TauCeti.DynkinType

variable {m N : ℕ} {μ : Type} [CommGroup μ]

def rootCoordinates (hN : 4 ≤ N) : (Fin N → μ) →* (Fin N → μ) :=
  monomialHom (Matrix.of (typeDSimpleRoot N hN))

@[simp] theorem rootCoordinates_apply (hN : 4 ≤ N) (a : Fin N → μ) (i : Fin N) :
    rootCoordinates hN a i = ∏ j, a j ^ typeDSimpleRoot N hN i j := rfl

theorem exists_simpleRoot_inverse_mod (hN : 4 ≤ N) (hm : Odd m) :
    ∃ B : Matrix (Fin N) (Fin N) ℤ,
      (Int.castRingHom (ZMod m)).mapMatrix (Matrix.of (typeDSimpleRoot N hN) * B) = 1 ∧
        (Int.castRingHom (ZMod m)).mapMatrix (B * Matrix.of (typeDSimpleRoot N hN)) = 1 := by
  refine exists_int_matrix_inverse_mod_of_isUnit_det _ ?_
  rw [det_typeDSimpleRoot_eq_two]
  have h := (ZMod.isUnit_iff_coprime 2 m).mpr (Nat.coprime_two_left.mpr hm)
  simpa using h

private theorem rootCoordinates_inverse (hN : 4 ≤ N)
    (l : μ ≃* Multiplicative (ZMod m)) (B : Matrix (Fin N) (Fin N) ℤ)
    (hB : (Int.castRingHom (ZMod m)).mapMatrix
      (Matrix.of (typeDSimpleRoot N hN) * B) = 1) (a : Fin N → μ) :
    rootCoordinates hN (monomialHom B a) = a := by
  have hBt : (Int.castRingHom (ZMod m)).mapMatrix
      (B.transpose * (Matrix.of (typeDSimpleRoot N hN)).transpose) = 1 := by
    rw [← Matrix.transpose_mul, RingHom.mapMatrix_apply, Matrix.transpose_map,
      ← RingHom.mapMatrix_apply, hB, Matrix.transpose_one]
  have h := corTuple_prod_mul_eq_mod l (Matrix.of (typeDSimpleRoot N hN)).transpose B.transpose hBt a
  funext i
  simpa only [rootCoordinates, monomialHom_apply, Finset.prod_apply, corTuple_apply,
    Matrix.transpose_apply, Matrix.of_apply] using congrFun h i

theorem exists_rootCoordinateEquiv (hN : 4 ≤ N) (hm : Odd m)
    (l : μ ≃* Multiplicative (ZMod m)) :
    ∃ e : (Fin N → μ) ≃* (Fin N → μ), ∀ a, e a = rootCoordinates hN a := by
  obtain ⟨B, hAB, hBA⟩ := exists_simpleRoot_inverse_mod hN hm
  have hright : Function.RightInverse (monomialHom (G := μ) B) (rootCoordinates hN) :=
    rootCoordinates_inverse hN l B hAB
  have hleft : Function.LeftInverse (monomialHom (G := μ) B) (rootCoordinates hN) := by
    intro a
    have hBt : (Int.castRingHom (ZMod m)).mapMatrix
        ((Matrix.of (typeDSimpleRoot N hN)).transpose * B.transpose) = 1 := by
      rw [← Matrix.transpose_mul, RingHom.mapMatrix_apply, Matrix.transpose_map,
        ← RingHom.mapMatrix_apply, hBA, Matrix.transpose_one]
    have h := corTuple_prod_mul_eq_mod l B.transpose
      (Matrix.of (typeDSimpleRoot N hN)).transpose hBt a
    funext i
    simpa only [rootCoordinates, monomialHom_apply, Finset.prod_apply, corTuple_apply,
      Matrix.transpose_apply, Matrix.of_apply] using congrFun h i
  exact ⟨MulEquiv.ofBijective (rootCoordinates hN) ⟨hleft.injective, hright.surjective⟩,
    fun a => rfl⟩

noncomputable def rootCoordinateEquiv (hN : 4 ≤ N) (hm : Odd m)
    (l : μ ≃* Multiplicative (ZMod m)) : (Fin N → μ) ≃* (Fin N → μ) :=
  (exists_rootCoordinateEquiv hN hm l).choose

@[simp] theorem rootCoordinateEquiv_apply (hN : 4 ≤ N) (hm : Odd m)
    (l : μ ≃* Multiplicative (ZMod m)) (a : Fin N → μ) :
    rootCoordinateEquiv hN hm l a = rootCoordinates hN a :=
  (exists_rootCoordinateEquiv hN hm l).choose_spec a

theorem rootCoordinates_of_add_one_lt (hN : 4 ≤ N) (a : Fin N → μ) {i : Fin N}
    (hi : i.val + 1 < N) :
    rootCoordinates hN a i = a i * (a ⟨i.val + 1, hi⟩)⁻¹ := by
  rw [rootCoordinates_apply, typeDSimpleRoot_of_add_one_lt hN hi]
  simp only [Pi.sub_apply, zpow_sub, Finset.prod_mul_distrib]
  have hprod : ∀ t : Fin N, (∏ j, a j ^ ((Pi.single t (1 : ℤ) : Fin N → ℤ) j)) = a t := by
    intro t
    rw [Finset.prod_eq_single t]
    · simp
    · intro b _ hb
      simp [Pi.single_apply, hb, Ne.symm hb]
    · simp
  rw [hprod, Finset.prod_inv_distrib, hprod]

theorem rootCoordinates_of_not_add_one_lt (hN : 4 ≤ N) (a : Fin N → μ) {i : Fin N}
    (hi : ¬ i.val + 1 < N) :
    rootCoordinates hN a i = a ⟨N - 2, by omega⟩ * a ⟨N - 1, by omega⟩ := by
  rw [rootCoordinates_apply, typeDSimpleRoot_of_not_add_one_lt hN hi]
  simp only [Pi.add_apply, zpow_add, Finset.prod_mul_distrib]
  have hprod : ∀ t : Fin N, (∏ j, a j ^ ((Pi.single t (1 : ℤ) : Fin N → ℤ) j)) = a t := by
    intro t
    rw [Finset.prod_eq_single t]
    · simp
    · intro b _ hb
      simp [Pi.single_apply, hb, Ne.symm hb]
    · simp
  rw [hprod, hprod]

def simpleReflection (hN : 4 ≤ N) (i : Fin N) :
    MulAut (Fin N → Multiplicative (ZMod m)) :=
  if hi : i.val + 1 < N then
    SpCoord.permAut (Equiv.swap i ⟨i.val + 1, hi⟩)
  else
    SpCoord.sgnAut ⟨N - 2, by omega⟩ * SpCoord.sgnAut ⟨N - 1, by omega⟩ *
      SpCoord.permAut (Equiv.swap ⟨N - 2, by omega⟩ ⟨N - 1, by omega⟩)

theorem simpleReflection_eq_mul_corTuple (hN : 4 ≤ N) (i : Fin N)
    (a : Fin N → Multiplicative (ZMod m)) :
    simpleReflection hN i a =
      a * (corTuple (Matrix.of (typeDSimpleRoot N hN)) i (rootCoordinates hN a i))⁻¹ := by
  funext k
  by_cases hi : i.val + 1 < N
  · rw [simpleReflection, dif_pos hi, SpCoord.permAut_apply,
      rootCoordinates_of_add_one_lt hN a hi]
    simp only [Function.comp_apply, Equiv.swap_inv, Pi.mul_apply, Pi.inv_apply,
      corTuple_apply, Matrix.of_apply, typeDSimpleRoot_of_add_one_lt hN hi,
      Pi.sub_apply, Pi.single_apply]
    by_cases hki : k = i
    · subst k
      have hnext : (⟨i.val + 1, hi⟩ : Fin N) ≠ i := Fin.ne_of_val_ne (by simp)
      simp only [Equiv.swap_apply_left, if_true, if_neg hnext.symm]
      simp only [sub_zero, zpow_one]
      simp [mul_comm, mul_left_comm, mul_assoc]
    · by_cases hkn : k = (⟨i.val + 1, hi⟩ : Fin N)
      · subst k
        have hnext : i ≠ (⟨i.val + 1, hi⟩ : Fin N) := Fin.ne_of_val_ne (by simp)
        simp only [Equiv.swap_apply_right, if_neg hnext, if_true, zero_sub, zpow_neg_one]
        simp [hnext, Ne.symm hnext, mul_comm, mul_left_comm, mul_assoc]
      · simp [Equiv.swap_apply_of_ne_of_ne hki hkn, hki, hkn, Ne.symm hki, Ne.symm hkn]
  · rw [simpleReflection, dif_neg hi, rootCoordinates_of_not_add_one_lt hN a hi]
    simp only [MulAut.mul_apply, SpCoord.sgnAut_apply, SpCoord.permAut_apply,
      Function.comp_apply, Equiv.swap_inv, Function.update_apply, Pi.mul_apply, Pi.inv_apply,
      corTuple_apply, Matrix.of_apply, typeDSimpleRoot_of_not_add_one_lt hN hi,
      Pi.add_apply, Pi.single_apply]
    have hlast : (⟨N - 2, by omega⟩ : Fin N) ≠ ⟨N - 1, by omega⟩ :=
      Fin.ne_of_val_ne (by simp; omega)
    by_cases hk2 : k = (⟨N - 2, by omega⟩ : Fin N)
    · subst k
      simp only [if_true, if_neg hlast, if_neg hlast.symm, Equiv.swap_apply_left,
        add_zero, zpow_one]
      simp [mul_comm, mul_left_comm, mul_assoc]
    · by_cases hk1 : k = (⟨N - 1, by omega⟩ : Fin N)
      · subst k
        simp only [if_true, if_neg hlast, if_neg hlast.symm, Equiv.swap_apply_right,
          zero_add, zpow_one]
        simp [mul_comm, mul_left_comm, mul_assoc]
      · simp [hk2, hk1, Ne.symm hk2, Ne.symm hk1,
          Equiv.swap_apply_of_ne_of_ne hk2 hk1]

theorem rootCoordinates_corTuple (hN : 4 ≤ N) (j : Fin N) (z : μ) :
    rootCoordinates hN (corTuple (Matrix.of (typeDSimpleRoot N hN)) j z) =
      corTuple (CartanMatrix.D N).transpose j z := by
  funext i
  rw [rootCoordinates_apply]
  simp only [corTuple_apply, Matrix.transpose_apply, Matrix.of_apply, ← zpow_mul]
  rw [Finset.prod_zpow_eq_zpow_sum]
  have hsum : ∑ k, typeDSimpleRoot N hN j k * typeDSimpleRoot N hN i k =
      CartanMatrix.D N j i := typeDSimpleRoot_dotProduct_typeDSimpleRoot hN j i
  rw [hsum, (CartanMatrix.D_isSymm N).apply i j]

end CFSG.StandardType.DScalarTorus
