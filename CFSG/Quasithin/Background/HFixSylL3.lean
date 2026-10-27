module

public import CFSG.Quasithin.Background.HFixSylBase
public import CFSG.Quasithin.Background.HL3NineComm

public section

namespace CFSG.Quasithin.H.FixSyl

open CFSG.Quasithin.H.L3Nine CFSG.Quasithin.H.Tri SU3 Matrix

variable {K : Type} [Field K]

omit [Field K] in
theorem trGL_zero_comm [Field K] {j k : Fin 3} (hj : (0 : Fin 3) ≠ j) (hk : (0 : Fin 3) ≠ k)
    (a b : K) : trGL 0 j hj a * trGL 0 k hk b = trGL 0 k hk b * trGL 0 j hj a := by
  apply Units.ext
  simp only [Units.val_mul, coe_trGL, transvection, add_mul, mul_add, one_mul, mul_one,
    single_mul_single_of_ne _ _ _ _ hj.symm, single_mul_single_of_ne _ _ _ _ hk.symm, add_zero]
  abel

theorem trGL_zero_mul_self [CharP K 2] {j : Fin 3} (hj : (0 : Fin 3) ≠ j) (a : K) :
    trGL 0 j hj a * trGL 0 j hj a = 1 := by
  apply Units.ext
  rw [Units.val_mul, coe_trGL, transvection_mul_transvection_same _ _ hj,
    CharTwo.add_self_eq_zero, transvection_zero, Units.val_one]

variable [Finite K] [CharP K 2] {n : ℕ}

@[expose] noncomputable def trSet (hK : Nat.card K = (2 ^ n) ^ 2) : Set (MulAut (HMod n K)) :=
  {x | ∃ a : K, x = rhoT hK (trGL (0 : Fin 3) 1 (by decide) a) ∨
    x = rhoT hK (trGL (0 : Fin 3) 2 (by decide) a)}

theorem trSet_comm (hK : Nat.card K = (2 ^ n) ^ 2) :
    ∀ x ∈ trSet hK, ∀ y ∈ trSet hK, x * y = y * x := by
  rintro x ⟨a, rfl | rfl⟩ y ⟨b, rfl | rfl⟩ <;> rw [← map_mul, ← map_mul, trGL_zero_comm]

theorem trSet_mul_self (hK : Nat.card K = (2 ^ n) ^ 2) : ∀ x ∈ trSet hK, x * x = 1 := by
  rintro x ⟨a, rfl | rfl⟩ <;> rw [← map_mul, trGL_zero_mul_self, map_one]

theorem trSet_le_img (hK : Nat.card K = (2 ^ n) ^ 2) : trSet hK ⊆ (img hK : Set _) := by
  rintro x ⟨a, rfl | rfl⟩ <;> exact rhoT_mem_img hK (det_trGL _ a)

theorem eq_one_or_e00_of_fix (hK : Nat.card K = (2 ^ 1) ^ 2) (X : HMod 1 K)
    (hX : ∀ x ∈ trSet hK, x X = X) : X = 1 ∨ X = e00 hK := by
  have h0 := eq_zero_of_fix le_rfl hK (X := X) (fun a => hX _ ⟨a, Or.inl rfl⟩)
    (fun a => hX _ ⟨a, Or.inr rfl⟩)
  have h00 : mat X 0 0 * mat X 0 0 = mat X 0 0 * 1 := by
    have := herm_apply X 0 0
    rw [bar_apply, pow_one, pow_two] at this
    rw [this, mul_one]
  rcases (mul_eq_mul_left_iff.1 h00).symm with h | h
  · left
    apply mat_injective
    rw [mat_one]
    ext i j
    by_cases hij : i = 0 ∧ j = 0
    · rw [hij.1, hij.2, h]
      rfl
    · rw [h0 i j hij]
      rfl
  · right
    apply mat_injective
    ext i j
    rw [mat_pt, rk1_apply]
    by_cases hij : i = 0 ∧ j = 0
    · rw [hij.1, hij.2, h, Pi.single_eq_same, map_one, mul_one]
    · rw [h0 i j hij]
      by_cases hi : i = 0
      · have hj : j ≠ 0 := fun hj => hij ⟨hi, hj⟩
        rw [Pi.single_eq_of_ne hj, map_zero, mul_zero]
      · rw [Pi.single_eq_of_ne hi, zero_mul]

omit [Finite K] [CharP K 2] in
theorem card_fixV_sylow_le_two_binaryNine {V : Type} [CommGroup V] [Finite V]
    {H S : Subgroup (MulAut V)} (h : BinaryNineTensor H ⊤ ⊥ 1) (hSH : S ≤ H)
    (hS : Nat.card ↥S = 2 ^ (Nat.card ↥H).factorization 2) : Nat.card ↥(fixV S) ≤ 2 := by
  obtain ⟨K, _, _, _, hK, hr⟩ := h
  have hK' : Nat.card K = (2 ^ 1) ^ 2 := by rw [hK]; norm_num
  obtain ⟨e, he⟩ := exists_model hK' hr
  exact card_fixV_le_two_of_gens e hSH hS (he ▸ trSet_le_img hK') (trSet_comm hK')
    (trSet_mul_self hK') (e00 hK') (eq_one_or_e00_of_fix hK')

end CFSG.Quasithin.H.FixSyl
