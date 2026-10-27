module

public import CFSG.LocalAnalysis.StandardType.GGHalfBlockTorus

public section

namespace CFSG.StandardType.GGHalf

open CFSG.LieType.Universal.SpecialLinear Matrix

abbrev F4 : Type := GaloisField 2 2

private noncomputable instance f4Fintype : Fintype F4 := Fintype.ofFinite F4

private theorem f4_natCard : Nat.card F4 = 4 := by
  rw [GaloisField.card 2 2 (by norm_num)]; norm_num

private theorem f4_fintypeCard : Fintype.card F4 = 4 := by
  rw [← Nat.card_eq_fintype_card]; exact f4_natCard

private theorem f4_pow_four (a : F4) : a ^ 4 = a := by
  have h := FiniteField.pow_card (K := F4) a
  rwa [f4_fintypeCard] at h

private theorem f4_exists_ne_zero_one : ∃ a : F4, a ≠ 0 ∧ a ≠ 1 := by
  classical
  by_contra h
  push Not at h
  have hle : (Finset.univ : Finset F4).card ≤ ({0, 1} : Finset F4).card := by
    apply Finset.card_le_card
    intro x _
    by_cases hx : x = 0
    · simp [hx]
    · have hx1 : x = 1 := h x hx
      simp [hx1]
  rw [Finset.card_univ, f4_fintypeCard] at hle
  simp at hle

private theorem sq_eq_add_one {a : F4} (h : a ^ 2 + a + 1 = 0) : a ^ 2 = a + 1 := by
  have h' : a ^ 2 + (a + 1) = 0 := by simpa only [add_assoc] using h
  calc a ^ 2 = a ^ 2 + 0 := (add_zero _).symm
    _ = a ^ 2 + ((a + 1) + (a + 1)) := by rw [CharTwo.add_self_eq_zero]
    _ = (a ^ 2 + (a + 1)) + (a + 1) := by rw [← add_assoc]
    _ = 0 + (a + 1) := by rw [h']
    _ = a + 1 := zero_add _

private theorem eq_of_add_eq_zero {a b : F4} (h : a + b = 0) : a = b := by
  rw [add_eq_zero_iff_eq_neg] at h
  rwa [CharTwo.neg_eq] at h

private theorem add_one_mul_sq_add_self_add_one (a : F4) :
    (a + 1) * (a ^ 2 + a + 1) = a ^ 3 + 1 := by
  ring_nf
  simp [CharTwo.two_eq_zero]

private theorem mul_add_one_mul_sq_add_self_add_one (a : F4) :
    a * (a + 1) * (a ^ 2 + a + 1) = a ^ 4 + a := by
  calc a * (a + 1) * (a ^ 2 + a + 1) = a * ((a + 1) * (a ^ 2 + a + 1)) := by ring
    _ = a * (a ^ 3 + 1) := by rw [add_one_mul_sq_add_self_add_one]
    _ = a ^ 4 + a := by ring

private theorem quad_eq_zero_of_ne_zero_one {a : F4} (h0 : a ≠ 0) (h1 : a ≠ 1) :
    a ^ 2 + a + 1 = 0 := by
  have hzero : a ^ 4 + a = 0 := by rw [f4_pow_four, CharTwo.add_self_eq_zero]
  have hfac : a ^ 4 + a = a * (a + 1) * (a ^ 2 + a + 1) :=
    (mul_add_one_mul_sq_add_self_add_one a).symm
  rw [hfac] at hzero
  rcases mul_eq_zero.mp hzero with h | h
  · rcases mul_eq_zero.mp h with h | h
    · exact absurd h h0
    · exact absurd (eq_of_add_eq_zero h) h1
  · exact h

theorem exists_f4_frame :
    ∃ (ω : F4) (ε : F4 →+* Matrix (Fin 2) (Fin 2) F2),
      ω ^ 2 + ω + 1 = 0 ∧ ε ω = !![0, 1; 1, 1] := by
  classical
  obtain ⟨ω, hω0, hω1⟩ := f4_exists_ne_zero_one
  have hω : ω ^ 2 + ω + 1 = 0 := quad_eq_zero_of_ne_zero_one hω0 hω1
  have hli : LinearIndependent (ZMod 2) ![1, ω] := by
    rw [linearIndependent_fin2]
    refine ⟨?_, ?_⟩
    · simpa using hω0
    · intro a
      have h01 : a = 0 ∨ a = 1 := by
        have hlt : a.val < 2 := ZMod.val_lt a
        have hcases : a.val = 0 ∨ a.val = 1 := by omega
        rcases hcases with h | h
        · left; rw [← ZMod.natCast_zmod_val a, h]; norm_num
        · right; rw [← ZMod.natCast_zmod_val a, h]; norm_num
      rcases h01 with rfl | rfl
      · simp
      · simpa using hω1
  have hcard : Fintype.card (Fin 2) = Module.finrank (ZMod 2) F4 := by
    rw [Fintype.card_fin, GaloisField.finrank (p := 2) (n := 2) (by norm_num)]
  let b : Module.Basis (Fin 2) (ZMod 2) F4 := basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hb : ⇑b = ![1, ω] := coe_basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hb0 : b 0 = 1 := by have h := congrFun hb 0; simpa using h
  have hb1 : b 1 = ω := by have h := congrFun hb 1; simpa using h
  have hsq : ω ^ 2 = ω + 1 := sq_eq_add_one hω
  have hrepr0 : b.repr ω = Finsupp.single 1 1 := by rw [← hb1, Module.Basis.repr_self]
  have hrepr1 : b.repr (ω * ω) = Finsupp.single 0 1 + Finsupp.single 1 1 := by
    have hs : ω * ω = b 0 + b 1 := by rw [hb0, hb1, ← pow_two, hsq]; ring
    rw [hs, map_add, Module.Basis.repr_self, Module.Basis.repr_self]
  have hlm : Algebra.leftMulMatrix b ω = !![0, 1; 1, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Algebra.leftMulMatrix_eq_repr_mul, hb0, hb1, hrepr0, hrepr1]
  let ε : F4 →+* Matrix (Fin 2) (Fin 2) F2 :=
    (RingHom.mapMatrix (ZMod.castHom (dvd_refl 2) F2)).comp (Algebra.leftMulMatrix b).toRingHom
  refine ⟨ω, ε, hω, ?_⟩
  change RingHom.mapMatrix (ZMod.castHom (dvd_refl 2) F2) (Algebra.leftMulMatrix b ω) = _
  rw [hlm]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [RingHom.mapMatrix_apply]

@[expose] noncomputable def f4Omega : F4 := exists_f4_frame.choose

@[expose] noncomputable def f4Eps : F4 →+* Matrix (Fin 2) (Fin 2) F2 := exists_f4_frame.choose_spec.choose

theorem f4Omega_sq : f4Omega ^ 2 + f4Omega + 1 = 0 :=
  exists_f4_frame.choose_spec.choose_spec.1

theorem f4Eps_omega : f4Eps f4Omega = !![0, 1; 1, 1] :=
  exists_f4_frame.choose_spec.choose_spec.2

theorem f4Omega_ne_zero : f4Omega ≠ 0 := by
  intro h
  have hsq := f4Omega_sq
  rw [h] at hsq
  exact (one_ne_zero : (1 : F4) ≠ 0) (by simpa using hsq)

theorem f4Omega_ne_one : f4Omega ≠ 1 := by
  intro h
  have hsq := f4Omega_sq
  rw [h] at hsq
  exact (one_ne_zero : (1 : F4) ≠ 0) (by simpa [CharTwo.add_self_eq_zero] using hsq)

theorem f4Omega_pow_three : f4Omega ^ 3 = 1 := by
  linear_combination (f4Omega - 1) * f4Omega_sq

private theorem f4Omega_sq_eq : f4Omega ^ 2 = f4Omega + 1 := sq_eq_add_one f4Omega_sq

private theorem f4_factor (a : F4) :
    a ^ 4 + a = a * (a + 1) * (a + f4Omega) * (a + f4Omega ^ 2) := by
  have h1 : f4Omega + f4Omega ^ 2 = 1 := by
    rw [f4Omega_sq_eq, ← add_assoc, CharTwo.add_self_eq_zero, zero_add]
  have h3 : f4Omega * f4Omega ^ 2 = 1 := by rw [← pow_succ', f4Omega_pow_three]
  have hq : (a + f4Omega) * (a + f4Omega ^ 2) = a ^ 2 + a + 1 := by
    calc (a + f4Omega) * (a + f4Omega ^ 2)
        = a ^ 2 + (f4Omega + f4Omega ^ 2) * a + f4Omega * f4Omega ^ 2 := by ring
      _ = a ^ 2 + 1 * a + 1 := by rw [h1, h3]
      _ = a ^ 2 + a + 1 := by ring
  calc a ^ 4 + a = a * (a + 1) * (a ^ 2 + a + 1) :=
        (mul_add_one_mul_sq_add_self_add_one a).symm
    _ = a * (a + 1) * ((a + f4Omega) * (a + f4Omega ^ 2)) := by rw [hq]
    _ = a * (a + 1) * (a + f4Omega) * (a + f4Omega ^ 2) := by ring

theorem f4_cases (a : F4) : a = 0 ∨ a = 1 ∨ a = f4Omega ∨ a = f4Omega ^ 2 := by
  have hzero : a ^ 4 + a = 0 := by rw [f4_pow_four, CharTwo.add_self_eq_zero]
  have h : a * (a + 1) * (a + f4Omega) * (a + f4Omega ^ 2) = 0 := by
    rw [← f4_factor a]
    exact hzero
  rcases mul_eq_zero.mp h with h | h
  · rcases mul_eq_zero.mp h with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl (eq_of_add_eq_zero h))
    · exact Or.inr (Or.inr (Or.inl (eq_of_add_eq_zero h)))
  · exact Or.inr (Or.inr (Or.inr (eq_of_add_eq_zero h)))

private theorem f4Eps_omega_sq : f4Eps (f4Omega ^ 2) = !![1, 1; 1, 0] := by
  rw [map_pow, f4Eps_omega]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, pow_two, CharTwo.add_self_eq_zero]

private theorem f4Omega_four : f4Omega ^ 4 = f4Omega := by
  rw [pow_succ, f4Omega_pow_three, one_mul]

private theorem f4Omega_sq_sq : (f4Omega ^ 2) ^ 2 = f4Omega := by
  rw [← pow_mul, show 2 * 2 = 4 from rfl, f4Omega_four]

theorem f4Eps_transpose (a : F4) : (f4Eps a).transpose = f4Eps a := by
  rcases f4_cases a with rfl | rfl | rfl | rfl
  · simp
  · simp
  · ext i j; fin_cases i <;> fin_cases j <;> simp [f4Eps_omega]
  · rw [map_pow, f4Eps_omega]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.transpose_apply, Matrix.mul_apply, Fin.sum_univ_two, pow_two,
        CharTwo.add_self_eq_zero]

theorem f4Eps_sq (a : F4) :
    f4Eps (a ^ 2) = !![1, 1; 0, 1] * f4Eps a * !![1, 1; 0, 1] := by
  rcases f4_cases a with rfl | rfl | rfl | rfl
  · simp
  · rw [one_pow, map_one]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, CharTwo.add_self_eq_zero]
  · rw [map_pow, f4Eps_omega]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, pow_two, CharTwo.add_self_eq_zero]
  · rw [f4Omega_sq_sq, f4Eps_omega, f4Eps_omega_sq]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, CharTwo.add_self_eq_zero]

end CFSG.StandardType.GGHalf

end
