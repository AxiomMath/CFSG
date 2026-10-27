module

public import CFSG.Quasithin.Background.B4ModelsLie
public import CFSG.Quasithin.Background.G64RealizeSec

public section

namespace CFSG.Quasithin.H13.SL3

open CFSG.Assembly.LowTwoRank Matrix CFSG.Quasithin

variable {F : Type} [Field F]

theorem frobPow_single_transpose' {ι : Type} [DecidableEq ι] (a : ℕ) (i j : ι) :
    (frobPow a (Matrix.single i j (1 : F)))ᵀ = Matrix.single j i 1 := by
  ext k l
  simp only [Matrix.transpose_apply, frobPow, Matrix.map_apply, Matrix.single_apply]
  split_ifs with h1 h2 h2
  · exact one_pow _
  · exact absurd ⟨h1.2, h1.1⟩ h2
  · exact absurd ⟨h2.2, h2.1⟩ h1
  · exact zero_pow (by positivity)

theorem eq_zero_of_mul_pow_eq_zero {x : F} (a : ℕ) (h : x * x ^ 2 ^ a = 0) : x = 0 := by
  rcases mul_eq_zero.mp h with h | h
  · exact h
  · exact pow_eq_zero_iff (by positivity) |>.mp h

theorem twistTensor_ker_scalar [CharP F 2] (a : ℕ) {W : Type*} [CommGroup W]
    {H : Subgroup (MulAut W)} {π : (FFModel.twistTensor a (StatedSL 3 F)).Gam →* ↥H}
    (h : (FFModel.twistTensor a (StatedSL 3 F)).RealizesVia H ⊤ ⊥ π)
    (g : ↥(StatedSL 3 F)) (hg : π g = 1) :
    ∃ c : F, ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = c • 1 := by
  obtain ⟨f, hfs, -, hfe⟩ := G64.RealizesVia.exists_secMap rfl h
  have key : ∀ X : Matrix (Fin 3) (Fin 3) F, (frobPow a X)ᵀ = X →
      ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * X *
        (frobPow a ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F))ᵀ = X := by
    intro X hX
    obtain ⟨u, hu⟩ := hfs ⟨Multiplicative.ofAdd X, hX⟩
    have h1 := hfe g u (Subgroup.mem_top _)
    have h2 : (⟨((π g : ↥H) : MulAut W) (u : W), Subgroup.mem_top _⟩ : ↥(⊤ : Subgroup W)) = u := by
      rw [hg]
      rfl
    rw [h2, hu] at h1
    have h3 := congrArg Multiplicative.toAdd h1
    simp only [FFModel.twistTensor, twistAct] at h3
    exact h3.symm
  set m := ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) with hm
  have hE : ∀ i : Fin 3, m * Matrix.single i i 1 * (frobPow a m)ᵀ = Matrix.single i i 1 :=
    fun i => key _ ((frobPow_single_transpose' a i i).trans rfl)
  have hX : ∀ i j : Fin 3, m * (Matrix.single i j 1 + Matrix.single j i 1) * (frobPow a m)ᵀ =
      Matrix.single i j 1 + Matrix.single j i 1 := by
    intro i j
    refine key _ ?_
    have hadd : frobPow a (Matrix.single i j (1 : F) + Matrix.single j i 1) =
        frobPow a (Matrix.single i j 1) + frobPow a (Matrix.single j i 1) := by
      ext k l
      simp only [frobPow, Matrix.map_apply, Matrix.add_apply]
      exact add_pow_char_pow _ _ 2 a
    rw [hadd, Matrix.transpose_add, frobPow_single_transpose', frobPow_single_transpose',
      add_comm]
  have hent : ∀ i k l : Fin 3, m k i * m l i ^ 2 ^ a = if k = i ∧ l = i then 1 else 0 := by
    intro i k l
    have := congrFun (congrFun (hE i) k) l
    simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply, frobPow,
      Matrix.map_apply, Matrix.single_apply] at this
    fin_cases i <;> fin_cases k <;> fin_cases l <;> simpa using this
  have hoff : ∀ i k : Fin 3, k ≠ i → m k i = 0 := by
    intro i k hki
    have := hent i k k
    split_ifs at this with h
    · exact absurd h.1 hki
    · exact eq_zero_of_mul_pow_eq_zero a this
  have hdiag : ∀ i : Fin 3, m i i * m i i ^ 2 ^ a = 1 := by
    intro i
    have := hent i i i
    split_ifs at this with h
    · exact this
    · exact absurd ⟨rfl, rfl⟩ h
  have hpair : ∀ i j : Fin 3, i ≠ j → m i i * m j j ^ 2 ^ a = 1 := by
    intro i j hij
    have := congrFun (congrFun (hX i j) i) j
    simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply, frobPow,
      Matrix.map_apply, Matrix.add_apply, Matrix.single_apply] at this
    fin_cases i <;> fin_cases j <;> simp_all
  have hne : ∀ j : Fin 3, m j j ^ 2 ^ a ≠ 0 := by
    intro j h0
    have := hdiag j
    rw [h0, mul_zero] at this
    exact zero_ne_one this
  have heq : ∀ i j : Fin 3, i ≠ j → m i i = m j j := fun i j hij =>
    mul_right_cancel₀ (hne j) ((hpair i j hij).trans (hdiag j).symm)
  refine ⟨m 0 0, ?_⟩
  ext k l
  by_cases hkl : k = l
  · subst hkl
    fin_cases k
    · simp
    · simp [heq 1 0 (by decide)]
    · simp [heq 2 0 (by decide)]
  · rw [hoff l k hkl]
    simp [Matrix.one_apply_ne hkl]

end CFSG.Quasithin.H13.SL3
