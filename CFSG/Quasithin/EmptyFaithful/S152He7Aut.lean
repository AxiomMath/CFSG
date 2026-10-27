module

public import CFSG.Quasithin.EmptyFaithful.S152He5Aut
public import CFSG.Quasithin.EmptyFaithful.S152He6IiiAbs

public section

namespace CFSG.Quasithin.He7

open CFSG.Quasithin.He5 CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.Quasithin.He6

variable {n : ℕ}

theorem innP_conj_mem (y : MulAut (projectiveSL n K2)) {g : MulAut (projectiveSL n K2)}
    (hg : g ∈ InnP n) : y * g * y⁻¹ ∈ InnP n := by
  obtain ⟨p, rfl⟩ := hg
  exact ⟨y p, conj_apply_aut y p⟩

theorem isSimpleGroup_innP (hn : 3 ≤ n) : IsSimpleGroup ↥(InnP n) := by
  have hs0 : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin n) K2) :=
    (CFSG.LinearGroups.linear_projective_simple (K := K2) (n := n) (by omega) (Or.inl hn)).2.1
  have hs : IsSimpleGroup (projectiveSL n K2) :=
    (LinearCover.projectiveSpecialLinearEquivProjectiveSL n K2).symm.isSimpleGroup
  have := hs
  exact (MonoidHom.ofInjective (conj_injective n)).symm.isSimpleGroup

theorem eq_one_of_commute_innP {y : MulAut (projectiveSL n K2)}
    (h : ∀ g ∈ InnP n, y * g = g * y) : y = 1 := by
  refine MulEquiv.ext fun p => ?_
  have h1 := h (MulAut.conj p) ⟨p, rfl⟩
  have h2 : MulAut.conj (y p) = (MulAut.conj p : MulAut (projectiveSL n K2)) := by
    rw [conj_apply_aut, h1]
    group
  exact conj_injective n h2

theorem eq_bot_or_eq_of_normal' {Y : Type*} [Group Y] {A N : Subgroup Y} (hA : IsSimpleGroup ↥A)
    (hNA : N ≤ A) (hN : ∀ g ∈ A, ∀ m ∈ N, g * m * g⁻¹ ∈ N) : N = ⊥ ∨ N = A := by
  have hnorm : (N.subgroupOf A).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hNA]
    exact fun h g hh hg => hN g hg h hh
  have := hnorm
  rcases hA.eq_bot_or_eq_top_of_normal (N.subgroupOf A) with h | h
  · left
    rw [Subgroup.subgroupOf_eq_bot] at h
    exact h.eq_bot_of_le hNA
  · right
    rw [Subgroup.subgroupOf_eq_top] at h
    exact le_antisymm hNA h

theorem hom_injective_or_exp_two (hn : 3 ≤ n) {H : Type*} [Group H]
    (φ : MulAut (projectiveSL n K2) →* H) : Function.Injective φ ∨ ∀ y, φ y * φ y = 1 := by
  have hker : ∀ g : MulAut (projectiveSL n K2), ∀ k ∈ φ.ker, g * k * g⁻¹ ∈ φ.ker := fun g k hk => by
    rw [MonoidHom.mem_ker] at hk ⊢
    rw [map_mul, map_mul, hk, mul_one, map_inv, mul_inv_cancel]
  have hN : ∀ g ∈ InnP n, ∀ m ∈ φ.ker ⊓ InnP n, g * m * g⁻¹ ∈ φ.ker ⊓ InnP n := fun g hg m hm =>
    ⟨hker g m hm.1, (InnP n).mul_mem ((InnP n).mul_mem hg hm.2) ((InnP n).inv_mem hg)⟩
  rcases eq_bot_or_eq_of_normal' (isSimpleGroup_innP hn) inf_le_right hN with h | h
  · left
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro k hk
    rw [Subgroup.mem_bot]
    refine eq_one_of_commute_innP fun g hg => ?_
    have h1 : k * g * k⁻¹ * g⁻¹ ∈ φ.ker ⊓ InnP n := by
      refine ⟨?_, ?_⟩
      · have := (φ.ker).mul_mem hk (hker g k⁻¹ ((φ.ker).inv_mem hk))
        simpa [mul_assoc] using this
      · exact (InnP n).mul_mem (innP_conj_mem k hg) ((InnP n).inv_mem hg)
    rw [h, Subgroup.mem_bot] at h1
    calc k * g = k * g * k⁻¹ * g⁻¹ * (g * k) := by group
      _ = g * k := by rw [h1, one_mul]
  · right
    intro y
    have h1 : y ^ 2 ∈ InnP n := Subgroup.sq_mem_of_index_two (index_inn_eq_two hn) y
    have h2 : y ^ 2 ∈ φ.ker ⊓ InnP n := by
      rw [h]
      exact h1
    have h3 : φ (y ^ 2) = 1 := h2.1
    rw [map_pow, sq] at h3
    exact h3

section Center

open scoped Matrix

theorem not_fixes_upper (hn : 3 ≤ n) (A : GL (Fin n) K2)
    (hfix : ∀ g ∈ projUpperTriangular n K2, (LinearFlag.conjAut n K2 A * LinearFlag.dualAut n K2) g = g) : False := by
  have key : ∀ i j : Fin n, i < j →
      (A : Matrix (Fin n) (Fin n) K2) * Matrix.single j i (1 : K2) =
        Matrix.single i j (1 : K2) * (A : Matrix (Fin n) (Fin n) K2) := by
    intro i j hij
    have hne : i ≠ j := ne_of_lt hij
    let t : Matrix.SpecialLinearGroup (Fin n) K2 :=
      ⟨Matrix.transvection i j (1 : K2), Matrix.det_transvection_of_ne i j hne 1⟩
    have ht : t ∈ LinearFlag.upperTriangular n K2 := by
      intro a b hab
      have hab' : a ≠ b := ne_of_gt hab
      have : ¬ (i = a ∧ j = b) := fun h => by
        have h1 : a = i := h.1.symm
        have h2 : b = j := h.2.symm
        rw [h1, h2] at hab
        exact absurd hij (not_lt_of_gt hab)
      simp [t, Matrix.transvection, hab', this]
    have h1 := hfix (proj n K2 t) (Subgroup.mem_map_of_mem _ ht)
    rw [MulAut.mul_apply, LinearFlag.dualAut_proj, LinearFlag.conjAut_proj] at h1
    have h2 := proj_injective n h1
    have htt : t * t = 1 := by
      apply Subtype.ext
      show Matrix.transvection i j (1 : K2) * Matrix.transvection i j (1 : K2) = 1
      rw [Matrix.transvection_mul_transvection_same i j hne]
      have : (1 : K2) + 1 = 0 := by decide
      rw [this, Matrix.transvection_zero]
    have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
    rw [hti] at h2
    have h3 := congrArg (fun g : Matrix.SpecialLinearGroup (Fin n) K2 => (g : Matrix (Fin n) (Fin n) K2)) h2
    simp only [LinearFlag.coe_slConjugation, Matrix.SpecialLinearGroup.coe_transpose] at h3
    have hAi : ((A⁻¹ : GL (Fin n) K2) : Matrix (Fin n) (Fin n) K2) * (A : Matrix (Fin n) (Fin n) K2) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have hT : (t : Matrix (Fin n) (Fin n) K2) = 1 + Matrix.single i j (1 : K2) := rfl
    have hTt : (t : Matrix (Fin n) (Fin n) K2)ᵀ = 1 + Matrix.single j i (1 : K2) := by
      rw [hT, Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_single]
    have h4 : (A : Matrix (Fin n) (Fin n) K2) * (t : Matrix (Fin n) (Fin n) K2)ᵀ =
        (t : Matrix (Fin n) (Fin n) K2) * (A : Matrix (Fin n) (Fin n) K2) :=
      calc (A : Matrix (Fin n) (Fin n) K2) * (t : Matrix (Fin n) (Fin n) K2)ᵀ
          = (A : Matrix (Fin n) (Fin n) K2) * (t : Matrix (Fin n) (Fin n) K2)ᵀ * 1 := (mul_one _).symm
        _ = (A : Matrix (Fin n) (Fin n) K2) * (t : Matrix (Fin n) (Fin n) K2)ᵀ *
            (((A⁻¹ : GL (Fin n) K2) : Matrix (Fin n) (Fin n) K2) * (A : Matrix (Fin n) (Fin n) K2)) := by
            rw [hAi]
        _ = ((A : Matrix (Fin n) (Fin n) K2) * (t : Matrix (Fin n) (Fin n) K2)ᵀ *
            ((A⁻¹ : GL (Fin n) K2) : Matrix (Fin n) (Fin n) K2)) * (A : Matrix (Fin n) (Fin n) K2) :=
            (Matrix.mul_assoc _ _ _).symm
        _ = (t : Matrix (Fin n) (Fin n) K2) * (A : Matrix (Fin n) (Fin n) K2) := by rw [h3]
    rw [hTt, hT, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul] at h4
    exact add_left_cancel h4
  have h1 := key ⟨0, by omega⟩ ⟨1, by omega⟩ (by simp [Fin.lt_def])
  have h2 := key ⟨1, by omega⟩ ⟨2, by omega⟩ (by simp [Fin.lt_def])
  have hne02 : (⟨2, by omega⟩ : Fin n) ≠ ⟨0, by omega⟩ := by simp [Fin.ext_iff]
  have hcol : ∀ a : Fin n, (A : Matrix (Fin n) (Fin n) K2) a ⟨2, by omega⟩ = 0 := by
    intro a
    have e12 : (A : Matrix (Fin n) (Fin n) K2) ⟨1, by omega⟩ ⟨2, by omega⟩ = 0 := by
      have := congrFun (congrFun h1 ⟨0, by omega⟩) ⟨2, by omega⟩
      rw [Matrix.mul_single_apply_of_ne _ _ _ _ _ hne02, Matrix.single_mul_apply_same] at this
      simpa using this.symm
    by_cases ha : a = ⟨1, by omega⟩
    · rw [ha]
      exact e12
    · have := congrFun (congrFun h2 a) ⟨1, by omega⟩
      rw [Matrix.mul_single_apply_same, Matrix.single_mul_apply_of_ne _ _ _ _ _ ha] at this
      simpa using this
  have hdet : (A : Matrix (Fin n) (Fin n) K2).det = 0 :=
    Matrix.det_eq_zero_of_column_eq_zero ⟨2, by omega⟩ hcol
  have := (Matrix.GeneralLinearGroup.det A).ne_zero
  rw [Matrix.GeneralLinearGroup.val_det_apply] at this
  exact this hdet

theorem eq_inn_of_commute_sylow (hn : 3 ≤ n) {T : Subgroup (MulAut (projectiveSL n K2))}
    (hT : IsPGroup 2 ↥T) (hTi : ¬ 2 ∣ T.index) {y : MulAut (projectiveSL n K2)}
    (hy : ∀ t ∈ T, y * t = t * y) : y ∈ InnP n := by
  have := finite_mulAut n
  by_contra hyi
  obtain ⟨hU2, hUi⟩ := projUpperTriangular_sylow n (by omega)
  have hS₁ : IsPGroup 2 ↥((projUpperTriangular n K2).map
      (MulAut.conj : projectiveSL n K2 →* MulAut (projectiveSL n K2))) := hU2.map _
  obtain ⟨g, hg⟩ := exists_conj_le_of_two_sylow hT hTi hS₁
  have hfix1 : ∀ u ∈ projUpperTriangular n K2, y (g u) = g u := by
    intro u hu
    have h1 := hg (MulAut.conj u) ⟨u, hu, rfl⟩
    have h2 := hy _ h1
    have h3 : (MulAut.conj (y (g u)) : MulAut (projectiveSL n K2)) = MulAut.conj (g u) := by
      rw [conj_apply_aut y (g u), conj_apply_aut g u]
      calc y * (g * MulAut.conj u * g⁻¹) * y⁻¹ = (g * MulAut.conj u * g⁻¹) * y * y⁻¹ := by rw [h2]
        _ = g * MulAut.conj u * g⁻¹ := by group
    exact conj_injective n h3
  set S : Subgroup (projectiveSL n K2) :=
    (projUpperTriangular n K2).map (g : MulAut (projectiveSL n K2)).toMonoidHom with hS
  have hS2 : IsPGroup 2 ↥S := hU2.map _
  have hSi : ¬ 2 ∣ S.index := by
    have : S.index = (projUpperTriangular n K2).index := Subgroup.index_map_equiv (projUpperTriangular n K2) g
    rw [this]
    exact hUi
  obtain ⟨c, hc⟩ := exists_conj_le_of_two_sylow hS2 hSi hU2
  have hy'fix : ∀ u ∈ projUpperTriangular n K2,
      (MulAut.conj c⁻¹ * y * MulAut.conj c : MulAut (projectiveSL n K2)) u = u := by
    intro u hu
    obtain ⟨u₀, hu₀, hu₀e⟩ := hc u hu
    have h1 : y (c * u * c⁻¹) = c * u * c⁻¹ := by
      rw [← hu₀e]
      exact hfix1 u₀ hu₀
    show MulAut.conj c⁻¹ (y (MulAut.conj c u)) = u
    rw [MulAut.conj_apply c u, h1, MulAut.conj_apply]
    group
  have hy'out : (MulAut.conj c⁻¹ * y * MulAut.conj c : MulAut (projectiveSL n K2)) ∉ InnP n := by
    intro hin
    apply hyi
    have h1 : (MulAut.conj c : MulAut (projectiveSL n K2)) ∈ InnP n := ⟨c, rfl⟩
    have h2 : (MulAut.conj c⁻¹ : MulAut (projectiveSL n K2)) ∈ InnP n := ⟨c⁻¹, rfl⟩
    have h3 := (InnP n).mul_mem ((InnP n).mul_mem h1 hin) h2
    have h4 : (MulAut.conj c : MulAut (projectiveSL n K2)) *
        (MulAut.conj c⁻¹ * y * MulAut.conj c) * MulAut.conj c⁻¹ = y := by
      have e1 : (MulAut.conj c : MulAut (projectiveSL n K2)) * MulAut.conj c⁻¹ = 1 := by
        rw [← map_mul, mul_inv_cancel, map_one]
      have e2 : (MulAut.conj c⁻¹ : MulAut (projectiveSL n K2)) * MulAut.conj c = 1 := by
        rw [← map_mul, inv_mul_cancel, map_one]
      calc (MulAut.conj c : MulAut (projectiveSL n K2)) *
            (MulAut.conj c⁻¹ * y * MulAut.conj c) * MulAut.conj c⁻¹
          = (MulAut.conj c * MulAut.conj c⁻¹) * y * (MulAut.conj c * MulAut.conj c⁻¹) := by group
        _ = y := by rw [e1]; group
    rwa [h4] at h3
  rcases mem_inn_or_eq_conj_dual hn (MulAut.conj c⁻¹ * y * MulAut.conj c) with h | ⟨A, hA⟩
  · exact hy'out h
  · exact not_fixes_upper hn A (fun g hg => by rw [← hA]; exact hy'fix g hg)

end Center

end CFSG.Quasithin.He7
