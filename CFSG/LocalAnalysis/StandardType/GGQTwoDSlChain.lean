module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDSlConj

public section

namespace CFSG.StandardType.QTwo

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace Sl

theorem exists_chain (m : ℕ) {a b c d : Fin m} (hab : a ≠ b) (hcd : c ≠ d) (ε₁ ε₂ : Bool)
    (hnc : dTau m ε₁ a b * dTau m ε₂ c d ≠ dTau m ε₂ c d * dTau m ε₁ a b) :
    ∃ y x z : Fin m, y ≠ x ∧ x ≠ z ∧ y ≠ z ∧
      dTau m ε₁ a b = dTau m ε₁ y x ∧ dTau m ε₂ c d = dTau m ε₂ x z := by
  by_cases hac : a = c
  · by_cases hbd : b = d
    · rw [← hac, ← hbd] at hnc
      exact absurd (comm_of_same m ε₁ ε₂ hab) hnc
    · refine ⟨b, a, d, hab.symm, ?_, hbd, dTau_symm m ε₁ a b, ?_⟩
      · rw [hac]; exact hcd
      · rw [← hac]
  · by_cases had : a = d
    · by_cases hbc : b = c
      · rw [← hbc, ← had, dTau_symm m ε₂ b a] at hnc
        exact absurd (comm_of_same m ε₁ ε₂ hab) hnc
      · refine ⟨b, a, c, hab.symm, hac, hbc, dTau_symm m ε₁ a b, ?_⟩
        rw [← had]
        exact dTau_symm m ε₂ c a
    · by_cases hbc : b = c
      · refine ⟨a, b, d, hab, ?_, had, rfl, ?_⟩
        · rw [hbc]; exact hcd
        · rw [← hbc]
      · by_cases hbd : b = d
        · refine ⟨a, b, c, hab, hbc, hac, rfl, ?_⟩
          rw [← hbd]
          exact dTau_symm m ε₂ c b
        · exact absurd (comm_of_disjoint m ε₁ ε₂ hab hcd hac had hbc hbd) hnc

theorem e_simple_of_lt {m : ℕ} {e : (ggCoxeterMatrixD m).Group ≃* dEven m} (he : IsDEquiv m e)
    {j : Fin m} (hj : j.val + 1 < m) :
    ((e ((ggCoxeterMatrixD m).simple j) : dEven m) : DVec m ≃ₗ[ZMod 3] DVec m) =
      dTau m false j ⟨j.val + 1, hj⟩ := by
  have hdec : decide (j.val + 1 = m) = false := by
    have hne : j.val + 1 ≠ m := by omega
    simp [hne]
  have hlo : OrthTorus.simpleLo j = j := Fin.ext (OrthTorus.simpleLo_of_lt hj)
  have hhi : OrthTorus.simpleHi j = ⟨j.val + 1, hj⟩ := Fin.ext (OrthTorus.simpleHi_of_lt hj)
  rw [he j, hdec, hlo, hhi]

theorem e_simple_last {m : ℕ} (hm : 4 ≤ m) {e : (ggCoxeterMatrixD m).Group ≃* dEven m}
    (he : IsDEquiv m e) {t : Fin m} (ht : t.val + 1 = m) :
    ((e ((ggCoxeterMatrixD m).simple t) : dEven m) : DVec m ≃ₗ[ZMod 3] DVec m) =
      dTau m true ⟨m - 2, by omega⟩ ⟨m - 1, by omega⟩ := by
  have hdec : decide (t.val + 1 = m) = true := by simp [ht]
  have hlo : OrthTorus.simpleLo t = ⟨m - 2, by omega⟩ :=
    Fin.ext (OrthTorus.simpleLo_of_last ht)
  have hhi : OrthTorus.simpleHi t = ⟨m - 1, by omega⟩ :=
    Fin.ext (OrthTorus.simpleHi_of_last ht)
  rw [he t, hdec, hlo, hhi]

theorem coe_conj {m : ℕ} (e : (ggCoxeterMatrixD m).Group ≃* dEven m)
    (u z : (ggCoxeterMatrixD m).Group) :
    ((e (u * z * u⁻¹) : dEven m) : DVec m ≃ₗ[ZMod 3] DVec m) =
      ((e u : dEven m) : DVec m ≃ₗ[ZMod 3] DVec m) *
        ((e z : dEven m) : DVec m ≃ₗ[ZMod 3] DVec m) *
          ((e u : dEven m) : DVec m ≃ₗ[ZMod 3] DVec m)⁻¹ := by
  simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]

theorem exists_dTau_of_conj_simple {m : ℕ} (hm : 4 ≤ m)
    {e : (ggCoxeterMatrixD m).Group ≃* dEven m} (he : IsDEquiv m e)
    (u : (ggCoxeterMatrixD m).Group) (t : Fin m) :
    ∃ (ε : Bool) (a b : Fin m), a ≠ b ∧
      ((e (u * (ggCoxeterMatrixD m).simple t * u⁻¹) : dEven m) : DVec m ≃ₗ[ZMod 3] DVec m) =
        dTau m ε a b := by
  rw [coe_conj, he t]
  exact conj_dTau_exists m (e u).2 _ (OrthTorus.simpleLo_ne_simpleHi (by omega) t)

theorem exists_simple_pair_conj_W {m : ℕ} (hm : 4 ≤ m) {x y : (ggCoxeterMatrixD m).Group}
    (hx : ∃ (u : (ggCoxeterMatrixD m).Group) (t : Fin m),
      x = u * (ggCoxeterMatrixD m).simple t * u⁻¹)
    (hy : ∃ (u : (ggCoxeterMatrixD m).Group) (t : Fin m),
      y = u * (ggCoxeterMatrixD m).simple t * u⁻¹)
    (hne : x * y ≠ y * x) :
    ∃ (w : (ggCoxeterMatrixD m).Group) (i j : Fin m), ggCoxeterMatrixD m i j = 3 ∧
      x = w * (ggCoxeterMatrixD m).simple i * w⁻¹ ∧
      y = w * (ggCoxeterMatrixD m).simple j * w⁻¹ := by
  obtain ⟨e, he⟩ := dEven_equiv hm
  obtain ⟨u₁, t₁, hxu⟩ := hx
  obtain ⟨u₂, t₂, hyu⟩ := hy
  obtain ⟨ε₁, a, b, hab, hX⟩ := exists_dTau_of_conj_simple hm he u₁ t₁
  obtain ⟨ε₂, c, d, hcd, hY⟩ := exists_dTau_of_conj_simple hm he u₂ t₂
  rw [← hxu] at hX
  rw [← hyu] at hY
  have hnc : dTau m ε₁ a b * dTau m ε₂ c d ≠ dTau m ε₂ c d * dTau m ε₁ a b := by
    intro h
    apply hne
    apply e.injective
    apply Subtype.ext
    simp only [map_mul, Subgroup.coe_mul]
    rw [hX, hY]
    exact h
  obtain ⟨y₀, x₀, z₀, h1, h2, h3, hX', hY'⟩ := exists_chain m hab hcd ε₁ ε₂ hnc
  have hm1 : 1 < m := by omega
  have hm2 : 2 < m := by omega
  have hm3 : 3 < m := by omega
  let q₀ : Fin m := ⟨0, by omega⟩
  let q₁ : Fin m := ⟨1, hm1⟩
  let q₂ : Fin m := ⟨2, hm2⟩
  let q₃ : Fin m := ⟨3, hm3⟩
  have h01 : q₀ ≠ q₁ := Fin.ne_of_val_ne (by simp [q₀, q₁])
  have h02 : q₀ ≠ q₂ := Fin.ne_of_val_ne (by simp [q₀, q₂])
  have h03 : q₀ ≠ q₃ := Fin.ne_of_val_ne (by simp [q₀, q₃])
  have h12 : q₁ ≠ q₂ := Fin.ne_of_val_ne (by simp [q₁, q₂])
  have h13 : q₁ ≠ q₃ := Fin.ne_of_val_ne (by simp [q₁, q₃])
  have h23 : q₂ ≠ q₃ := Fin.ne_of_val_ne (by simp [q₂, q₃])
  have hf : Function.Injective ![q₀, q₁, q₂] := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  have hg : Function.Injective ![y₀, x₀, z₀] := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [Ne.symm]
  obtain ⟨π, hπ⟩ := Equiv.Perm.exists_extending_pair _ _ hf hg
  have hπ0 : π q₀ = y₀ := by simpa using hπ 0
  have hπ1 : π q₁ = x₀ := by simpa using hπ 1
  have hπ2 : π q₂ = z₀ := by simpa using hπ 2
  obtain ⟨D, hD, -, hD1, hD2⟩ := exists_conj_pair m h01 h02 h03 h12 h13 h23 ε₁ ε₂
  have hU : dPerm m π * D ∈ dEven m := (dEven m).mul_mem (dPerm_mem_dEven m π) hD
  have hs0 : ((e ((ggCoxeterMatrixD m).simple q₀) : dEven m) : DVec m ≃ₗ[ZMod 3] DVec m) =
      dTau m false q₀ q₁ := e_simple_of_lt he (j := q₀) (by simp [q₀]; omega)
  have hs1 : ((e ((ggCoxeterMatrixD m).simple q₁) : dEven m) : DVec m ≃ₗ[ZMod 3] DVec m) =
      dTau m false q₁ q₂ := e_simple_of_lt he (j := q₁) (by simp [q₁]; omega)
  have hconj : ∀ z : (ggCoxeterMatrixD m).Group,
      ((e (e.symm ⟨dPerm m π * D, hU⟩ * z * (e.symm ⟨dPerm m π * D, hU⟩)⁻¹) : dEven m) :
        DVec m ≃ₗ[ZMod 3] DVec m) =
      (dPerm m π * D) * ((e z : dEven m) : DVec m ≃ₗ[ZMod 3] DVec m) * (dPerm m π * D)⁻¹ := by
    intro z
    rw [coe_conj, MulEquiv.apply_symm_apply]
  refine ⟨e.symm ⟨dPerm m π * D, hU⟩, q₀, q₁, ?_, ?_, ?_⟩
  · exact (OrthTorus.ggCoxeterMatrixD_eq_three_iff (by omega) q₀ q₁).2
      (Or.inl ⟨rfl, by simp [q₁]; omega⟩)
  · apply e.injective
    apply Subtype.ext
    rw [hconj, hs0, hX, hX', ← hπ0, ← hπ1]
    exact (perm_mul_conj_dTau m π hD1).symm
  · apply e.injective
    apply Subtype.ext
    rw [hconj, hs1, hY, hY', ← hπ1, ← hπ2]
    exact (perm_mul_conj_dTau m π hD2).symm

end Sl

end CFSG.StandardType.QTwo

end
