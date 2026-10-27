module

public import CFSG.LocalAnalysis.StandardType.GGRootCentralizerExcBruhat

public section

namespace CFSG.StandardType

namespace RootCentExc

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem iform_eq_of_sum {τ : Tag} {θ : Fin τ.rank → ℤ} {i₀ : Fin τ.rank} {c : ℤ}
    (h : ∀ j, ∑ i, θ i * τ.symmetrizedCartan i j = c * (Pi.single i₀ 1 : Fin τ.rank → ℤ) j)
    (v : Fin τ.rank → ℤ) : CFSG.LieType.Steinberg.Adjoint.iform θ v = c * v i₀ := by
  have e : CFSG.LieType.Steinberg.Adjoint.iform θ v =
      ∑ j, (∑ i, θ i * τ.symmetrizedCartan i j) * v j := by
    rw [CFSG.LieType.Steinberg.Adjoint.iform, Finset.sum_comm]
    simp only [Finset.sum_mul]
  rw [e]
  simp only [h, Pi.single_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]

@[expose] def f4HighRoot : Fin Tag.F4.rank → ℤ := (![2, 3, 4, 2] : Fin 4 → ℤ)

theorem isRoot_f4HighRoot : IsRoot .F4 f4HighRoot :=
  (RootCertificate.isRoot_iff (Tag.rootCertificate_check _)).2 ⟨43, by decide +kernel, by decide +kernel⟩

theorem height_le_of_isRoot_F4 {α : Fin Tag.F4.rank → ℤ}
    (hα : IsRoot .F4 α) : height α ≤ height f4HighRoot := by
  obtain ⟨k, hk, rfl⟩ := (RootCertificate.isRoot_iff (Tag.rootCertificate_check _)).1 hα
  have h : (List.range Tag.F4.rootCertificate.roots.length).all fun k =>
      decide (height (Tag.F4.rootCertificate.root k) ≤ height f4HighRoot) := by decide +kernel
  simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  exact h k hk

theorem highRootData_F4 : HighRootData .F4 f4HighRoot ⟨0, by decide⟩ where
  maxHeight := ⟨isRoot_f4HighRoot, fun _ => height_le_of_isRoot_F4⟩
  coPair := by decide +kernel
  form := ⟨2, by norm_num, iform_eq_of_sum (by decide +kernel)⟩

@[expose] def e6HighRoot : Fin Tag.E6.rank → ℤ := (![1, 2, 2, 3, 2, 1] : Fin 6 → ℤ)

theorem isRoot_e6HighRoot : IsRoot .E6 e6HighRoot :=
  (RootCertificate.isRoot_iff (Tag.rootCertificate_check _)).2 ⟨70, by decide +kernel, by decide +kernel⟩

theorem height_le_of_isRoot_E6 {α : Fin Tag.E6.rank → ℤ}
    (hα : IsRoot .E6 α) : height α ≤ height e6HighRoot := by
  obtain ⟨k, hk, rfl⟩ := (RootCertificate.isRoot_iff (Tag.rootCertificate_check _)).1 hα
  have h : (List.range Tag.E6.rootCertificate.roots.length).all fun k =>
      decide (height (Tag.E6.rootCertificate.root k) ≤ height e6HighRoot) := by decide +kernel
  simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  exact h k hk

theorem highRootData_E6 : HighRootData .E6 e6HighRoot ⟨1, by decide⟩ where
  maxHeight := ⟨isRoot_e6HighRoot, fun _ => height_le_of_isRoot_E6⟩
  coPair := by decide +kernel
  form := ⟨1, by norm_num, iform_eq_of_sum (by decide +kernel)⟩

@[expose] def e7HighRoot : Fin Tag.E7.rank → ℤ := (![2, 2, 3, 4, 3, 2, 1] : Fin 7 → ℤ)

theorem isRoot_e7HighRoot : IsRoot .E7 e7HighRoot :=
  (RootCertificate.isRoot_iff (Tag.rootCertificate_check _)).2 ⟨124, by decide +kernel, by decide +kernel⟩

theorem height_le_of_isRoot_E7 {α : Fin Tag.E7.rank → ℤ}
    (hα : IsRoot .E7 α) : height α ≤ height e7HighRoot := by
  obtain ⟨k, hk, rfl⟩ := (RootCertificate.isRoot_iff (Tag.rootCertificate_check _)).1 hα
  have h : (List.range Tag.E7.rootCertificate.roots.length).all fun k =>
      decide (height (Tag.E7.rootCertificate.root k) ≤ height e7HighRoot) := by decide +kernel
  simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  exact h k hk

theorem highRootData_E7 : HighRootData .E7 e7HighRoot ⟨0, by decide⟩ where
  maxHeight := ⟨isRoot_e7HighRoot, fun _ => height_le_of_isRoot_E7⟩
  coPair := by decide +kernel
  form := ⟨1, by norm_num, iform_eq_of_sum (by decide +kernel)⟩

@[expose] def e8HighRoot : Fin Tag.E8.rank → ℤ := (![2, 3, 4, 6, 5, 4, 3, 2] : Fin 8 → ℤ)

theorem isRoot_e8HighRoot : IsRoot .E8 e8HighRoot :=
  (RootCertificate.isRoot_iff (Tag.rootCertificate_check _)).2 ⟨238, by decide +kernel, by decide +kernel⟩

theorem height_le_of_isRoot_E8 {α : Fin Tag.E8.rank → ℤ}
    (hα : IsRoot .E8 α) : height α ≤ height e8HighRoot := by
  obtain ⟨k, hk, rfl⟩ := (RootCertificate.isRoot_iff (Tag.rootCertificate_check _)).1 hα
  have h : (List.range Tag.E8.rootCertificate.roots.length).all fun k =>
      decide (height (Tag.E8.rootCertificate.root k) ≤ height e8HighRoot) := by decide +kernel
  simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  exact h k hk

theorem highRootData_E8 : HighRootData .E8 e8HighRoot ⟨7, by decide⟩ where
  maxHeight := ⟨isRoot_e8HighRoot, fun _ => height_le_of_isRoot_E8⟩
  coPair := by decide +kernel
  form := ⟨1, by norm_num, iform_eq_of_sum (by decide +kernel)⟩

end RootCentExc

end CFSG.StandardType
