module

public import CFSG.LocalAnalysis.StandardType.ZS.ImpExtSetting
import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.Basic

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

public section

namespace CFSG.StandardType.ZS

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]

theorem phiForm_apply (f : Module.Basis (Fin 4) (ZMod p) U) (x : U) :
    phiForm f x = ∑ i : Fin 4, (if i = 3 then (-1 : ZMod p) else 1) * (f.repr x i) ^ 2 := by
  simp [phiForm, QuadraticMap.weightedSumSquares_apply, smul_eq_mul, pow_two]

theorem phiForm_polarBilin_apply (f : Module.Basis (Fin 4) (ZMod p) U) (x y : U) :
    QuadraticMap.polar (phiForm f) x y =
      2 * ∑ i : Fin 4,
        (if i = 3 then (-1 : ZMod p) else 1) * f.repr x i * f.repr y i := by
  rw [QuadraticMap.polar, phiForm_apply, phiForm_apply, phiForm_apply]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_add]
  simp only [Finsupp.add_apply]
  ring_nf

theorem phiForm_polar_basis (f : Module.Basis (Fin 4) (ZMod p) U) (m : U)
    (j : Fin 4) :
    QuadraticMap.polar (phiForm f) m (f j) =
      (2 : ZMod p) * (if j = 3 then (-1 : ZMod p) else 1) * f.repr m j := by
  rw [phiForm_polarBilin_apply]
  rw [Finset.mul_sum]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i hi hij
    simp [Module.Basis.repr_self, Finsupp.single_eq_of_ne hij]
  · intro hj
    exact (hj (Finset.mem_univ j)).elim

theorem phiForm_polarBilin_basis (f : Module.Basis (Fin 4) (ZMod p) U) (m : U)
    (j : Fin 4) :
    QuadraticMap.polarBilin (phiForm f) m (f j) =
      (2 : ZMod p) * (if j = 3 then (-1 : ZMod p) else 1) * f.repr m j := by
  rw [QuadraticMap.polarBilin_apply_apply, phiForm_polar_basis]

theorem phiForm_apply_f3 (f : Module.Basis (Fin 4) (ZMod p) U) :
    phiForm f (f 3) = -1 := by
  rw [phiForm_apply]
  simp [Fin.sum_univ_four, Module.Basis.repr_self]

theorem mem_span_iff_repr_three_eq_zero (f : Module.Basis (Fin 4) (ZMod p) U) (x : U) :
    x ∈ Submodule.span (ZMod p) (Set.range fun i : Fin 3 => f i.castSucc) ↔
      f.repr x 3 = 0 := by
  have hset : Set.range (fun i : Fin 3 => f i.castSucc) =
      f '' Set.range (fun i : Fin 3 => (i.castSucc : Fin 4)) := by
    ext y
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i.castSucc, ⟨i, rfl⟩, rfl⟩
    · rintro ⟨i, ⟨j, rfl⟩, rfl⟩
      exact ⟨j, rfl⟩
  rw [hset, Module.Basis.mem_span_image, Finsupp.support_subset_iff]
  constructor
  · intro h
    by_contra h3
    exact h3 (h 3 (by simp))
  · intro h a ha
    by_cases ha3 : a = 3
    · rw [ha3]
      exact h
    · exfalso
      exact ha ⟨⟨a.val, by omega⟩, by ext; simp [Fin.castSucc]⟩

private lemma exists_coord_ne_zero_of_iso (f : Module.Basis (Fin 4) (ZMod p) U)
    {r : U} (hQr : phiForm f r = 0)
    (hrW : r ∉ Submodule.span (ZMod p) (Set.range fun i : Fin 3 => f i.castSucc)) :
    ∃ k : Fin 3, f.repr r k.castSucc ≠ 0 := by
  by_contra h
  push Not at h
  have h0 : f.repr r (0 : Fin 4) = 0 := by simpa using h (0 : Fin 3)
  have h1 : f.repr r (1 : Fin 4) = 0 := by simpa using h (1 : Fin 3)
  have h2 : f.repr r (2 : Fin 4) = 0 := by simpa using h (2 : Fin 3)
  have hr : r = f.repr r 3 • f 3 := by
    conv_lhs => rw [← Module.Basis.sum_repr f r]
    rw [Fin.sum_univ_four]
    simp [h0, h1, h2]
  have hQ : phiForm f r = -(f.repr r 3) ^ 2 := by
    conv_lhs => rw [hr]
    rw [QuadraticMap.map_smul, phiForm_apply_f3]
    ring
  have hc2 : (f.repr r 3) ^ 2 = 0 := by
    have : -((f.repr r 3) ^ 2) = 0 := by rw [← hQ]; exact hQr
    exact neg_eq_zero.mp this
  have h3 : f.repr r 3 = 0 := mul_self_eq_zero.mp (by simpa [pow_two] using hc2)
  exact hrW ((mem_span_iff_repr_three_eq_zero f r).mpr h3)

private lemma exists_distinct_triple (k : Fin 3) :
    ∃ k' k'' : Fin 3, k ≠ k' ∧ k ≠ k'' ∧ k' ≠ k'' := by
  fin_cases k
  · exact ⟨1, 2, by decide, by decide, by decide⟩
  · exact ⟨0, 2, by decide, by decide, by decide⟩
  · exact ⟨0, 1, by decide, by decide, by decide⟩

theorem phiForm_apply_triple (f : Module.Basis (Fin 4) (ZMod p) U) {k k' k'' : Fin 3}
    (hkk' : k ≠ k') (hkk'' : k ≠ k'') (hk'k'' : k' ≠ k'') (c a b : ZMod p) :
    phiForm f (c • f k.castSucc + a • f k'.castSucc + b • f k''.castSucc) =
      c ^ 2 + a ^ 2 + b ^ 2 := by
  rw [phiForm_apply]
  fin_cases k <;> fin_cases k' <;> fin_cases k'' <;>
    simp_all [Fin.sum_univ_four, Module.Basis.repr_self, Finsupp.single_apply]
  all_goals ring

private lemma mem_span_triple (f : Module.Basis (Fin 4) (ZMod p) U) {k k' k'' : Fin 3}
    (c a b : ZMod p) :
    c • f k.castSucc + a • f k'.castSucc + b • f k''.castSucc ∈
      Submodule.span (ZMod p) (Set.range fun i : Fin 3 => f i.castSucc) := by
  exact Submodule.add_mem _ (Submodule.add_mem _
    (Submodule.smul_mem _ c (Submodule.subset_span ⟨k, rfl⟩))
    (Submodule.smul_mem _ a (Submodule.subset_span ⟨k', rfl⟩)))
    (Submodule.smul_mem _ b (Submodule.subset_span ⟨k'', rfl⟩))

private lemma polar_diff_triple (f : Module.Basis (Fin 4) (ZMod p) U) {k k' k'' : Fin 3}
    {r : U} (a b : ZMod p) :
    QuadraticMap.polar (phiForm f) r
        ((1 : ZMod p) • f k.castSucc + a • f k'.castSucc + b • f k''.castSucc) -
      QuadraticMap.polar (phiForm f) r
        ((-1 : ZMod p) • f k.castSucc + a • f k'.castSucc + b • f k''.castSucc) =
      (4 : ZMod p) * f.repr r k.castSucc := by
  rw [← QuadraticMap.polarBilin_apply_apply, ← QuadraticMap.polarBilin_apply_apply]
  rw [← map_sub]
  have huv : ((1 : ZMod p) • f k.castSucc + a • f k'.castSucc + b • f k''.castSucc) -
      ((-1 : ZMod p) • f k.castSucc + a • f k'.castSucc + b • f k''.castSucc) =
      (2 : ZMod p) • f k.castSucc := by
    module
  rw [huv, map_smul, phiForm_polarBilin_basis]
  have hk3 : (k.castSucc : Fin 4) ≠ 3 := ne_of_lt (Fin.castSucc_lt_last k)
  simp [hk3]
  ring

private lemma exists_isotropic_span (hp : p ≠ 2) (f : Module.Basis (Fin 4) (ZMod p) U) {r : U}
    {k k' k'' : Fin 3} (hk : f.repr r k.castSucc ≠ 0) (hkk' : k ≠ k') (hkk'' : k ≠ k'')
    (hk'k'' : k' ≠ k'') :
    ∃ u ∈ Submodule.span (ZMod p) (Set.range fun i : Fin 3 => f i.castSucc),
      phiForm f u = 0 ∧ QuadraticMap.polar (phiForm f) r u ≠ 0 := by
  obtain ⟨a, b, hab⟩ := ZMod.sq_add_sq p (-1 : ZMod p)
  let u : U := (1 : ZMod p) • f k.castSucc + a • f k'.castSucc + b • f k''.castSucc
  let u' : U := (-1 : ZMod p) • f k.castSucc + a • f k'.castSucc + b • f k''.castSucc
  have hQu : phiForm f u = 0 := by
    dsimp [u]
    rw [phiForm_apply_triple f hkk' hkk'' hk'k'']
    ring_nf
    linear_combination hab
  have hQu' : phiForm f u' = 0 := by
    dsimp [u']
    rw [phiForm_apply_triple f hkk' hkk'' hk'k'']
    ring_nf
    linear_combination hab
  have huW : u ∈ Submodule.span (ZMod p) (Set.range fun i : Fin 3 => f i.castSucc) := by
    dsimp [u]
    exact mem_span_triple f 1 a b
  have hu'W : u' ∈ Submodule.span (ZMod p) (Set.range fun i : Fin 3 => f i.castSucc) := by
    dsimp [u']
    exact mem_span_triple f (-1) a b
  have hdiff : QuadraticMap.polar (phiForm f) r u - QuadraticMap.polar (phiForm f) r u' =
      (4 : ZMod p) * f.repr r k.castSucc := by
    dsimp [u, u']
    exact polar_diff_triple f a b
  have hnonzero : QuadraticMap.polar (phiForm f) r u ≠ 0 ∨
      QuadraticMap.polar (phiForm f) r u' ≠ 0 := by
    by_contra h
    push Not at h
    obtain ⟨h1, h2⟩ := h
    have hzero : (4 : ZMod p) * f.repr r k.castSucc = 0 := by
      rw [← hdiff, h1, h2, sub_zero]
    have h2' : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
    have h4 : (4 : ZMod p) ≠ 0 := by
      rw [show (4 : ZMod p) = 2 * 2 by norm_num]
      exact mul_ne_zero h2' h2'
    exact hk ((mul_eq_zero.mp hzero).resolve_left h4)
  rcases hnonzero with h | h
  · exact ⟨u, huW, hQu, h⟩
  · exact ⟨u', hu'W, hQu', h⟩

theorem phiForm_apply_smul_two (f : Module.Basis (Fin 4) (ZMod p) U) (a b : ZMod p) :
    phiForm f (a • f 0 + b • f 1) = a ^ 2 + b ^ 2 := by
  rw [phiForm_apply]
  simp [Fin.sum_univ_four, Module.Basis.repr_self, Finsupp.single_apply]

private lemma exists_isom_span_of_anisotropic (hp : p ≠ 2)
    (f : Module.Basis (Fin 4) (ZMod p) U) {r : U} (hQr : phiForm f r ≠ 0) :
    ∃ h : U ≃ₗ[ZMod p] U, IsIsom p (phiForm f) h ∧
      h r ∈ Submodule.span (ZMod p) (Set.range fun i : Fin 3 => f i.castSucc) := by
  obtain ⟨a, b, hab⟩ := ZMod.sq_add_sq p (phiForm f r)
  let u : U := a • f 0 + b • f 1
  have huW : u ∈ Submodule.span (ZMod p) (Set.range fun i : Fin 3 => f i.castSucc) := by
    dsimp [u]
    refine Submodule.add_mem _ ?_ ?_
    · exact Submodule.smul_mem _ a (Submodule.subset_span ⟨(0 : Fin 3), rfl⟩)
    · exact Submodule.smul_mem _ b (Submodule.subset_span ⟨(1 : Fin 3), rfl⟩)
  have hQu : phiForm f u = phiForm f r := by
    dsimp [u]
    rw [phiForm_apply_smul_two, hab]
  let _ : NeZero (2 : ZMod p) := ⟨ZMod.prime_ne_zero p 2 hp⟩
  obtain ⟨e, he⟩ := QuadraticMap.exists_isometryEquiv_apply_eq_of_map_eq
    (Q := phiForm f) hQu.symm (by rw [hQu]; exact hQr)
  refine ⟨e.toLinearEquiv, fun x => e.map_app x, ?_⟩
  have he' : e.toLinearEquiv r = u := he
  rw [he']
  exact huW

private lemma exists_isom_span_of_isotropic (hp : p ≠ 2)
    (f : Module.Basis (Fin 4) (ZMod p) U) {r : U} (hQr : phiForm f r = 0)
    (hrW : r ∉ Submodule.span (ZMod p) (Set.range fun i : Fin 3 => f i.castSucc)) :
    ∃ h : U ≃ₗ[ZMod p] U, IsIsom p (phiForm f) h ∧
      h r ∈ Submodule.span (ZMod p) (Set.range fun i : Fin 3 => f i.castSucc) := by
  obtain ⟨k, hk⟩ := exists_coord_ne_zero_of_iso f hQr hrW
  obtain ⟨k', k'', hkk', hkk'', hk'k''⟩ := exists_distinct_triple k
  obtain ⟨u, huW, hQu, hpol⟩ := exists_isotropic_span hp f (r := r) hk hkk' hkk'' hk'k''
  have hQsub : phiForm f (r - u) = -QuadraticMap.polar (phiForm f) r u := by
    rw [QuadraticMap.polar]
    rw [sub_eq_add_neg, QuadraticMap.map_add (phiForm f) r (-u),
      QuadraticMap.map_neg (phiForm f) u, hQr, hQu]
    rw [QuadraticMap.map_add (phiForm f) r u, hQr, hQu,
      QuadraticMap.polar_neg_right (phiForm f) r u]
    ring
  have hQsub_ne : phiForm f (r - u) ≠ 0 := by
    rw [hQsub]
    exact neg_ne_zero.mpr hpol
  let _ : Invertible (phiForm f (r - u)) := invertibleOfNonzero hQsub_ne
  refine ⟨TauCeti.QuadraticMap.reflection (phiForm f) (r - u), ?_, ?_⟩
  · intro x
    exact TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup
      (TauCeti.QuadraticMap.reflection_mem_orthogonalGroup (phiForm f) (r - u)) x
  · rw [TauCeti.QuadraticMap.reflection_sub_apply_eq_of_map_eq (phiForm f) r u ?_]
    · exact huW
    · rw [hQr, hQu]

theorem exists_isIsom_apply_mem_span (hp : p ≠ 2) (f : Module.Basis (Fin 4) (ZMod p) U)
    (r : U) : ∃ h : U ≃ₗ[ZMod p] U, IsIsom p (phiForm f) h ∧
      h r ∈ Submodule.span (ZMod p) (Set.range fun i : Fin 3 => f i.castSucc) := by
  by_cases hrW : r ∈ Submodule.span (ZMod p) (Set.range fun i : Fin 3 => f i.castSucc)
  · exact ⟨1, fun _ => rfl, by simpa using hrW⟩
  · by_cases hQr : phiForm f r ≠ 0
    · exact exists_isom_span_of_anisotropic hp f hQr
    · exact exists_isom_span_of_isotropic hp f (not_not.mp hQr) hrW


end CFSG.StandardType.ZS

end
