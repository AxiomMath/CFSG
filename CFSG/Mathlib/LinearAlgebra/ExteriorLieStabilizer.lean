module

public import TauCeti.Algebra.Lie.ExteriorPower
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
public import Mathlib.LinearAlgebra.Trace

public noncomputable section

namespace CFSG.LinearAlgebra

section Ring

variable {R : Type*} {M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

theorem map_one_eq_zero_of_leibniz (D : ExteriorAlgebra R M →ₗ[R] ExteriorAlgebra R M)
    (hmul : ∀ x y, D (x * y) = D x * y + x * D y) : D 1 = 0 := by
  have h := hmul 1 1
  simp only [mul_one, one_mul] at h
  simpa using h

theorem apply_ιMulti_of_leibniz (f : Module.End R M)
    (D : ExteriorAlgebra R M →ₗ[R] ExteriorAlgebra R M)
    (hι : ∀ m, D (ExteriorAlgebra.ι R m) = ExteriorAlgebra.ι R (f m))
    (hmul : ∀ x y, D (x * y) = D x * y + x * D y) {n : ℕ} (v : Fin n → M) :
    D (ExteriorAlgebra.ιMulti R n v) =
      ∑ i, ExteriorAlgebra.ιMulti R n (Function.update v i (f (v i))) := by
  induction n with
  | zero =>
    rw [ExteriorAlgebra.ιMulti_zero_apply, map_one_eq_zero_of_leibniz D hmul, Fin.sum_univ_zero]
  | succ n ih =>
    rw [ExteriorAlgebra.ιMulti_succ_apply, hmul, hι, ih, Fin.sum_univ_succ, Finset.mul_sum]
    congr 1
    · rw [ExteriorAlgebra.ιMulti_succ_apply, Function.update_self]
      congr 2
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [ExteriorAlgebra.ιMulti_succ_apply, Function.update_of_ne (Fin.succ_ne_zero i).symm]
      congr 2
      exact (Fin.tail_update_succ v i (f (v i.succ))).symm

theorem apply_coe_of_leibniz (f : Module.End R M)
    (D : ExteriorAlgebra R M →ₗ[R] ExteriorAlgebra R M)
    (hι : ∀ m, D (ExteriorAlgebra.ι R m) = ExteriorAlgebra.ι R (f m))
    (hmul : ∀ x y, D (x * y) = D x * y + x * D y) {n : ℕ} (x : ⋀[R]^n M) :
    D x = (exteriorPower.lieMap n f x : ExteriorAlgebra R M) := by
  have h : D ∘ₗ (⋀[R]^n M).subtype = (⋀[R]^n M).subtype ∘ₗ exteriorPower.lieMap n f := by
    refine exteriorPower.linearMap_ext (AlternatingMap.ext fun v => ?_)
    simp [exteriorPower.ιMulti_apply_coe, apply_ιMulti_of_leibniz f D hι hmul]
  exact LinearMap.congr_fun h x

theorem lieMap_ιMulti_coe_basis_eq_trace_smul {U : Submodule R M} {d : ℕ}
    (b : Module.Basis (Fin d) R U) (f : Module.End R M) (hf : ∀ x ∈ U, f x ∈ U) :
    exteriorPower.lieMap d f (exteriorPower.ιMulti R d (fun i => (b i : M))) =
      LinearMap.trace R U (f.restrict hf) • exteriorPower.ιMulti R d (fun i => (b i : M)) := by
  classical
  have hzero : ∀ r s : Fin d, s ≠ r →
      exteriorPower.ιMulti R d (Function.update (fun i => (b i : M)) r (b s : M)) = 0 :=
    fun r s hs => AlternatingMap.map_update_self _ _ (Ne.symm hs)
  have key : ∀ r : Fin d,
      exteriorPower.ιMulti R d (Function.update (fun i => (b i : M)) r (f (b r))) =
        b.repr (f.restrict hf (b r)) r • exteriorPower.ιMulti R d (fun i => (b i : M)) := by
    intro r
    have hfr : f (b r : M) = ∑ s, b.repr (f.restrict hf (b r)) s • (b s : M) := by
      conv_lhs => rw [← LinearMap.restrict_coe_apply f hf (b r),
        ← b.sum_repr (f.restrict hf (b r))]
      simp only [Submodule.coe_sum, Submodule.coe_smul]
    rw [hfr, AlternatingMap.map_update_sum]
    simp only [AlternatingMap.map_update_smul]
    rw [Finset.sum_eq_single r (fun s _ hs => by rw [hzero r s hs, smul_zero])
      (fun h => absurd (Finset.mem_univ r) h), Function.update_eq_self]
  simp only [exteriorPower.lieMap_apply_ιMulti]
  rw [LinearMap.trace_eq_matrix_trace R b, Matrix.trace, Finset.sum_smul]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply]
  exact key r

theorem exists_basis_span_image_coe {ι : Type*} [LinearOrder ι] (b : Module.Basis ι R M)
    (s : Finset ι) :
    ∃ bs : Module.Basis (Fin s.card) R (Submodule.span R (b '' (s : Set ι))),
      ∀ i, (bs i : M) = b (s.orderEmbOfFin rfl i) := by
  have hli : LinearIndependent R (b ∘ s.orderEmbOfFin rfl) :=
    b.linearIndependent.comp _ (s.orderEmbOfFin rfl).injective
  have hrange : Set.range (b ∘ s.orderEmbOfFin rfl) = b '' (s : Set ι) := by
    rw [Set.range_comp, Finset.range_orderEmbOfFin]
  refine ⟨(Module.Basis.span hli).map (LinearEquiv.ofEq _ _ (by rw [hrange])), fun i => ?_⟩
  rw [Module.Basis.map_apply, LinearEquiv.coe_ofEq_apply, Module.Basis.span_apply]
  rfl

theorem basis_exteriorAlgebra_eq_coe_ιMulti {ι : Type*} [LinearOrder ι] (b : Module.Basis ι R M)
    (s : Finset ι) :
    b.ExteriorAlgebra s =
      (exteriorPower.ιMulti R s.card (fun i => b (s.orderEmbOfFin rfl i)) :
        ExteriorAlgebra R M) := by
  rw [exteriorPower.ιMulti_apply_coe]
  have h := ExteriorAlgebra.basis_apply_powersetCard b
    (Set.powersetCard.ofCard (rfl : s.card = s.card))
  rw [Set.powersetCard.val_ofCard] at h
  rw [h, ExteriorAlgebra.ιMulti_family, Set.powersetCard.ofFinEmbEquiv_symm_apply]
  rfl

theorem exists_coe_ιMulti_basis_eq_basis_exteriorAlgebra {ι : Type*} [LinearOrder ι]
    (b : Module.Basis ι R M) (s : Finset ι) :
    ∃ bs : Module.Basis (Fin s.card) R (Submodule.span R (b '' (s : Set ι))),
      (exteriorPower.ιMulti R s.card (fun i => (bs i : M)) : ExteriorAlgebra R M) =
        b.ExteriorAlgebra s := by
  obtain ⟨bs, hbs⟩ := exists_basis_span_image_coe b s
  refine ⟨bs, ?_⟩
  rw [basis_exteriorAlgebra_eq_coe_ιMulti]
  simp only [hbs]

end Ring

section Field

variable {k : Type*} {V : Type*} [Field k] [AddCommGroup V] [Module k V]

private theorem extend_coord_apply {U : Submodule k V} {d : ℕ} (b : Module.Basis (Fin d) k U)
    {μ : Fin d → V →ₗ[k] k} (hμ : ∀ j, μ j ∘ₗ U.subtype = b.coord j) (r j : Fin d) :
    μ j (b r) = if r = j then 1 else 0 := by
  classical
  have h := LinearMap.congr_fun (hμ j) (b r)
  rw [LinearMap.comp_apply, Submodule.subtype_apply, b.coord_apply, b.repr_self,
    Finsupp.single_apply] at h
  convert h

private theorem det_updateRow_one {n : Type*} [Fintype n] [DecidableEq n] (i : n) (u : n → k) :
    (Matrix.updateRow (1 : Matrix n n k) i u).det = u i := by
  rw [← Matrix.det_transpose, ← Matrix.updateCol_transpose, Matrix.transpose_one,
    ← Matrix.cramer_apply, Matrix.cramer_one]
  rfl

variable {U : Submodule k V} {d : ℕ}

theorem ιMulti_coe_basis_ne_zero (b : Module.Basis (Fin d) k U) :
    exteriorPower.ιMulti k d (fun i => (b i : V)) ≠ 0 := by
  classical
  choose μ hμ using fun j => LinearMap.exists_extend (b.coord j)
  intro h
  have h1 := congrArg (exteriorPower.alternatingMapLinearEquiv
    (Matrix.detRowAlternating.compLinearMap (LinearMap.pi μ))) h
  rw [exteriorPower.alternatingMapLinearEquiv_apply_ιMulti, map_zero,
    AlternatingMap.compLinearMap_apply] at h1
  have hM : (fun s => LinearMap.pi μ (b s : V)) = (1 : Matrix (Fin d) (Fin d) k) := by
    funext s j
    rw [LinearMap.pi_apply, extend_coord_apply b hμ s j, Matrix.one_apply]
  rw [hM] at h1
  exact one_ne_zero (Matrix.det_one.symm.trans h1)

theorem map_le_of_lieMap_ιMulti_coe_basis_mem (b : Module.Basis (Fin d) k U) (f : Module.End k V)
    (h : exteriorPower.lieMap d f (exteriorPower.ιMulti k d (fun i => (b i : V))) ∈
      k ∙ (exteriorPower.ιMulti k d (fun i => (b i : V)))) :
    U.map f ≤ U := by
  classical
  have hspan : Submodule.span k (Set.range fun i => (b i : V)) = U := by
    have h' := congrArg (Submodule.map U.subtype) b.span_eq
    rw [Submodule.map_span, Submodule.map_subtype_top, ← Set.range_comp] at h'
    exact h'
  suffices hb : ∀ r, f (b r : V) ∈ U by
    rw [Submodule.map_le_iff_le_comap]
    calc U = Submodule.span k (Set.range fun i => (b i : V)) := hspan.symm
      _ ≤ U.comap f :=
        Submodule.span_le.mpr (Set.range_subset_iff.mpr fun r => Submodule.mem_comap.mpr (hb r))
  intro r
  by_contra hr
  obtain ⟨l, hl, hUl⟩ := Submodule.exists_le_ker_of_notMem hr
  choose μ hμ using fun j => LinearMap.exists_extend (b.coord j)
  let π : V →ₗ[k] Fin d → k := LinearMap.pi (Function.update μ r l)
  let Φ := exteriorPower.alternatingMapLinearEquiv (Matrix.detRowAlternating.compLinearMap π)
  have hΦ : ∀ v : Fin d → V,
      Φ (exteriorPower.ιMulti k d v) = (Matrix.of fun s j => π (v s) j).det := fun v => by
    simp only [Φ, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
      AlternatingMap.compLinearMap_apply]
    rfl
  have hπ : ∀ s j, π (b s) j = if j = r then 0 else if s = j then 1 else 0 := by
    intro s j
    simp only [π, LinearMap.pi_apply]
    by_cases hj : j = r
    · subst hj
      rw [Function.update_self, if_pos rfl]
      exact LinearMap.mem_ker.mp (hUl (b s).2)
    · rw [Function.update_of_ne hj, if_neg hj]
      exact extend_coord_apply b hμ s j
  have h0 : Φ (exteriorPower.ιMulti k d (fun i => (b i : V))) = 0 := by
    rw [hΦ]
    exact Matrix.det_eq_zero_of_column_eq_zero r fun s => by simp [hπ]
  have h1 : Φ (exteriorPower.lieMap d f (exteriorPower.ιMulti k d (fun i => (b i : V)))) =
      l (f (b r)) := by
    simp only [exteriorPower.lieMap_apply_ιMulti, map_sum, hΦ]
    rw [Finset.sum_eq_single r]
    · rw [← show π (f (b r)) r = l (f (b r)) by simp [π]]
      convert det_updateRow_one r (π (f (b r))) using 2
      ext s j
      by_cases hs : s = r
      · rw [hs]
        simp
      · rw [Matrix.of_apply, Function.update_of_ne hs, Matrix.updateRow_ne hs, hπ,
          Matrix.one_apply]
        rcases eq_or_ne j r with rfl | hj
        · simp [hs]
        · simp [hj]
    · intro s _ hs
      refine Matrix.det_eq_zero_of_row_eq_zero r fun j => ?_
      rw [Matrix.of_apply, Function.update_of_ne (Ne.symm hs), hπ]
      rcases eq_or_ne j r with rfl | hj
      · simp
      · simp [hj, Ne.symm hj]
    · exact fun hr' => absurd (Finset.mem_univ r) hr'
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp h
  apply hl
  rw [← h1, ← hc, map_smul, h0, smul_zero]

theorem lieMap_ιMulti_coe_basis_mem_span_singleton_iff (b : Module.Basis (Fin d) k U)
    (f : Module.End k V) :
    exteriorPower.lieMap d f (exteriorPower.ιMulti k d (fun i => (b i : V))) ∈
        k ∙ (exteriorPower.ιMulti k d (fun i => (b i : V))) ↔ U.map f ≤ U := by
  refine ⟨map_le_of_lieMap_ιMulti_coe_basis_mem b f, fun h => ?_⟩
  rw [lieMap_ιMulti_coe_basis_eq_trace_smul b f fun x hx => h (Submodule.mem_map_of_mem hx)]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

theorem leibniz_coe_ιMulti_basis_mem_span_singleton_iff (b : Module.Basis (Fin d) k U)
    (f : Module.End k V) (D : ExteriorAlgebra k V →ₗ[k] ExteriorAlgebra k V)
    (hι : ∀ m, D (ExteriorAlgebra.ι k m) = ExteriorAlgebra.ι k (f m))
    (hmul : ∀ x y, D (x * y) = D x * y + x * D y) :
    D (exteriorPower.ιMulti k d (fun i => (b i : V)) : ExteriorAlgebra k V) ∈
        k ∙ (exteriorPower.ιMulti k d (fun i => (b i : V)) : ExteriorAlgebra k V) ↔
      U.map f ≤ U := by
  rw [apply_coe_of_leibniz f D hι hmul, ← lieMap_ιMulti_coe_basis_mem_span_singleton_iff b f,
    Submodule.mem_span_singleton, Submodule.mem_span_singleton]
  refine exists_congr fun c => ?_
  rw [← Submodule.coe_smul, SetLike.coe_eq_coe]

theorem exists_coe_eq_basis_exteriorAlgebra {ι : Type*} [LinearOrder ι] (b : Module.Basis ι k V)
    (s : Finset ι) :
    ∃ w : ⋀[k]^s.card V, (w : ExteriorAlgebra k V) = b.ExteriorAlgebra s ∧ w ≠ 0 ∧
      ∀ f : Module.End k V, exteriorPower.lieMap s.card f w ∈ k ∙ w ↔
        (Submodule.span k (b '' (s : Set ι))).map f ≤ Submodule.span k (b '' (s : Set ι)) := by
  obtain ⟨bs, hbs⟩ := exists_coe_ιMulti_basis_eq_basis_exteriorAlgebra b s
  exact ⟨_, hbs, ιMulti_coe_basis_ne_zero bs, lieMap_ιMulti_coe_basis_mem_span_singleton_iff bs⟩

theorem leibniz_basis_exteriorAlgebra_mem_span_singleton_iff {ι : Type*} [LinearOrder ι]
    (b : Module.Basis ι k V) (s : Finset ι) (f : Module.End k V)
    (D : ExteriorAlgebra k V →ₗ[k] ExteriorAlgebra k V)
    (hι : ∀ m, D (ExteriorAlgebra.ι k m) = ExteriorAlgebra.ι k (f m))
    (hmul : ∀ x y, D (x * y) = D x * y + x * D y) :
    D (b.ExteriorAlgebra s) ∈ k ∙ (b.ExteriorAlgebra s) ↔
      (Submodule.span k (b '' (s : Set ι))).map f ≤ Submodule.span k (b '' (s : Set ι)) := by
  obtain ⟨bs, hbs⟩ := exists_coe_ιMulti_basis_eq_basis_exteriorAlgebra b s
  rw [← hbs]
  exact leibniz_coe_ιMulti_basis_mem_span_singleton_iff bs f D hι hmul

end Field

end CFSG.LinearAlgebra
