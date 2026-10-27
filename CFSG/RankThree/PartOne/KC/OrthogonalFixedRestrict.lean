module

public import CFSG.RankThree.PartOne.KC.OrthogonalFixedBlock
public import CFSG.RankThree.PartOne.KC.OrthogonalPairedBlock

public section

namespace CFSG.RankThree.PartOne.KCOrthogonal

open Polynomial Module CFSG.RankThree.PartOne.KCPrimary

section Rank

variable {K : Type*} [Field K]

theorem finrank_range_eq_of_adjoint {M N : Type*} [AddCommGroup M] [Module K M]
    [FiniteDimensional K M] [AddCommGroup N] [Module K N] (P : M →ₗ[K] N →ₗ[K] K)
    (hP : Function.Bijective P.flip) (f : M →ₗ[K] M) (f' : N →ₗ[K] N)
    (h : ∀ u w, P (f u) w = P u (f' w)) :
    finrank K (LinearMap.range f') = finrank K (LinearMap.range f) := by
  let Φ : N ≃ₗ[K] Module.Dual K M := LinearEquiv.ofBijective P.flip hP
  have hΦ : ∀ w, Φ (f' w) = f.dualMap (Φ w) := fun w => LinearMap.ext fun u => (h u w).symm
  have hmap : (LinearMap.range f').map (Φ : N →ₗ[K] Module.Dual K M) =
      LinearMap.range f.dualMap := by
    ext φ
    simp only [Submodule.mem_map, LinearMap.mem_range, LinearEquiv.coe_coe]
    constructor
    · rintro ⟨_, ⟨w, rfl⟩, rfl⟩
      exact ⟨Φ w, (hΦ w).symm⟩
    · rintro ⟨ψ, rfl⟩
      refine ⟨f' (Φ.symm ψ), ⟨Φ.symm ψ, rfl⟩, ?_⟩
      rw [hΦ, Φ.apply_symm_apply]
  rw [← LinearEquiv.finrank_map_eq Φ (LinearMap.range f'), hmap,
    LinearMap.finrank_range_dualMap_eq_finrank_range]

variable {V : Type*} [AddCommGroup V] [Module K V]

theorem finrank_range_restrict {p q : Submodule K V} (f : V →ₗ[K] V)
    (hf : ∀ x ∈ p, f x ∈ q) :
    finrank K (LinearMap.range (f.restrict hf)) = finrank K (p.map f) := by
  have : (LinearMap.range (f.restrict hf)).map q.subtype = p.map f := by
    ext y
    simp only [Submodule.mem_map, LinearMap.mem_range, Submodule.subtype_apply]
    constructor
    · rintro ⟨_, ⟨u, rfl⟩, rfl⟩
      exact ⟨u, u.2, rfl⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨_, ⟨⟨u, hu⟩, rfl⟩, rfl⟩
  rw [← this, Submodule.finrank_map_subtype_eq]

end Rank

section Fixed

variable {K : Type*} {V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

omit [FiniteDimensional K V] in
theorem polar_comp_subtype (U : Submodule K V) (u w : U) :
    QuadraticMap.polar (Q.comp U.subtype) u w = QuadraticMap.polar Q (u : V) (w : V) := by
  simp only [QuadraticMap.polar, QuadraticMap.comp_apply, map_add]
  rfl

theorem OddOrderIsometry.polarBilin_fixed_nondegenerate (hx : OddOrderIsometry Q p x) :
    (QuadraticMap.polarBilin (Q.comp (fixedSpace x).subtype)).Nondegenerate := by
  have key : ∀ u : fixedSpace x, (∀ w : fixedSpace x, QuadraticMap.polar Q (u : V) (w : V) = 0) →
      u = 0 := by
    intro u hu
    refine Subtype.ext (hx.regular _ fun v => ?_)
    obtain ⟨w, hw, r, hr, rfl⟩ := exists_add_of_isCompl hx.fixed_others.1 v
    rw [QuadraticMap.polar_add_right, hu ⟨w, hw⟩, hx.fixed_others.2 u u.2 r hr, add_zero]
  refine ⟨fun u hu => key u fun w => ?_, fun u hu => key u fun w => ?_⟩
  · have := hu w
    rwa [QuadraticMap.polarBilin_apply_apply, polar_comp_subtype] at this
  · have := hu w
    rwa [QuadraticMap.polarBilin_apply_apply, polar_comp_subtype, QuadraticMap.polar_comm] at this

@[expose] noncomputable def isometryRestrictFixed (Q : QuadraticForm K V) (x : V ≃ₗ[K] V) :
    ↥(isometryCentralizer Q x) →* (fixedSpace x ≃ₗ[K] fixedSpace x) where
  toFun g := restrictEquiv (fixedSpace x) g.1
    (fun _ hw => mem_fixedSpace_of_apply (Subgroup.mem_inf.mp g.2).2 hw)
    (fun _ hw => mem_fixedSpace_of_apply (symm_mem_centralizer x (Subgroup.mem_inf.mp g.2).2) hw)
  map_one' := LinearEquiv.ext fun _ => Subtype.ext rfl
  map_mul' _ _ := LinearEquiv.ext fun _ => Subtype.ext rfl

omit [FiniteDimensional K V] in
theorem coe_isometryRestrictFixed (g : ↥(isometryCentralizer Q x)) (w : fixedSpace x) :
    (isometryRestrictFixed Q x g w : V) = g.1 (w : V) := rfl

omit [FiniteDimensional K V] in
theorem isometryRestrictFixed_mem_orthogonalGroup (g : ↥(isometryCentralizer Q x)) :
    isometryRestrictFixed Q x g ∈
      TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace x).subtype) := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro w
  have h := (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp (Subgroup.mem_inf.mp g.2).1) (w : V)
  show Q ((isometryRestrictFixed Q x g w : fixedSpace x) : V) = Q (w : V)
  rw [coe_isometryRestrictFixed]
  exact h

omit [FiniteDimensional K V] in
theorem isometryRestrictFixed_restrictFixed (g : ↥(supportedBlock Q x (X - 1))) :
    isometryRestrictFixed Q x ⟨g.1, supportedBlock_le_isometryCentralizer _ g.2⟩ =
      restrictFixed Q x g := rfl

end Fixed

end CFSG.RankThree.PartOne.KCOrthogonal
