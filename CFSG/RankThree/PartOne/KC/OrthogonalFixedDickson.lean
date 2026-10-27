module

public import CFSG.RankThree.PartOne.KC.OrthogonalFixedRestrict
public import CFSG.RankThree.OrthogonalInvolutions.Dickson
public import CFSG.RankThree.PartOne.KC.OrthogonalSelfDualBlock

public section

namespace CFSG.RankThree.PartOne.KCOrthogonal

open Polynomial Module CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.OrthogonalInvolutions

section Orbit

variable {K : Type*} {V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

omit [FiniteDimensional K V] in
theorem finrank_map_symm_sub_one (g : V ≃ₗ[K] V) (U : Submodule K V) :
    finrank K (U.map ((g.symm : V →ₗ[K] V) - 1)) = finrank K (U.map ((g : V →ₗ[K] V) - 1)) := by
  have : U.map ((g.symm : V →ₗ[K] V) - 1) = (U.map ((g : V →ₗ[K] V) - 1)).map
      ((g.symm.trans (LinearEquiv.neg K) : V ≃ₗ[K] V) : V →ₗ[K] V) := by
    ext y
    simp only [Submodule.mem_map, LinearMap.sub_apply, LinearEquiv.coe_coe, Module.End.one_apply,
      LinearEquiv.trans_apply, LinearEquiv.neg_apply]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨g w - w, ⟨w, hw, rfl⟩, by simp⟩
    · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
      exact ⟨w, hw, by simp⟩
  rw [this, LinearEquiv.finrank_map_eq]

theorem OddOrderIsometry.finrank_map_sub_one_orbit (hx : OddOrderIsometry Q p x) {h : K[X]}
    (hh : h ∈ primaryFactors x.toLinearMap) {g : V ≃ₗ[K] V} (hg : g ∈ isometryCentralizer Q x) :
    finrank K ((primaryComponent x.toLinearMap h).map ((g : V →ₗ[K] V) - 1)) =
      finrank K ((primaryComponent x.toLinearMap (reciprocalPolynomial h)).map
        ((g : V →ₗ[K] V) - 1)) := by
  have hgO := (Subgroup.mem_inf.mp hg).1
  have hgc := (Subgroup.mem_inf.mp hg).2
  have hgc' := symm_mem_centralizer x hgc
  have hmaps : ∀ v ∈ primaryComponent x.toLinearMap h, ((g : V →ₗ[K] V) - 1) v ∈
      primaryComponent x.toLinearMap h := fun v hv =>
    Submodule.sub_mem _ (apply_mem_primaryComponent_of_mem_centralizer hgc hv) hv
  have hmaps' : ∀ v ∈ primaryComponent x.toLinearMap (reciprocalPolynomial h),
      ((g.symm : V →ₗ[K] V) - 1) v ∈ primaryComponent x.toLinearMap (reciprocalPolynomial h) :=
    fun v hv => Submodule.sub_mem _ (apply_mem_primaryComponent_of_mem_centralizer hgc' hv) hv
  have hadj : ∀ (u : primaryComponent x.toLinearMap h)
      (w : primaryComponent x.toLinearMap (reciprocalPolynomial h)),
      pairingHom Q x h (((g : V →ₗ[K] V) - 1).restrict hmaps u) w =
        pairingHom Q x h u (((g.symm : V →ₗ[K] V) - 1).restrict hmaps' w) := by
    intro u w
    simp only [pairingHom_apply, LinearMap.coe_restrict_apply, LinearMap.sub_apply,
      LinearEquiv.coe_coe, Module.End.one_apply, QuadraticMap.polar_sub_left,
      QuadraticMap.polar_sub_right]
    have := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hgO (u : V) (g.symm (w : V))
    rw [g.apply_symm_apply] at this
    rw [this]
  have h1 := finrank_range_eq_of_adjoint (pairingHom Q x h) (hx.pairing_flip_bijective hh) _ _ hadj
  rw [finrank_range_restrict, finrank_range_restrict, finrank_map_symm_sub_one] at h1
  exact h1.symm

end Orbit

section SelfDual

variable {K : Type*} {V : Type*} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

theorem OddOrderIsometry.even_finrank_map_sub_one_selfDual (hx : OddOrderIsometry Q p x)
    (hp2 : Odd p) {h : K[X]} (hh : h ∈ primaryFactors x.toLinearMap) (hne1 : h ≠ X - 1)
    (hself : h = reciprocalPolynomial h) {g : V ≃ₗ[K] V}
    (hgc : g ∈ Subgroup.centralizer ({x} : Set (V ≃ₗ[K] V))) :
    Even (finrank K ((primaryComponent x.toLinearMap h).map ((g : V →ₗ[K] V) - 1))) := by
  have hirr := irreducible_of_mem_primaryFactors hh
  have : Fact (Irreducible h) := ⟨hirr⟩
  obtain ⟨d, H, hdeg, -⟩ := hx.exists_selfDual_hermitian hp2 hh hne1 hself
  let γ : Module.End (AdjoinRoot h) (primaryComponent x.toLinearMap h) :=
    ((centralizerGL x h ⟨g, hgc⟩ : BlockGL x h) :
      Module.End (AdjoinRoot h) (primaryComponent x.toLinearMap h))
  have hγ : ∀ v : primaryComponent x.toLinearMap h, ((γ v : primaryComponent x.toLinearMap h) : V) =
      g (v : V) := fun v => coe_centralizerGL x h ⟨g, hgc⟩ v
  let U : Submodule (AdjoinRoot h) (primaryComponent x.toLinearMap h) := LinearMap.range (γ - 1)
  have hmap : (primaryComponent x.toLinearMap h).map ((g : V →ₗ[K] V) - 1) =
      (U.restrictScalars K).map (primaryComponent x.toLinearMap h).subtype := by
    ext y
    simp only [Submodule.mem_map, LinearMap.sub_apply, LinearEquiv.coe_coe, Module.End.one_apply,
      Submodule.subtype_apply]
    constructor
    · rintro ⟨v, hv, rfl⟩
      refine ⟨(γ - 1) ⟨v, hv⟩, ⟨⟨v, hv⟩, rfl⟩, ?_⟩
      simp only [LinearMap.sub_apply, Module.End.one_apply, Submodule.coe_sub, hγ]
    · rintro ⟨_, ⟨v, rfl⟩, rfl⟩
      refine ⟨(v : V), v.2, ?_⟩
      simp only [LinearMap.sub_apply, Module.End.one_apply, Submodule.coe_sub, hγ]
  rw [hmap, Submodule.finrank_map_subtype_eq,
    LinearEquiv.finrank_eq
      ((Submodule.restrictScalarsEquiv K (AdjoinRoot h) _ U).restrictScalars K),
    ← Module.finrank_mul_finrank K (AdjoinRoot h) U,
    (AdjoinRoot.powerBasis hirr.ne_zero).finrank, AdjoinRoot.powerBasis_dim, hdeg]
  exact (even_two_mul d).mul_right _

end SelfDual

section Block

variable {K : Type*} {V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

theorem disjoint_primaryComponent_of_ne (hx : OddOrderIsometry Q p x) {a b : K[X]}
    (ha : a ∈ primaryFactors x.toLinearMap) (hb : b ∈ primaryFactors x.toLinearMap) (hab : a ≠ b) :
    Disjoint (primaryComponent x.toLinearMap a) (primaryComponent x.toLinearMap b) := by
  classical
  rw [disjoint_iff_inf_le]
  intro v hv
  obtain ⟨hva, hvb⟩ := Submodule.mem_inf.mp hv
  have h1 := primaryProjection_of_mem hx.squarefree_minpoly ha hva
  have h2 := primaryProjection_of_mem_ne hx.squarefree_minpoly ha hb (Ne.symm hab) hvb
  rw [h1] at h2
  exact (Submodule.mem_bot K).mpr h2

theorem OddOrderIsometry.commSpace_eq_map_orbit (hx : OddOrderIsometry Q p x) {r : K[X]}
    (hr : r ∈ primaryFactors x.toLinearMap) {g : V ≃ₗ[K] V} (hg : g ∈ supportedBlock Q x r) :
    commSpace g = (orbitSpace x.toLinearMap r).map ((g : V →ₗ[K] V) - 1) := by
  ext y
  rw [Submodule.mem_map]
  constructor
  · intro hy
    obtain ⟨v, rfl⟩ := mem_commSpace.mp hy
    obtain ⟨u, hu, o, ho, rfl⟩ := exists_add_of_isCompl (hx.isCompl_orbit_others hr) v
    refine ⟨u, hu, ?_⟩
    have := (mem_supportedBlock.mp hg).2 o ho
    simp only [LinearMap.sub_apply, LinearEquiv.coe_coe, Module.End.one_apply, map_add, this]
    abel
  · rintro ⟨u, -, rfl⟩
    exact sub_mem_commSpace g u

end Block

section Main

variable {K : Type*} {V : Type*} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

theorem OddOrderIsometry.even_finrank_commSpace_of_mem_supportedBlock (hx : OddOrderIsometry Q p x)
    (hp2 : Odd p) {r : K[X]} (hr : r ∈ primaryFactors x.toLinearMap) (hne1 : r ≠ X - 1)
    {g : V ≃ₗ[K] V} (hg : g ∈ supportedBlock Q x r) : Even (finrank K (commSpace g)) := by
  have hgc := supportedBlock_le_centralizer r hg
  have hgM := supportedBlock_le_isometryCentralizer r hg
  rw [hx.commSpace_eq_map_orbit hr hg, orbitSpace, Submodule.map_sup]
  by_cases hself : r = reciprocalPolynomial r
  · rw [← hself, sup_idem]
    exact hx.even_finrank_map_sub_one_selfDual hp2 hr hne1 hself hgc
  · have hr' := hx.reciprocalPolynomial_mem hr
    have hdisj := disjoint_primaryComponent_of_ne hx hr hr' hself
    have hle : ∀ {a : K[X]}, (a ∈ primaryFactors x.toLinearMap) →
        (primaryComponent x.toLinearMap a).map ((g : V →ₗ[K] V) - 1) ≤
          primaryComponent x.toLinearMap a := by
      intro a _ y hy
      obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.mp hy
      exact Submodule.sub_mem _ (apply_mem_primaryComponent_of_mem_centralizer hgc hv) hv
    have hbot : (primaryComponent x.toLinearMap r).map ((g : V →ₗ[K] V) - 1) ⊓
        (primaryComponent x.toLinearMap (reciprocalPolynomial r)).map
          ((g : V →ₗ[K] V) - 1) = ⊥ :=
      disjoint_iff.mp (hdisj.mono (hle hr) (hle hr'))
    have hsum := Submodule.finrank_sup_add_finrank_inf_eq
      ((primaryComponent x.toLinearMap r).map ((g : V →ₗ[K] V) - 1))
      ((primaryComponent x.toLinearMap (reciprocalPolynomial r)).map ((g : V →ₗ[K] V) - 1))
    rw [hbot, finrank_bot, add_zero, ← hx.finrank_map_sub_one_orbit hr hgM] at hsum
    rw [hsum]
    exact ⟨_, rfl⟩

omit [Finite K] in
theorem OddOrderIsometry.finrank_commSpace_eq_restrictFixed (hx : OddOrderIsometry Q p x)
    {g : V ≃ₗ[K] V} (hg : g ∈ supportedBlock Q x (X - 1)) :
    finrank K (commSpace g) = finrank K (commSpace (restrictFixed Q x ⟨g, hg⟩)) := by
  have hmap : commSpace g =
      (commSpace (restrictFixed Q x ⟨g, hg⟩)).map (fixedSpace x).subtype := by
    ext y
    rw [Submodule.mem_map]
    constructor
    · intro hy
      obtain ⟨v, rfl⟩ := mem_commSpace.mp hy
      obtain ⟨w, hw, o, ho, rfl⟩ := exists_add_of_isCompl hx.fixed_others.1 v
      have := (mem_supportedBlock.mp hg).2 o ho
      refine ⟨restrictFixed Q x ⟨g, hg⟩ ⟨w, hw⟩ - ⟨w, hw⟩, sub_mem_commSpace _ _, ?_⟩
      simp only [Submodule.subtype_apply, Submodule.coe_sub, coe_restrictFixed, map_add, this]
      abel
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨u, rfl⟩ := mem_commSpace.mp hz
      exact sub_mem_commSpace g (u : V)
  rw [hmap, Submodule.finrank_map_subtype_eq]

theorem OddOrderIsometry.dicksonHom_eq_restrict_of_mem_supportedBlock (hx : OddOrderIsometry Q p x)
    (hp2 : Odd p) (hQ : Q.polarBilin.Nondegenerate) {r : K[X]}
    (hr : r ∈ primaryFactors x.toLinearMap) {g : V ≃ₗ[K] V} (hg : g ∈ supportedBlock Q x r) :
    dicksonHom Q hQ ⟨g, (Subgroup.mem_inf.mp (supportedBlock_le_isometryCentralizer r hg)).1⟩ =
      dicksonHom (Q.comp (fixedSpace x).subtype) hx.polarBilin_fixed_nondegenerate
        ⟨isometryRestrictFixed Q x ⟨g, supportedBlock_le_isometryCentralizer r hg⟩,
          isometryRestrictFixed_mem_orthogonalGroup _⟩ := by
  by_cases hne1 : r = X - 1
  · subst hne1
    rw [dicksonHom_apply, dicksonHom_apply]
    congr 2
    exact hx.finrank_commSpace_eq_restrictFixed hg
  · have hev := hx.even_finrank_commSpace_of_mem_supportedBlock hp2 hr hne1 hg
    have hfix : ∀ w ∈ fixedSpace x, g w = w := by
      by_cases hX : (X - 1 : K[X]) ∈ primaryFactors x.toLinearMap
      · intro w hw
        rw [fixedSpace_eq_primaryComponent] at hw
        refine apply_eq_of_mem_supportedBlock hg hX (Ne.symm hne1) (fun heq => hne1 ?_) hw
        rw [← hx.reciprocal_reciprocal_eq hr, ← heq, reciprocalPolynomial_X_sub_one]
      · intro w hw
        rw [fixedSpace_eq_bot_of_not_mem hX, Submodule.mem_bot] at hw
        rw [hw, map_zero]
    have h1 : (⟨isometryRestrictFixed Q x ⟨g, supportedBlock_le_isometryCentralizer r hg⟩,
        isometryRestrictFixed_mem_orthogonalGroup _⟩ :
          ↥(TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace x).subtype))) = 1 :=
      Subtype.ext (LinearEquiv.ext fun w => Subtype.ext (hfix w w.2))
    rw [h1, map_one, dicksonHom_apply, ← ofAdd_zero, Multiplicative.ofAdd.injective.eq_iff]
    exact ZMod.natCast_eq_zero_iff_even.mpr hev

@[expose] noncomputable def dicksonCentralizer (Q : QuadraticForm K V) (x : V ≃ₗ[K] V)
    (hQ : Q.polarBilin.Nondegenerate) : ↥(isometryCentralizer Q x) →* Multiplicative (ZMod 2) :=
  (dicksonHom Q hQ).comp
    (Subgroup.inclusion (fun _ hg => (Subgroup.mem_inf.mp hg).1 :
      isometryCentralizer Q x ≤ TauCeti.QuadraticMap.orthogonalGroup Q))

@[expose] noncomputable def dicksonFixed (hx : OddOrderIsometry Q p x) :
    ↥(isometryCentralizer Q x) →* Multiplicative (ZMod 2) :=
  (dicksonHom (Q.comp (fixedSpace x).subtype) hx.polarBilin_fixed_nondegenerate).comp
    ((isometryRestrictFixed Q x).codRestrict _
      (fun g => isometryRestrictFixed_mem_orthogonalGroup g))

theorem OddOrderIsometry.dicksonCentralizer_eq_dicksonFixed (hx : OddOrderIsometry Q p x)
    (hp2 : Odd p) (hQ : Q.polarBilin.Nondegenerate) {Rep : Finset K[X]}
    (hRep : IsOrbitRepresentatives x Rep) :
    dicksonCentralizer Q x hQ = dicksonFixed hx := by
  classical
  ext ⟨m, hm⟩
  have hle := hx.isometryCentralizer_le hRep hm
  have hstep : ∀ g g' : V ≃ₗ[K] V, (∃ hgM : g ∈ isometryCentralizer Q x,
      dicksonCentralizer Q x hQ ⟨g, hgM⟩ = dicksonFixed hx ⟨g, hgM⟩) →
      (∃ hgM : g' ∈ isometryCentralizer Q x,
      dicksonCentralizer Q x hQ ⟨g', hgM⟩ = dicksonFixed hx ⟨g', hgM⟩) →
      ∃ hgM : g * g' ∈ isometryCentralizer Q x,
      dicksonCentralizer Q x hQ ⟨g * g', hgM⟩ = dicksonFixed hx ⟨g * g', hgM⟩ := by
    rintro g g' ⟨hgM, hgeq⟩ ⟨hgM', hgeq'⟩
    refine ⟨mul_mem hgM hgM', ?_⟩
    have e2 : (⟨g * g', mul_mem hgM hgM'⟩ : ↥(isometryCentralizer Q x)) =
        ⟨g, hgM⟩ * ⟨g', hgM'⟩ := rfl
    rw [e2, map_mul, map_mul, hgeq, hgeq']
  have hone : ∃ hgM : (1 : V ≃ₗ[K] V) ∈ isometryCentralizer Q x,
      dicksonCentralizer Q x hQ ⟨1, hgM⟩ = dicksonFixed hx ⟨1, hgM⟩ :=
    ⟨one_mem _, by
      change dicksonCentralizer Q x hQ 1 = dicksonFixed hx 1
      rw [map_one, map_one]⟩
  refine (Subgroup.iSup_induction (fun r => ⨆ (_ : r ∈ Rep), supportedBlock Q x r)
    (C := fun g => ∃ hgM : g ∈ isometryCentralizer Q x,
      dicksonCentralizer Q x hQ ⟨g, hgM⟩ = dicksonFixed hx ⟨g, hgM⟩)
    hle (fun r g hg => ?_) hone hstep).elim fun hgM h => ?_
  · refine Subgroup.iSup_induction (fun _ : r ∈ Rep => supportedBlock Q x r)
      (C := fun g => ∃ hgM : g ∈ isometryCentralizer Q x,
        dicksonCentralizer Q x hQ ⟨g, hgM⟩ = dicksonFixed hx ⟨g, hgM⟩)
      hg (fun hr g hg => ?_) hone hstep
    exact ⟨supportedBlock_le_isometryCentralizer r hg,
      hx.dicksonHom_eq_restrict_of_mem_supportedBlock hp2 hQ (hRep.1 hr) hg⟩
  · exact h

end Main

end CFSG.RankThree.PartOne.KCOrthogonal
