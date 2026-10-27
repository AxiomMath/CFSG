module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.RankThree.PartOne.KC.OrthogonalPrimaryPairing

public section

namespace CFSG.RankThree.PartOne.KCOrthogonal

open Polynomial Module CFSG.RankThree.PartOne.KCPrimary

section Units

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (x : V ≃ₗ[K] V)

theorem mem_centralizer_iff {g : V ≃ₗ[K] V} :
    g ∈ Subgroup.centralizer ({x} : Set (V ≃ₗ[K] V)) ↔ ∀ v, g (x v) = x (g v) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h v
    have := congrArg (fun f : V ≃ₗ[K] V => f v) h
    exact this
  · intro h
    ext v
    exact h v

theorem commute_toLinearMap_of_mem_centralizer {g : V ≃ₗ[K] V}
    (hg : g ∈ Subgroup.centralizer ({x} : Set (V ≃ₗ[K] V))) :
    Commute g.toLinearMap x.toLinearMap := by
  have h := (mem_centralizer_iff x).mp hg
  ext v
  exact h v

theorem symm_mem_centralizer {g : V ≃ₗ[K] V}
    (hg : g ∈ Subgroup.centralizer ({x} : Set (V ≃ₗ[K] V))) :
    g.symm ∈ Subgroup.centralizer ({x} : Set (V ≃ₗ[K] V)) := by
  have h := (mem_centralizer_iff x).mp hg
  rw [mem_centralizer_iff]
  intro v
  apply g.injective
  rw [g.apply_symm_apply, h, g.apply_symm_apply]

@[expose] noncomputable def unitToEquiv (u : (commutant x.toLinearMap)ˣ) : V ≃ₗ[K] V :=
  LinearEquiv.ofLinearMap (u : commutant x.toLinearMap).1
    ((u⁻¹ : (commutant x.toLinearMap)ˣ) : commutant x.toLinearMap).1
    (congrArg Subtype.val u.mul_inv) (congrArg Subtype.val u.inv_mul)

theorem unitToEquiv_apply (u : (commutant x.toLinearMap)ˣ) (v : V) :
    unitToEquiv x u v = (u : commutant x.toLinearMap).1 v := rfl

@[expose] noncomputable def centralizerUnits :
    (Subgroup.centralizer ({x} : Set (V ≃ₗ[K] V)) : Subgroup (V ≃ₗ[K] V)) ≃*
      (commutant x.toLinearMap)ˣ where
  toFun g := ⟨⟨g.1.toLinearMap,
    (mem_commutant _).mpr (commute_toLinearMap_of_mem_centralizer x g.2)⟩,
    ⟨g.1.symm.toLinearMap, (mem_commutant _).mpr
      (commute_toLinearMap_of_mem_centralizer x (symm_mem_centralizer x g.2))⟩,
    Subtype.ext (LinearMap.ext fun v => g.1.apply_symm_apply v),
    Subtype.ext (LinearMap.ext fun v => g.1.symm_apply_apply v)⟩
  invFun u := ⟨unitToEquiv x u, by
    rw [mem_centralizer_iff]
    intro v
    have h := (mem_commutant x.toLinearMap).mp (u : commutant x.toLinearMap).2
    have := congrArg (fun f : Module.End K V => f v) h.eq
    exact this⟩
  left_inv g := Subtype.ext (LinearEquiv.ext fun v => rfl)
  right_inv u := Units.ext (Subtype.ext (LinearMap.ext fun v => rfl))
  map_mul' g h := Units.ext (Subtype.ext (LinearMap.ext fun v => rfl))

section Theta

variable [FiniteDimensional K V]

@[expose] noncomputable def theta (hsq : Squarefree (minpoly K x.toLinearMap)) :
    (Subgroup.centralizer ({x} : Set (V ≃ₗ[K] V)) : Subgroup (V ≃ₗ[K] V)) ≃*
      ((a : primaryFactors x.toLinearMap) →
        LinearMap.GeneralLinearGroup (AdjoinRoot (a : K[X])) (primaryComponent x.toLinearMap a)) :=
  (centralizerUnits x).trans (commutantUnitsEquivPi hsq)

theorem coe_theta_apply (hsq : Squarefree (minpoly K x.toLinearMap))
    (g : (Subgroup.centralizer ({x} : Set (V ≃ₗ[K] V)) : Subgroup (V ≃ₗ[K] V)))
    (a : primaryFactors x.toLinearMap) (v : primaryComponent x.toLinearMap a) :
    ((theta x hsq g a : Module.End (AdjoinRoot (a : K[X])) (primaryComponent x.toLinearMap a)) v :
      V) = g.1 (v : V) := rfl

end Theta

end Units

section Basics

variable {K : Type*} [Field K]

theorem irreducible_X_sub_one : Irreducible (X - 1 : K[X]) := by
  simpa using Polynomial.irreducible_X_sub_C (1 : K)

theorem monic_X_sub_one : (X - 1 : K[X]).Monic := by
  simpa using monic_X_sub_C (1 : K)

theorem coeff_zero_X_sub_one : (X - 1 : K[X]).coeff 0 = -1 := by
  simp [coeff_sub, coeff_X, coeff_one]

theorem reciprocalPolynomial_X_sub_one : reciprocalPolynomial (X - 1 : K[X]) = X - 1 := by
  have hX : (X : K[X]).reverse = 1 := by
    have := reverse_mul_X (1 : K[X])
    rw [one_mul] at this
    rw [this, show (1 : K[X]) = C 1 from C_1.symm, reverse_C]
  have h1 : (X - 1 : K[X]).reverse = 1 - X := by
    rw [show (X - 1 : K[X]) = X + C (-1) by simp [sub_eq_add_neg], reverse_add_C]
    simp [sub_eq_add_neg, hX]
  rw [reciprocalPolynomial, h1, coeff_zero_X_sub_one]
  simp [neg_sub]

end Basics

section GeomSum

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

theorem OddOrderIsometry.sum_pow_eq_zero (hx : OddOrderIsometry Q p x) {k : K[X]}
    (hk : k ∈ primaryFactors x.toLinearMap) (hk1 : k ≠ X - 1) {v : V}
    (hv : v ∈ primaryComponent x.toLinearMap k) :
    ∑ i ∈ Finset.range p, (x.toLinearMap ^ i) v = 0 := by
  have hdvd := hx.dvd_X_pow_sub_one hk
  have hirr := irreducible_of_mem_primaryFactors hk
  have hmon := (mem_primaryFactors.mp hk).2.1
  have hfac : (X ^ p - 1 : K[X]) = (∑ i ∈ Finset.range p, X ^ i) * (X - 1) :=
    (geom_sum_mul (X : K[X]) p).symm
  rw [hfac] at hdvd
  have hnd : ¬ k ∣ (X - 1 : K[X]) := fun hd =>
    hk1 (eq_of_monic_of_associated hmon monic_X_sub_one
      (hirr.associated_of_dvd irreducible_X_sub_one hd))
  have hdvd' : k ∣ ∑ i ∈ Finset.range p, (X : K[X]) ^ i :=
    ((hirr.prime).dvd_or_dvd hdvd).resolve_right hnd
  obtain ⟨g, hg⟩ := hdvd'
  have h1 : aeval x.toLinearMap (∑ i ∈ Finset.range p, (X : K[X]) ^ i) v = 0 := by
    rw [hg, mul_comm, map_mul, Module.End.mul_apply, mem_primaryComponent.mp hv, map_zero]
  simpa [map_sum, aeval_X_pow] using h1

omit [FiniteDimensional K V] in
theorem mem_orbitSpace_of_apply {h : K[X]}
    {g : V ≃ₗ[K] V} (hg : g ∈ Subgroup.centralizer ({x} : Set (V ≃ₗ[K] V))) {u : V}
    (hu : u ∈ orbitSpace x.toLinearMap h) : g u ∈ orbitSpace x.toLinearMap h := by
  have hc := commute_toLinearMap_of_mem_centralizer x hg
  obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := Submodule.mem_sup.mp hu
  rw [map_add]
  exact Submodule.add_mem_sup (apply_mem_primaryComponent hc hu₁)
    (apply_mem_primaryComponent hc hu₂)

theorem OddOrderIsometry.sum_pow_eq_zero_orbit (hx : OddOrderIsometry Q p x) {h : K[X]}
    (hh : h ∈ primaryFactors x.toLinearMap) (hne1 : h ≠ X - 1) {u : V}
    (hu : u ∈ orbitSpace x.toLinearMap h) :
    ∑ i ∈ Finset.range p, (x.toLinearMap ^ i) u = 0 := by
  have hh' := hx.reciprocalPolynomial_mem hh
  have hne1' : reciprocalPolynomial h ≠ X - 1 := fun heq => hne1 (by
    rw [← hx.reciprocal_reciprocal_eq hh, heq, reciprocalPolynomial_X_sub_one])
  obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := Submodule.mem_sup.mp hu
  simp only [map_add, Finset.sum_add_distrib]
  rw [hx.sum_pow_eq_zero hh hne1 hu₁, hx.sum_pow_eq_zero hh' hne1' hu₂, add_zero]

theorem OddOrderIsometry.quadratic_eq_of_polar_eq (hx : OddOrderIsometry Q p x) {h : K[X]}
    (hh : h ∈ primaryFactors x.toLinearMap) (hne1 : h ≠ X - 1) {T : V ≃ₗ[K] V}
    (hT : T ∈ Subgroup.centralizer ({x} : Set (V ≃ₗ[K] V)))
    (hpol : ∀ u ∈ orbitSpace x.toLinearMap h, ∀ u' ∈ orbitSpace x.toLinearMap h,
      QuadraticMap.polar Q (T u) (T u') = QuadraticMap.polar Q u u') {u : V}
    (hu : u ∈ orbitSpace x.toLinearMap h) : Q (T u) = Q u := by
  have hxQ : ∀ v, Q (x v) = Q v := fun v =>
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hx.mem v
  have hTx := (mem_centralizer_iff x).mp hT
  set U := orbitSpace x.toLinearMap h with hU
  have hxU : ∀ w ∈ U, x w ∈ U := fun w hw => mem_orbitSpace_of_apply
    ((Subgroup.mem_centralizer_singleton_iff).mpr rfl) hw
  have hpow : ∀ (i : ℕ) (w : V), (x.toLinearMap ^ i) w = (x ^ i) w := fun i w => by
    rw [← toLinearMap_pow]; rfl
  have hxQi : ∀ (i : ℕ) (w : V), Q ((x.toLinearMap ^ i) w) = Q w := fun i w => by
    rw [hpow]
    exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp (pow_mem hx.mem i) w
  have hTpow : ∀ (i : ℕ) (w : V), T ((x.toLinearMap ^ i) w) = (x.toLinearMap ^ i) (T w) := by
    intro i
    induction i with
    | zero => intro w; rfl
    | succ i ih =>
      intro w
      rw [pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih]
      congr 1
      exact hTx w
  have hmemU : ∀ i : ℕ, (x.toLinearMap ^ i) u ∈ U := by
    intro i
    induction i with
    | zero => simpa using hu
    | succ i ih =>
      rw [pow_succ', Module.End.mul_apply]
      exact hxU _ ih
  let D : U →+ K := AddMonoidHom.mk' (fun w : U => Q (T (w : V)) - Q (w : V)) fun w w' => by
    have h1 := QuadraticMap.map_add (⇑Q) (T (w : V)) (T (w' : V))
    have h2 := QuadraticMap.map_add (⇑Q) (w : V) (w' : V)
    have h3 := hpol _ w.2 _ w'.2
    simp only [Submodule.coe_add, map_add]
    rw [h1, h2, h3]
    ring
  have hD : ∀ i : ℕ, D ⟨(x.toLinearMap ^ i) u, hmemU i⟩ = D ⟨u, hu⟩ := by
    intro i
    change Q (T ((x.toLinearMap ^ i) u)) - Q ((x.toLinearMap ^ i) u) = Q (T u) - Q u
    rw [hTpow, hxQi, hxQi]
  have hsum : ∑ i ∈ Finset.range p, (⟨(x.toLinearMap ^ i) u, hmemU i⟩ : U) = 0 := by
    apply Subtype.ext
    rw [Submodule.coe_sum]
    exact hx.sum_pow_eq_zero_orbit hh hne1 hu
  have h0 := congrArg D hsum
  rw [map_sum, map_zero] at h0
  simp only [hD, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h0
  have h4 : D ⟨u, hu⟩ = 0 := (mul_eq_zero.mp h0).resolve_left hx.cast_ne_zero
  change Q (T u) - Q u = 0 at h4
  exact sub_eq_zero.mp h4

end GeomSum


end CFSG.RankThree.PartOne.KCOrthogonal
