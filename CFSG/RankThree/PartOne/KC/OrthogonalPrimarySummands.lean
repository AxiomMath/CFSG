module

public import CFSG.RankThree.PartOne.KC.OrthogonalSelfDualModel

public section

universe u v

namespace CFSG.RankThree.PartOne.KCOrthogonal

open Polynomial Module CFSG.RankThree.PartOne.KCPrimary

section Internal

variable {K : Type*} {V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {x : Module.End K V}

open scoped _root_.Classical in
theorem isInternal_primaryComponent (hx : Squarefree (minpoly K x)) :
    DirectSum.IsInternal (fun a : primaryFactors x => primaryComponent x a) := by
  have hbij : Function.Bijective (primarySum x) := (primaryEquivPi hx).symm.bijective
  rw [DirectSum.IsInternal]
  have h1 : ((DirectSum.coeAddMonoidHom (fun a : primaryFactors x => primaryComponent x a)) :
      (DirectSum _ fun a : primaryFactors x => primaryComponent x a) → V) =
      (primarySum x) ∘ (DirectSum.linearEquivFunOnFintype K _
        (fun a : primaryFactors x => primaryComponent x a)) := by
    funext d
    induction d using DirectSum.induction_on with
    | zero => simp
    | of i a =>
      simp only [DirectSum.coeAddMonoidHom_of, Function.comp_apply, primarySum_apply]
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hji
        have := DirectSum.of_eq_of_ne (β := fun i : primaryFactors x => primaryComponent x i) i j
          a hji
        simp [this]
      · simp
    | add a b ha hb => simp only [map_add, Function.comp_apply] at ha hb ⊢; rw [ha, hb]
  rw [h1]
  exact hbij.comp (LinearEquiv.bijective _)


end Internal

section Others

variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

@[expose] noncomputable def othersSpace (x : Module.End K V) (h : K[X]) : Submodule K V :=
  ⨆ (k : K[X]) (_ : k ∈ primaryFactors x ∧ k ≠ h ∧ k ≠ reciprocalPolynomial h),
    primaryComponent x k

theorem OddOrderIsometry.polar_orbit_others (hx : OddOrderIsometry Q p x) {h : K[X]}
    (hh : h ∈ primaryFactors x.toLinearMap) {u r : V}
    (hu : u ∈ orbitSpace x.toLinearMap h) (hr : r ∈ othersSpace x.toLinearMap h) :
    QuadraticMap.polar Q u r = 0 := by
  have hh' := hx.reciprocalPolynomial_mem hh
  obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := Submodule.mem_sup.mp hu
  unfold othersSpace at hr
  refine Submodule.iSup_induction _ (motive := fun r => QuadraticMap.polar Q (u₁ + u₂) r = 0)
    hr (fun k r hr => ?_) (by simp)
    (fun a b ha hb => by rw [QuadraticMap.polar_add_right, ha, hb, add_zero])
  refine Submodule.iSup_induction _ (motive := fun r => QuadraticMap.polar Q (u₁ + u₂) r = 0)
    hr (fun hk r hr => ?_) (by simp)
    (fun a b ha hb => by rw [QuadraticMap.polar_add_right, ha, hb, add_zero])
  have h1 : QuadraticMap.polar Q u₁ r = 0 :=
    hx.polar_primaryComponent_eq_zero hh hk.1 hk.2.2 hu₁ hr
  have h2 : QuadraticMap.polar Q u₂ r = 0 :=
    hx.polar_primaryComponent_eq_zero hh' hk.1
      (by rw [hx.reciprocal_reciprocal_eq hh]; exact hk.2.1) hu₂ hr
  rw [QuadraticMap.polar_add_left, h1, h2, add_zero]

theorem OddOrderIsometry.isCompl_orbit_others (hx : OddOrderIsometry Q p x) {h : K[X]}
    (hh : h ∈ primaryFactors x.toLinearMap) :
    IsCompl (orbitSpace x.toLinearMap h) (othersSpace x.toLinearMap h) := by
  classical
  refine ⟨?_, ?_⟩
  · rw [disjoint_iff_inf_le]
    intro u hu
    obtain ⟨huO, huR⟩ := Submodule.mem_inf.mp hu
    refine (Submodule.mem_bot K).mpr (hx.eq_zero_of_polar_orbit hh huO fun w hw => ?_)
    rw [QuadraticMap.polar_comm]
    exact hx.polar_orbit_others hh hw huR
  · rw [codisjoint_iff, eq_top_iff]
    intro v _
    have hsum := congrArg (fun f : Module.End K V => f v)
      (sum_primaryProjection (x := x.toLinearMap) hx.squarefree_minpoly)
    simp only [LinearMap.sum_apply, Module.End.one_apply] at hsum
    rw [← hsum]
    refine Submodule.sum_mem _ fun k hk => ?_
    have hmem := primaryProjection_mem hx.squarefree_minpoly hk v
    by_cases hkh : k = h
    · subst hkh
      exact Submodule.mem_sup_left (Submodule.mem_sup_left hmem)
    by_cases hkh' : k = reciprocalPolynomial h
    · subst hkh'
      exact Submodule.mem_sup_left (Submodule.mem_sup_right hmem)
    exact Submodule.mem_sup_right
      (Submodule.mem_iSup_of_mem k (Submodule.mem_iSup_of_mem ⟨hk, hkh, hkh'⟩ hmem))

end Others

section Split

variable {K : Type u} {V : Type v} {W : Type u} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

theorem exists_split_repeated {m : ℕ} (Q : QuadraticForm K V) (QW : QuadraticForm K W)
    (O R : Submodule K V) (hcompl : IsCompl O R)
    (horth : ∀ u ∈ O, ∀ r ∈ R, QuadraticMap.polar Q u r = 0)
    (ι : (Fin m → W) →ₗ[K] V) (hι : Function.Injective ι) (hrange : LinearMap.range ι = O)
    (hQ : ∀ w, Q (ι w) = ∑ i, QW (w i)) :
    ∃ ψ : V ≃ₗ[K] R × (Fin m → W),
      (∀ v, Q v = (Q.comp R.subtype) (ψ v).1 + ∑ i, QW ((ψ v).2 i)) ∧
      (∀ r : R, ψ.symm (r, 0) = (r : V)) ∧ ∀ w, ψ.symm (0, w) = ι w := by
  let eO : (Fin m → W) ≃ₗ[K] O :=
    (LinearEquiv.ofInjective ι hι).trans (LinearEquiv.ofEq _ _ hrange)
  let e : (R × O) ≃ₗ[K] V :=
    (LinearEquiv.prodComm K R O).trans (Submodule.prodEquivOfIsCompl O R hcompl)
  let ψ : V ≃ₗ[K] R × (Fin m → W) :=
    e.symm.trans (LinearEquiv.prodCongr (LinearEquiv.refl K R) eO.symm)
  have hsymm : ∀ (r : R) (w : Fin m → W), ψ.symm (r, w) = (r : V) + ι w := by
    intro r w
    change e (r, eO w) = _
    simp only [e, LinearEquiv.trans_apply, LinearEquiv.prodComm_apply,
      Submodule.coe_prodEquivOfIsCompl', Prod.swap_prod_mk]
    rw [add_comm]
    rfl
  have hmem : ∀ w, ι w ∈ O := fun w => hrange ▸ LinearMap.mem_range_self ι w
  refine ⟨ψ, fun v => ?_, fun r => ?_, fun w => ?_⟩
  · obtain ⟨⟨r, w⟩, hrw⟩ : ∃ p : R × (Fin m → W), p = ψ v := ⟨_, rfl⟩
    have hv : v = (r : V) + ι w := by rw [← hsymm, hrw, ψ.symm_apply_apply]
    rw [← hrw, hv, QuadraticMap.map_add (⇑Q) _ _, hQ, QuadraticMap.polar_comm,
      horth _ (hmem w) _ r.2, add_zero]
    simp [QuadraticMap.comp_apply]
  · rw [hsymm, map_zero, add_zero]
  · rw [hsymm]
    simp

end Split

section Repeated

variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

theorem OddOrderIsometry.repeatedSummands_of_model (hx : OddOrderIsometry Q p x) {h : K[X]}
    (hh : h ∈ primaryFactors x.toLinearMap) {W : Type u} [AddCommGroup W] [Module K W]
    [Nontrivial W] (QW : QuadraticForm K W) (hQW : (QuadraticMap.polarBilin QW).Nondegenerate)
    (h₀ : W ≃ₗ[K] W) (hh₀ : h₀ ∈ TauCeti.QuadraticMap.orthogonalGroup QW) (hord : orderOf h₀ = p)
    (ι : (Fin (primaryMultiplicity x.toLinearMap h) → W) →ₗ[K] V) (hinj : Function.Injective ι)
    (hrange : LinearMap.range ι = orbitSpace x.toLinearMap h)
    (hQ : ∀ w, Q (ι w) = ∑ i, QW (w i)) (hxι : ∀ w, x (ι w) = ι (fun i => h₀ (w i))) :
    RepeatedSummands Q x p h := by
  obtain ⟨ψ, hψQ, hψR, hψW⟩ := exists_split_repeated Q QW (orbitSpace x.toLinearMap h)
    (othersSpace x.toLinearMap h) (hx.isCompl_orbit_others hh)
    (fun u hu r hr => hx.polar_orbit_others hh hu hr) ι hinj hrange hQ
  refine ⟨↥(othersSpace x.toLinearMap h), W, inferInstance, inferInstance, inferInstance,
    inferInstance, Q.comp (othersSpace x.toLinearMap h).subtype, QW, ψ, hψQ, hQW, inferInstance,
    ⟨h₀, hh₀, hord, fun i w => ?_⟩, fun r => ?_, fun w => ?_⟩
  · rw [hψW, hψW, hxι]
    congr 1
    funext j
    by_cases hj : j = i
    · subst hj
      simp
    · simp [hj]
  · rw [hψR]
    exact r.2
  · rw [hψW, ← hrange]
    exact LinearMap.mem_range_self ι w

theorem orderOf_root_unit {h : K[X]} [Fact (Irreducible h)] (hp : p.Prime)
    (hlam0 : AdjoinRoot.root h ≠ 0) (hlam1 : AdjoinRoot.root h ≠ 1)
    (hlamp : AdjoinRoot.root h ^ p = 1) :
    orderOf (Units.mk0 (AdjoinRoot.root h) hlam0) = p := by
  have : Fact p.Prime := ⟨hp⟩
  refine orderOf_eq_prime (Units.ext ?_) fun h1 => hlam1 ?_
  · simpa using hlamp
  · simpa using congrArg Units.val h1

variable [Finite K]

theorem OddOrderIsometry.repeatedSummands_paired (hx : OddOrderIsometry Q p x) (hp : p.Prime)
    {h : K[X]} (hh : h ∈ primaryFactors x.toLinearMap) (hne1 : h ≠ X - 1)
    (hne : h ≠ reciprocalPolynomial h) : RepeatedSummands Q x p h := by
  have hirr := irreducible_of_mem_primaryFactors hh
  have hmon := (mem_primaryFactors.mp hh).2.1
  have : Fact (Irreducible h) := ⟨hirr⟩
  have : Module.Finite K (AdjoinRoot h) := (AdjoinRoot.powerBasis hirr.ne_zero).finite
  have : Finite (AdjoinRoot h) := Module.finite_of_finite K
  have hlam1 : AdjoinRoot.root h ≠ 1 := root_ne_one hmon hne1
  have hlamp : AdjoinRoot.root h ^ p = 1 := root_pow_eq_one (hx.dvd_X_pow_sub_one hh)
  have hp0 : p ≠ 0 := hp.ne_zero
  have hlam0 : AdjoinRoot.root h ≠ 0 := fun h0' => by
    rw [h0', zero_pow hp0] at hlamp
    exact zero_ne_one hlamp
  obtain ⟨-, -, ι, hinj, hrange, hQ, hxι⟩ := hx.pairedModel hh hne1 hne
  set u : (AdjoinRoot h)ˣ := Units.mk0 (AdjoinRoot.root h) hlam0 with hu
  let P : (Fin (primaryMultiplicity x.toLinearMap h) → AdjoinRoot h × AdjoinRoot h) →ₗ[K]
      (Fin (primaryMultiplicity x.toLinearMap h) → AdjoinRoot h) ×
        (Fin (primaryMultiplicity x.toLinearMap h) → AdjoinRoot h) :=
    (LinearMap.pi fun i => (LinearMap.fst K (AdjoinRoot h) (AdjoinRoot h)) ∘ₗ LinearMap.proj i).prod
      (LinearMap.pi fun i => (LinearMap.snd K (AdjoinRoot h) (AdjoinRoot h)) ∘ₗ LinearMap.proj i)
  have hP : ∀ w, P w = (fun i => (w i).1, fun i => (w i).2) := fun w => rfl
  have hPinj : Function.Injective P := fun w w' hww => by
    funext i
    exact Prod.ext (congrFun (Prod.ext_iff.mp hww).1 i) (congrFun (Prod.ext_iff.mp hww).2 i)
  have hPsurj : Function.Surjective P := fun ab => ⟨fun i => (ab.1 i, ab.2 i), rfl⟩
  refine hx.repeatedSummands_of_model hh (pairedForm K (AdjoinRoot h))
    (pairedForm_nondegenerate K (AdjoinRoot h)) (pairedRotation (K := K) u)
    (pairedRotation_mem_orthogonalGroup u) ?_ (ι ∘ₗ P) (hinj.comp hPinj) ?_ ?_ ?_
  · have h1 : orderOf (pairedRotationHom K (AdjoinRoot h) u) = orderOf u :=
      orderOf_injective _ pairedRotationHom_injective u
    rw [orderOf_root_unit hp hlam0 hlam1 hlamp] at h1
    exact h1
  · rw [LinearMap.range_comp, LinearMap.range_eq_top.mpr hPsurj, Submodule.map_top, hrange]
  · intro w
    rw [LinearMap.comp_apply, hP, hQ, map_sum]
    exact Finset.sum_congr rfl fun i _ => (pairedForm_apply K (AdjoinRoot h) _ _).symm
  · intro w
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hP, hP, hxι]
    congr 1

theorem OddOrderIsometry.repeatedSummands_selfDual (hx : OddOrderIsometry Q p x) (hp : p.Prime)
    (hp2 : p ≠ 2) {h : K[X]} (hh : h ∈ primaryFactors x.toLinearMap) (hne1 : h ≠ X - 1)
    (hself : h = reciprocalPolynomial h) : RepeatedSummands Q x p h := by
  have hirr := irreducible_of_mem_primaryFactors hh
  have hmon := (mem_primaryFactors.mp hh).2.1
  have : Fact (Irreducible h) := ⟨hirr⟩
  have : Module.Finite K (AdjoinRoot h) := (AdjoinRoot.powerBasis hirr.ne_zero).finite
  have : Finite (AdjoinRoot h) := Module.finite_of_finite K
  have hlam1 : AdjoinRoot.root h ≠ 1 := root_ne_one hmon hne1
  have hlamp : AdjoinRoot.root h ^ p = 1 := root_pow_eq_one (hx.dvd_X_pow_sub_one hh)
  have hp0 : p ≠ 0 := hp.ne_zero
  have hlam0 : AdjoinRoot.root h ≠ 0 := fun h0' => by
    rw [h0', zero_pow hp0] at hlamp
    exact zero_ne_one hlamp
  obtain ⟨d, hdeg, -, -, -, -, hroot, ι, hinj, hrange, hQ, hxι⟩ :=
    hx.selfDualModel (hp.odd_of_ne_two hp2) hh hne1 hself
  have hd : finrank K (AdjoinRoot h) = 2 * d := by
    rw [(AdjoinRoot.powerBasis hirr.ne_zero).finrank, AdjoinRoot.powerBasis_dim, hdeg]
  set u : (AdjoinRoot h)ˣ := Units.mk0 (AdjoinRoot.root h) hlam0 with hu
  have hQ' : ∀ a, Q (ι a) = ∑ i, hermitianForm hd (a i) := fun a => by
    obtain ⟨hmem, hq⟩ := hQ a
    rw [hq]
    have : (⟨∑ i, a i * a i ^ (Nat.card K ^ d), hmem⟩ : fixedSubfield K (AdjoinRoot h) d) =
        ∑ i, unitaryNorm hd (a i) :=
      Subtype.ext (by simp [coe_unitaryNorm, frobPow_apply])
    rw [this, map_sum]
    rfl
  have hunit : (u : AdjoinRoot h) * frobPow K (AdjoinRoot h) d u = 1 := by
    rw [hu, Units.val_mk0, frobPow_apply, hroot, mul_inv_cancel₀ hlam0]
  refine hx.repeatedSummands_of_model hh (hermitianForm hd) (hermitianForm_nondegenerate hd)
    (mulEquiv (K := K) u) (mulEquiv_mem_orthogonalGroup hd u hunit) ?_ ι hinj ?_ hQ' ?_
  · have h1 : orderOf (mulEquivHom K (AdjoinRoot h) u) = orderOf u :=
      orderOf_injective _ (mulEquivHom_injective) u
    rw [orderOf_root_unit hp hlam0 hlam1 hlamp] at h1
    exact h1
  · rw [hrange, orbitSpace, ← hself, sup_idem]
  · intro a
    rw [hxι]
    rfl

end Repeated


end CFSG.RankThree.PartOne.KCOrthogonal

namespace CFSG.RankThree.PartOne

open Polynomial CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal

open scoped _root_.Classical in
theorem orthogonal_nontrivial_primary_repeated_quadratic_summands
    {K : Type u} {V : Type v} [Field K] [Finite K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpl : p ≠ ringChar K) {x : V ≃ₗ[K] V}
    (hxO : x ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hxp : orderOf x = p) :
    Set.BijOn reciprocalPolynomial (primaryFactors x.toLinearMap : Set K[X])
      (primaryFactors x.toLinearMap : Set K[X]) ∧
    DirectSum.IsInternal
      (fun h : primaryFactors x.toLinearMap => primaryComponent x.toLinearMap (h : K[X])) ∧
    (∀ h ∈ primaryFactors x.toLinearMap, ∀ k ∈ primaryFactors x.toLinearMap, k ≠ h →
      k ≠ reciprocalPolynomial h → ∀ v ∈ primaryComponent x.toLinearMap h,
        ∀ w ∈ primaryComponent x.toLinearMap k, QuadraticMap.polar Q v w = 0) ∧
    (∀ h ∈ primaryFactors x.toLinearMap, ∀ u ∈ orbitSpace x.toLinearMap h,
      (∀ w ∈ orbitSpace x.toLinearMap h, QuadraticMap.polar Q u w = 0) → u = 0) ∧
    (∀ (h : K[X]) (hh : h ∈ primaryFactors x.toLinearMap), h ≠ X - 1 →
      h ≠ reciprocalPolynomial h → PairedModel Q x h (irreducible_of_mem_primaryFactors hh)) ∧
    (∀ (h : K[X]) (hh : h ∈ primaryFactors x.toLinearMap), h ≠ X - 1 →
      h = reciprocalPolynomial h → SelfDualModel Q x h (irreducible_of_mem_primaryFactors hh)) ∧
    ∀ h ∈ primaryFactors x.toLinearMap, h ≠ X - 1 → RepeatedSummands Q x p h := by
  have hpℓ : (p : K) ≠ 0 := by
    intro h0
    have h1 := (ringChar.spec K p).mp h0
    have hℓ : (ringChar K).Prime := CharP.char_is_prime K _
    rcases (Nat.dvd_prime hp).mp h1 with h2 | h2
    · exact hℓ.one_lt.ne' h2
    · exact hpl h2.symm
  have hx : OddOrderIsometry Q p x :=
    ⟨hxO, by rw [← hxp]; exact pow_orderOf_eq_one x, hpℓ, fun v hv =>
      hQ.1 v fun w => by simpa using hv w⟩
  refine ⟨hx.bijOn_reciprocalPolynomial, isInternal_primaryComponent hx.squarefree_minpoly,
    fun h hh k hk hkh hkh' v hv w hw => hx.polar_primaryComponent_eq_zero hh hk hkh' hv hw,
    fun h hh u hu hperp => hx.eq_zero_of_polar_orbit hh hu hperp,
    fun h hh hne1 hne => hx.pairedModel hh hne1 hne,
    fun h hh hne1 hself => hx.selfDualModel (hp.odd_of_ne_two hp2) hh hne1 hself,
    fun h hh hne1 => ?_⟩
  by_cases hself : h = reciprocalPolynomial h
  · exact hx.repeatedSummands_selfDual hp hp2 hh hne1 hself
  · exact hx.repeatedSummands_paired hp hh hne1 hself

end CFSG.RankThree.PartOne
