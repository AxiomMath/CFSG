module

public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelSpNsTorus
public import CFSG.RankThree.PartOne.S11d.OrthDicksonOmega
public import TauCeti.LinearAlgebra.BilinearForm.SymplecticBasis
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalAnisotropicPlaneRegular
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular

public section

namespace CFSG.StandardType

namespace OmMv

open Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.RankThree.Classical2 (orthDerived)

section Conj

variable {K : Type} [Field K] {X V : Type} [AddCommGroup X] [Module K X] [AddCommGroup V]
  [Module K V] (Φ : X ≃ₗ[K] V)

@[expose] def fc : (X ≃ₗ[K] X) →* (V ≃ₗ[K] V) where
  toFun M := Φ.symm.trans (M.trans Φ)
  map_one' := LinearEquiv.ext fun v => by simp
  map_mul' M M' := LinearEquiv.ext fun v => by simp [LinearEquiv.mul_apply]

theorem fc_apply (M : X ≃ₗ[K] X) (x : X) : fc Φ M (Φ x) = Φ (M x) := by
  simp [fc]

end Conj

section QuadSum

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem quad_sum_add {ι : Type} (t : Finset ι) (x : ι → V) (y : V)
    (hxx : ∀ i ∈ t, ∀ j ∈ t, i ≠ j → polar Q (x i) (x j) = 0)
    (hxy : ∀ i ∈ t, polar Q (x i) y = 0) :
    Q (∑ i ∈ t, x i + y) = ∑ i ∈ t, Q (x i) + Q y := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
    have h1 : polar Q (x a) (∑ i ∈ t, x i) = ∑ i ∈ t, polar Q (x a) (x i) := by
      simpa only [polarBilin_apply_apply] using map_sum (polarBilin Q (x a)) x t
    have h2 : polar Q (x a) (∑ i ∈ t, x i + y) = 0 := by
      rw [polar_add_right, h1, hxy a (Finset.mem_insert_self a t), add_zero]
      refine Finset.sum_eq_zero fun i hi => hxx a (Finset.mem_insert_self a t) i
        (Finset.mem_insert_of_mem hi) fun h => ha (h ▸ hi)
    rw [Finset.sum_insert ha, Finset.sum_insert ha, add_assoc, QuadraticMap.map_add (⇑Q), h2,
      add_zero, ih (fun i hi j hj hij => hxx i (Finset.mem_insert_of_mem hi) j
        (Finset.mem_insert_of_mem hj) hij) (fun i hi => hxy i (Finset.mem_insert_of_mem hi)),
      add_assoc]

end QuadSum

section Frame

variable {K : Type} [Field K] {D V : Type} [AddCommGroup D] [Module K D] [AddCommGroup V]
  [Module K V] {s : ℕ} {κ : Type} {Φ : ((Fin s → D) × (κ → K)) ≃ₗ[K] V}
  {Q : QuadraticForm K V} {ω : LinearMap.BilinForm K D}

theorem frame_eq_sum (Φ : ((Fin s → D) × (κ → K)) ≃ₗ[K] V) (d : Fin s → D) (w : κ → K) :
    Φ (d, w) = ∑ i, Φ (Pi.single i (d i), 0) + Φ (0, w) := by
  classical
  rw [← map_sum, ← map_add]
  congr 1
  refine Prod.ext ?_ ?_
  · simp [Prod.fst_sum, Finset.univ_sum_single]
  · simp [Prod.snd_sum]

theorem polar_frame_single
    (hdec : ∀ d d' w w', polarBilin Q (Φ (d, w)) (Φ (d', w')) =
      ∑ i, ω (d i) (d' i) + polarBilin Q (Φ (0, w)) (Φ (0, w')))
    (i : Fin s) (x : D) (d : Fin s → D) (w : κ → K) :
    polar Q (Φ (Pi.single i x, 0)) (Φ (d, w)) = ω x (d i) := by
  classical
  rw [← polarBilin_apply_apply, hdec, Finset.sum_eq_single i]
  · simp only [Pi.single_eq_same, Prod.mk_zero_zero, map_zero, LinearMap.zero_apply, add_zero]
  · intro k _ hk
    rw [Pi.single_eq_of_ne hk, map_zero, LinearMap.zero_apply]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem quad_frame
    (hdec : ∀ d d' w w', polarBilin Q (Φ (d, w)) (Φ (d', w')) =
      ∑ i, ω (d i) (d' i) + polarBilin Q (Φ (0, w)) (Φ (0, w')))
    (d : Fin s → D) (w : κ → K) :
    Q (Φ (d, w)) = ∑ i, Q (Φ (Pi.single i (d i), 0)) + Q (Φ (0, w)) := by
  classical
  rw [frame_eq_sum Φ d w]
  refine quad_sum_add _ _ _ (fun i _ j _ hij => ?_) (fun i _ => ?_)
  · rw [polar_frame_single hdec, Pi.single_eq_of_ne hij, map_zero]
  · rw [polar_frame_single hdec, Pi.zero_apply, map_zero]

theorem quad_mono
    (hdec : ∀ d d' w w', polarBilin Q (Φ (d, w)) (Φ (d', w')) =
      ∑ i, ω (d i) (d' i) + polarBilin Q (Φ (0, w)) (Φ (0, w')))
    (π : Equiv.Perm (Fin s)) (T : Fin s → (D ≃ₗ[K] D))
    (hT : ∀ k x, Q (Φ (Pi.single k (T k x), 0)) = Q (Φ (Pi.single (π k) x, 0))) :
    fc Φ (SpNS.monoEquiv π T) ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
  refine TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => ?_
  obtain ⟨⟨d, w⟩, rfl⟩ := Φ.surjective v
  rw [fc_apply, SpNS.monoEquiv_apply, quad_frame hdec (fun i => T i (d (π i))) w,
    quad_frame hdec d w]
  congr 1
  simp only [hT]
  exact Equiv.sum_comp π (fun k => Q (Φ (Pi.single k (d k), 0)))

theorem quad_single_sub [CharP K 2]
    (hdec : ∀ d d' w w', polarBilin Q (Φ (d, w)) (Φ (d', w')) =
      ∑ i, ω (d i) (d' i) + polarBilin Q (Φ (0, w)) (Φ (0, w')))
    (i : Fin s) (x y : D) :
    Q (Φ (Pi.single i (x - y), 0)) =
      Q (Φ (Pi.single i x, 0)) + Q (Φ (Pi.single i y, 0)) + ω x y := by
  have e : Φ (Pi.single i (x - y), 0) = Φ (Pi.single i x, 0) + -Φ (Pi.single i y, 0) := by
    rw [← map_neg, ← map_add, Prod.neg_mk, neg_zero, Prod.mk_add_mk, ← Pi.single_neg,
      ← Pi.single_add, add_zero, sub_eq_add_neg]
  rw [e, QuadraticMap.map_add (⇑Q), QuadraticMap.map_neg, polar_neg_right,
    polar_frame_single hdec, Pi.single_eq_same, CharTwo.neg_eq]

theorem blockQ_sub_one [CharP K 2]
    (hdec : ∀ d d' w w', polarBilin Q (Φ (d, w)) (Φ (d', w')) =
      ∑ i, ω (d i) (d' i) + polarBilin Q (Φ (0, w)) (Φ (0, w')))
    (i : Fin s) {f : D → D} (hf : ∀ x, Q (Φ (Pi.single i (f x), 0)) = Q (Φ (Pi.single i x, 0)))
    (z : D) : Q (Φ (Pi.single i (f z - z), 0)) = ω (f z) z := by
  rw [quad_single_sub hdec, hf, CharTwo.add_self_eq_zero, zero_add]

theorem blockQ_eq [CharP K 2]
    (hdec : ∀ d d' w w', polarBilin Q (Φ (d, w)) (Φ (d', w')) =
      ∑ i, ω (d i) (d' i) + polarBilin Q (Φ (0, w)) (Φ (0, w')))
    {c : D → D} (hc1 : ∀ u, ∃ u₀, c u₀ - u₀ = u) {i j : Fin s}
    (hi : ∀ x, Q (Φ (Pi.single i (c x), 0)) = Q (Φ (Pi.single i x, 0)))
    (hj : ∀ x, Q (Φ (Pi.single j (c x), 0)) = Q (Φ (Pi.single j x, 0))) (x : D) :
    Q (Φ (Pi.single i x, 0)) = Q (Φ (Pi.single j x, 0)) := by
  obtain ⟨z, rfl⟩ := hc1 x
  rw [blockQ_sub_one hdec i hi, blockQ_sub_one hdec j hj]

theorem blockQ_twist [CharP K 2]
    (hdec : ∀ d d' w w', polarBilin Q (Φ (d, w)) (Φ (d', w')) =
      ∑ i, ω (d i) (d' i) + polarBilin Q (Φ (0, w)) (Φ (0, w')))
    {c : D → D} (hc1 : ∀ u, ∃ u₀, c u₀ - u₀ = u) {i : Fin s}
    (hi : ∀ x, Q (Φ (Pi.single i (c x), 0)) = Q (Φ (Pi.single i x, 0)))
    {T : D →ₗ[K] D} (hT : ∀ x y, ω (T x) (T y) = ω x y) {c' : D → D}
    (hc' : ∀ x, Q (Φ (Pi.single i (c' x), 0)) = Q (Φ (Pi.single i x, 0)))
    (hTc : ∀ x, T (c x) = c' (T x)) (x : D) :
    Q (Φ (Pi.single i (T x), 0)) = Q (Φ (Pi.single i x, 0)) := by
  obtain ⟨z, rfl⟩ := hc1 x
  rw [map_sub, hTc, blockQ_sub_one hdec i hc', blockQ_sub_one hdec i hi, ← hTc, hT]

theorem blockQ_pow {c : D ≃ₗ[K] D} {i : Fin s}
    (hi : ∀ x, Q (Φ (Pi.single i (c x), 0)) = Q (Φ (Pi.single i x, 0))) (m : ℕ) (x : D) :
    Q (Φ (Pi.single i ((c ^ m) x), 0)) = Q (Φ (Pi.single i x, 0)) := by
  induction m generalizing x with
  | zero => rw [pow_zero]; rfl
  | succ m ih => rw [CoordSpNs.pow_apply_succ, hi, ih]

end Frame

section Swap

variable {K : Type} [Field K] {D V : Type} [AddCommGroup D] [Module K D] [AddCommGroup V]
  [Module K V] {s : ℕ} {κ : Type} {Φ : ((Fin s → D) × (κ → K)) ≃ₗ[K] V}

theorem finrank_commSpace_swap {i j : Fin s} (hij : i ≠ j) :
    finrank K (commSpace (fc Φ (SpNS.monoEquiv (κ := κ) (Equiv.swap i j)
      fun _ => LinearEquiv.refl K D))) = finrank K D := by
  classical
  set w := fc Φ (SpNS.monoEquiv (κ := κ) (Equiv.swap i j) fun _ => LinearEquiv.refl K D) with hw
  set ι : D →ₗ[K] V := Φ.toLinearMap ∘ₗ LinearMap.inl K _ _ ∘ₗ
    (LinearMap.single K (fun _ => D) i - LinearMap.single K (fun _ => D) j) with hι
  have hιapply : ∀ y, ι y = Φ (Pi.single i y - Pi.single j y, 0) := fun y => rfl
  have hinj : Function.Injective ι := by
    intro a b hab
    rw [hιapply, hιapply] at hab
    have h := congrArg (fun v => (Φ.symm v).1 i) hab
    simpa [Pi.single_apply, hij] using h
  have hrange : commSpace w = LinearMap.range ι := by
    apply le_antisymm
    · intro y hy
      obtain ⟨v, rfl⟩ := mem_commSpace.mp hy
      obtain ⟨⟨d, x⟩, rfl⟩ := Φ.surjective v
      refine ⟨d j - d i, ?_⟩
      rw [hιapply, hw, fc_apply, SpNS.monoEquiv_apply, ← map_sub, Prod.mk_sub_mk, sub_self]
      congr 2
      funext k
      simp only [Pi.sub_apply, LinearEquiv.refl_apply]
      by_cases hki : k = i
      · subst hki
        simp [hij]
      · by_cases hkj : k = j
        · subst hkj
          simp [hki]
        · simp [hki, hkj, Equiv.swap_apply_of_ne_of_ne hki hkj]
    · rintro _ ⟨y, rfl⟩
      refine mem_commSpace.mpr ⟨Φ (Pi.single j y, 0), ?_⟩
      rw [hιapply, hw, fc_apply, SpNS.monoEquiv_apply, ← map_sub, Prod.mk_sub_mk, sub_self]
      congr 2
      funext k
      simp only [Pi.sub_apply, LinearEquiv.refl_apply]
      by_cases hki : k = i
      · subst hki
        simp [hij]
      · by_cases hkj : k = j
        · subst hkj
          simp [hki]
        · simp [hki, hkj, Equiv.swap_apply_of_ne_of_ne hki hkj]
  rw [hrange, LinearMap.finrank_range_of_inj hinj]

variable {Q : QuadraticForm K V} {ω : LinearMap.BilinForm K D}

theorem swap_mem_orthDerived [Finite K] [CharP K 2] [FiniteDimensional K V]
    [FiniteDimensional K D] (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ v ∈ T, Q v = 0)
    (hdec : ∀ d d' w w', polarBilin Q (Φ (d, w)) (Φ (d', w')) =
      ∑ i, ω (d i) (d' i) + polarBilin Q (Φ (0, w)) (Φ (0, w')))
    (hωa : ω.IsAlt) (hωnd : ω.Nondegenerate) {i j : Fin s} (hij : i ≠ j)
    (hQij : ∀ x, Q (Φ (Pi.single i x, 0)) = Q (Φ (Pi.single j x, 0))) :
    fc Φ (SpNS.monoEquiv (κ := κ) (Equiv.swap i j) fun _ => LinearEquiv.refl K D) ∈
      orthDerived Q := by
  have hO : fc Φ (SpNS.monoEquiv (κ := κ) (Equiv.swap i j) fun _ => LinearEquiv.refl K D) ∈
      TauCeti.QuadraticMap.orthogonalGroup Q := by
    refine quad_mono hdec _ _ fun k x => ?_
    rw [LinearEquiv.refl_apply]
    by_cases hki : k = i
    · subst hki
      rw [Equiv.swap_apply_left]
      exact hQij x
    · by_cases hkj : k = j
      · subst hkj
        rw [Equiv.swap_apply_right]
        exact (hQij x).symm
      · rw [Equiv.swap_apply_of_ne_of_ne hki hkj]
  refine CFSG.RankThree.PartOne.FieldFix.omegaGroup_le_orthDerived hQ hT ⟨hO, ?_⟩
  rw [finrank_commSpace_swap hij]
  exact LinearMap.BilinForm.IsAlt.even_finrank hωa hωnd

end Swap

end OmMv

end CFSG.StandardType
