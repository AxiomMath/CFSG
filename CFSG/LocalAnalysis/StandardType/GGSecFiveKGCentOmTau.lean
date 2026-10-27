module

public import CFSG.LocalAnalysis.StandardType.GGRootCentKGOTwoOmPlusSemi
public import CFSG.LocalAnalysis.StandardType.GGSixAutSteinbergTrialitySpin

import CFSG.LocalAnalysis.StandardType.GGRootCentKGOTwoOmPlusStep
import CFSG.LocalAnalysis.StandardType.GGSixAutSteinbergTrialityModel
import CFSG.LieType.Universal.Spin.Generation.Eichler
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmas

public section

namespace CFSG.StandardType.KGCentOm

open CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.StandardType.KGOm
  CFSG.ClassicalGroups.Orthogonal QuadraticMap

private theorem eichler_smul_eq_add_smul_sub {K : Type} [Field K] {V : Type*} [AddCommGroup V]
    [Module K V] {Q : QuadraticForm K V} {u w : V} (hu : Q u = 0) (hw : Q w = 0)
    (huw : polar Q u w = 0) (c : K) (y : V) :
    eichler Q u (c • w) y = y + c • (eichler Q u w y - y) := by
  have h1 := CFSG.LocalAnalysis.ComponentInitial.eichler_smul_apply Q hu hw huw 1 y
  rw [one_smul] at h1
  rw [CFSG.LocalAnalysis.ComponentInitial.eichler_smul_apply Q hu hw huw c y, h1]
  module

theorem eq_of_conj_eichler_smul_eq {K : Type} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} (g : V ≃ₗ[K] V) {u w u' w' : V} (hu : Q u = 0) (hw : Q w = 0)
    (huw : polar Q u w = 0) (hu' : Q u' = 0) (hw' : Q w' = 0) (huw' : polar Q u' w' = 0)
    (hne : eichler Q u w ≠ 1) {a b : K}
    (h1 : g * eichler Q u' w' * g⁻¹ = eichler Q u w)
    (h2 : g * eichler Q u' (a • w') * g⁻¹ = eichler Q u (b • w)) : a = b := by
  obtain ⟨x, hx⟩ : ∃ x, eichler Q u w x ≠ x := by
    by_contra hcon
    push Not at hcon
    exact hne (LinearEquiv.ext fun x => by rw [hcon x]; rfl)
  have e1 := congrArg (fun e : V ≃ₗ[K] V => e x) h1
  have e2 := congrArg (fun e : V ≃ₗ[K] V => e x) h2
  simp only [LinearEquiv.mul_apply] at e1 e2
  rw [eichler_smul_eq_add_smul_sub hu' hw' huw', eichler_smul_eq_add_smul_sub hu hw huw, map_add,
    map_smul, map_sub, LinearEquiv.apply_inv_apply', e1] at e2
  have e3 : (a - b) • (eichler Q u w x - x) = 0 := by
    rw [sub_smul, add_left_cancel e2, sub_self]
  rcases smul_eq_zero.mp e3 with h | h
  · exact sub_eq_zero.mp h
  · exact absurd (sub_eq_zero.mp h) hx

private theorem eichler_plusVec_ne_one {n : ℕ} {K : Type} [Field K] {i j : Fin n} (hij : i ≠ j)
    (s t : Bool) : eichler (quadPlus n K) (plusVec n K j t) (plusVec n K i s) ≠ 1 := by
  intro h
  have hu := quadPlus_plusVec n K j t
  have huw : polar (quadPlus n K) (plusVec n K j t) (plusVec n K i s) = 0 := by
    rw [polar_quadPlus_plusVec]
    simp [hij.symm]
  have h1 : polar (quadPlus n K) (plusVec n K j (!t)) (plusVec n K j t) = 1 := by
    rw [polar_quadPlus_plusVec]
    simp
  have h2 : polar (quadPlus n K) (plusVec n K j (!t)) (plusVec n K i s) = 0 := by
    rw [polar_quadPlus_plusVec]
    simp [hij.symm]
  have h3 := congrArg (fun e : (Fin n ⊕ Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K) =>
    e (plusVec n K j (!t))) h
  simp only [eichler_apply hu huw, h1, h2, quadPlus_plusVec] at h3
  have hw0 : plusVec n K i s = 0 := by simpa using h3
  have h4 : polar (quadPlus n K) (plusVec n K i s) (plusVec n K i (!s)) = 1 := by
    rw [polar_quadPlus_plusVec]
    simp
  rw [hw0, polar_zero_left] at h4
  exact zero_ne_one h4

private theorem ringEquiv_eq_one_of_conj_eichler {K : Type} [Field K] {V : Type*}
    [AddCommGroup V] [Module K V] {Q : QuadraticForm K V} (g : V ≃ₗ[K] V) {u w u' w' : V}
    (hu : Q u = 0) (hw : Q w = 0) (huw : polar Q u w = 0) (hu' : Q u' = 0) (hw' : Q w' = 0)
    (huw' : polar Q u' w' = 0) (hne : eichler Q u w ≠ 1) {τ : K ≃+* K}
    (h : ∀ b : K, g * eichler Q u' (τ b • w') * g⁻¹ = eichler Q u (b • w)) : τ = 1 :=
  RingEquiv.ext fun b => eq_of_conj_eichler_smul_eq g hu hw huw hu' hw' huw' hne
    (by simpa using h 1) (h b)

theorem ringEquiv_eq_one_of_conj_longRoot {n : ℕ} {K : Type} [Field K] [CharP K 2] (hn : 3 ≤ n)
    {c : spinGroup (quadPlus n K) →* spinGroup (quadPlus n K)} {ε : Bool} {τ : K ≃+* K}
    (hcA : ∀ (k : spinGroup (quadPlus n K)) (y : Fin n ⊕ Fin n → K),
      spinAction (quadPlus n K) (c k) (plusSemi (by omega) ε τ y) =
        plusSemi (by omega) ε τ (spinAction (quadPlus n K) k y))
    {γ : spinGroup (quadPlus n K)} {i j : Fin n} (hij : i ≠ j) (s s' : Bool)
    (hfix : ∀ b : K, γ * c ((plusFrame n K hn).longRoot hij s s' (.ofAdd b)) * γ⁻¹ =
      (plusFrame n K hn).longRoot hij s s' (.ofAdd b)) : τ = 1 := by
  have hn1 : 1 ≤ n := by omega
  have hu : quadPlus n K (plusVec n K j s') = 0 := quadPlus_plusVec n K j s'
  have hw : quadPlus n K (plusVec n K i s) = 0 := quadPlus_plusVec n K i s
  have huw : polar (quadPlus n K) (plusVec n K j s') (plusVec n K i s) = 0 := by
    rw [polar_quadPlus_plusVec]
    simp [hij.symm]
  have hσ : ∀ b : K, spinAction (quadPlus n K) ((plusFrame n K hn).longRoot hij s s' (.ofAdd b)) =
      eichler (quadPlus n K) (plusVec n K j s') (b • plusVec n K i s) := fun b =>
    (plusFrame n K hn).spinAction_longRoot_eq_eichler hij s s' b
  have hσc : ∀ b : K, spinAction (quadPlus n K)
      (c ((plusFrame n K hn).longRoot hij s s' (.ofAdd b))) =
      eichler (quadPlus n K) (plusSemi hn1 ε τ (plusVec n K j s'))
        (τ b • plusSemi hn1 ε τ (plusVec n K i s)) := by
    intro b
    refine LinearEquiv.ext fun x => ?_
    set y : Fin n ⊕ Fin n → K := plusSemi hn1 ε τ⁻¹ x
    have hAy : plusSemi hn1 ε τ y = x := plusSemi_inverse_right hn1 ε τ x
    have hbw : polar (quadPlus n K) (plusVec n K j s') (b • plusVec n K i s) = 0 := by
      rw [polar_smul_right_eq, huw, mul_zero]
    have hcx : spinAction (quadPlus n K) (c ((plusFrame n K hn).longRoot hij s s' (.ofAdd b))) x =
        plusSemi hn1 ε τ
          (spinAction (quadPlus n K) ((plusFrame n K hn).longRoot hij s s' (.ofAdd b)) y) := by
      rw [← hAy]
      simpa using hcA ((plusFrame n K hn).longRoot hij s s' (.ofAdd b)) y
    rw [hcx, hσ b, plusSemi_eichler hn1 ε τ hu hbw, plusSemi_smul, hAy]
  refine ringEquiv_eq_one_of_conj_eichler (spinAction (quadPlus n K) γ)
    (u' := plusSemi hn1 ε τ (plusVec n K j s')) (w' := plusSemi hn1 ε τ (plusVec n K i s))
    hu hw huw (by rw [plusSemi_quadratic, hu, map_zero])
    (by rw [plusSemi_quadratic, hw, map_zero]) (by rw [plusSemi_polar, huw, map_zero])
    (eichler_plusVec_ne_one hij s s') fun b => ?_
  have h := congrArg (spinAction (quadPlus n K)) (hfix b)
  rw [map_mul, map_mul, map_inv, hσc b, hσ b] at h
  exact h

theorem ringEquiv_eq_one_of_conj_xr {K : Type} [Field K] [CharP K 2] {τ : K ≃+* K}
    {γ : Triality.Sp8 K} {δ δ' : Fin 4 → ℤ} (hδ : δ ∈ Triality.rootsD4)
    (hδ' : δ' ∈ Triality.rootsD4)
    (hfix : ∀ b : K, γ * Triality.xr δ' (τ b) * γ⁻¹ = Triality.xr δ b) : τ = 1 := by
  obtain ⟨i, j, s, t, hij, h, -⟩ := Triality.exists_eq_fromStd hδ
  obtain ⟨i', j', s', t', hij', h', -⟩ := Triality.exists_eq_fromStd hδ'
  have hσ : ∀ b : K, spinAction (quadPlus 4 K) (Triality.xr δ b) =
      eichler (quadPlus 4 K) (plusVec 4 K j t) (b • plusVec 4 K i s) := fun b => by
    rw [Triality.xr_eq_longRoot hij h]
    exact (plusFrame 4 K Triality.three_le_four).spinAction_longRoot_eq_eichler hij s t b
  have hσ' : ∀ b : K, spinAction (quadPlus 4 K) (Triality.xr δ' b) =
      eichler (quadPlus 4 K) (plusVec 4 K j' t') (b • plusVec 4 K i' s') := fun b => by
    rw [Triality.xr_eq_longRoot hij' h']
    exact (plusFrame 4 K Triality.three_le_four).spinAction_longRoot_eq_eichler hij' s' t' b
  refine ringEquiv_eq_one_of_conj_eichler (spinAction (quadPlus 4 K) γ)
    (quadPlus_plusVec 4 K j t) (quadPlus_plusVec 4 K i s) ?_ (quadPlus_plusVec 4 K j' t')
    (quadPlus_plusVec 4 K i' s') ?_ (eichler_plusVec_ne_one hij s t) fun b => ?_
  · rw [polar_quadPlus_plusVec]
    simp [hij.symm]
  · rw [polar_quadPlus_plusVec]
    simp [hij'.symm]
  · have h := congrArg (spinAction (quadPlus 4 K)) (hfix b)
    rw [map_mul, map_mul, map_inv, hσ' (τ b), hσ b] at h
    exact h

end CFSG.StandardType.KGCentOm

end
