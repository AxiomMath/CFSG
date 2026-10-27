module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.LinearAlgebra.Pi

public section

namespace CFSG.StandardType.LinTwoTv

variable {s : ℕ}

@[expose] def hamWt (v : Fin s → ZMod 3) : ℕ := (Finset.univ.filter fun i => v i ≠ 0).card

theorem eq_zero_of_hamWt_eq_zero {v : Fin s → ZMod 3} (h : hamWt v = 0) : v = 0 := by
  have h' := Finset.filter_eq_empty_iff.mp (Finset.card_eq_zero.mp h)
  funext i
  simpa using h' (Finset.mem_univ i)

theorem hamWt_single (i : Fin s) {c : ZMod 3} (hc : c ≠ 0) : hamWt (Pi.single i c) = 1 := by
  rw [hamWt, Finset.card_eq_one]
  refine ⟨i, ?_⟩
  ext j
  by_cases hj : j = i
  · subst hj
    simp [hc]
  · simp [hj]

theorem exists_single_of_hamWt_eq_one {v : Fin s → ZMod 3} (h : hamWt v = 1) :
    ∃ j, v j ≠ 0 ∧ v = Pi.single j (v j) := by
  obtain ⟨j, hj⟩ := Finset.card_eq_one.mp h
  have hvj : v j ≠ 0 := by
    have : j ∈ Finset.univ.filter fun i => v i ≠ 0 := by
      rw [hj]
      exact Finset.mem_singleton_self j
    simpa using this
  refine ⟨j, hvj, ?_⟩
  funext i
  by_cases hi : i = j
  · subst hi
    simp
  · have hn : i ∉ Finset.univ.filter fun i => v i ≠ 0 := by
      rw [hj]
      simpa using hi
    have h0 : v i = 0 := by simpa using hn
    simp [Pi.single_apply, hi, h0]

theorem smul_single_one (i : Fin s) (c : ZMod 3) :
    c • (Pi.single i 1 : Fin s → ZMod 3) = Pi.single i c := by
  rw [← Pi.single_smul, smul_eq_mul, mul_one]

theorem eq_id_of_hamWt_sq (τ : (Fin s → ZMod 3) →ₗ[ZMod 3] (Fin s → ZMod 3))
    (hw : ∀ v, hamWt (τ v) = hamWt v) (hsq : ∀ v, τ (τ v - v) = τ v - v) :
    ∀ v, τ v = v := by
  classical
  have hinj : ∀ v, τ v = 0 → v = 0 := fun v hv =>
    eq_zero_of_hamWt_eq_zero (by rw [← hw v, hv]; simp [hamWt])
  have hw1 : ∀ i : Fin s, hamWt (τ (Pi.single i 1)) = 1 := fun i => by
    rw [hw]
    exact hamWt_single i one_ne_zero
  choose π hπ using fun i : Fin s => exists_single_of_hamWt_eq_one (hw1 i)
  set c : Fin s → ZMod 3 := fun i => τ (Pi.single i 1) (π i) with hc
  have hc0 : ∀ i, c i ≠ 0 := fun i => (hπ i).1
  have hτe : ∀ i, τ (Pi.single i 1) = Pi.single (π i) (c i) := fun i => (hπ i).2
  have hτs : ∀ i (x : ZMod 3), τ (Pi.single i x) = Pi.single (π i) (x * c i) := fun i x => by
    rw [← smul_single_one, map_smul, hτe, ← Pi.single_smul, smul_eq_mul]
  have hπinj : Function.Injective π := by
    intro i j hij
    by_contra hne
    have h1 : τ (Pi.single i (c j) - Pi.single j (c i)) = 0 := by
      rw [map_sub, hτs, hτs, hij]
      simp [mul_comm]
    have h2 := hinj _ h1
    have h3 := congrFun h2 i
    simp [Pi.single_apply, hne, Ne.symm hne] at h3
    exact hc0 j h3
  by_contra hcon
  push Not at hcon
  obtain ⟨i, hi⟩ : ∃ i, τ (Pi.single i 1) ≠ Pi.single i 1 := by
    by_contra h
    push Not at h
    obtain ⟨v, hv⟩ := hcon
    apply hv
    have : τ = LinearMap.id := LinearMap.pi_ext fun i x => by
      rw [← smul_single_one, map_smul, h, LinearMap.id_apply]
    rw [this]
    rfl
  by_cases hπi : π i = i
  ·
    have hci1 : c i ≠ 1 := fun h => hi (by rw [hτe, hπi, h])
    have hci : c i = 2 := by
      have : ∀ x : ZMod 3, x ≠ 0 → x ≠ 1 → x = 2 := by decide
      exact this _ (hc0 i) hci1
    have h2 := hsq (Pi.single i 1)
    rw [hτe, hπi, hci] at h2
    have h3 : (Pi.single i (2 : ZMod 3) - Pi.single i 1 : Fin s → ZMod 3) = Pi.single i 1 := by
      rw [← Pi.single_sub]
      congr 1
    rw [h3, hτe, hπi, hci] at h2
    apply hi
    rw [hτe, hπi, hci]
    exact h2
  ·
    have h2 := congrFun (hsq (Pi.single i 1)) (π i)
    rw [map_sub, hτe, hτs] at h2
    have hπj : ¬ π i = π (π i) := fun h => hπi (hπinj h.symm)
    simp only [Pi.sub_apply, Pi.single_apply, hπj, hπi, if_false, if_true, zero_sub, sub_zero,
      ite_true] at h2
    have h4 : (2 : ZMod 3) * c i = 0 := by linear_combination -h2
    have h5 : c i = 0 := by
      have h6 : ∀ x : ZMod 3, 2 * x = 0 → x = 0 := by decide
      exact h6 _ h4
    exact hc0 i h5

end CFSG.StandardType.LinTwoTv

end
