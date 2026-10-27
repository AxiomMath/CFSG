module

public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotAutUBasic

public section

namespace CFSG.SeitzReduction.UnitaryPilot

open Matrix Subgroup CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ComponentClassification.OuterAutomorphisms CFSG.ComponentClassification CFSG.LinearGroups

variable {f : ℕ} {K : Type} [Field K] {n : ℕ}

theorem autU_pow_of_mulEquiv {X Y : Type*} [Group X] [Group Y] [Finite X] (e : X ≃* Y)
    (hY : ∀ (U : Sylow 2 Y) (β : MulAut Y) (k : ℕ), β ^ 2 ^ k = 1 →
      (∀ u ∈ (U : Subgroup Y), β u = u) → β ∈ inner Y)
    (U : Sylow 2 X) (β : MulAut X) (k : ℕ) (hβk : β ^ 2 ^ k = 1)
    (hβ : ∀ u ∈ (U : Subgroup X), β u = u) : β ∈ inner X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set U' : Sylow 2 Y := U.mapSurjective (f := e.toMonoidHom) e.surjective with hU'
  have hmem : ∀ x : X, x ∈ (U : Subgroup X) → e x ∈ (U' : Subgroup Y) := fun x hx =>
    ⟨x, hx, rfl⟩
  have hU'mem : ∀ y ∈ (U' : Subgroup Y), ∃ x ∈ (U : Subgroup X), e x = y := by
    rintro y ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩
  have hβ'k : MulAut.congr e β ^ 2 ^ k = 1 := by rw [← map_pow, hβk, map_one]
  obtain ⟨y, hy⟩ := hY U' (MulAut.congr e β) k hβ'k fun u hu => by
    obtain ⟨x, hx, rfl⟩ := hU'mem u hu
    simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply, hβ x hx]
  refine ⟨e.symm y, (MulAut.congr e).injective ?_⟩
  rw [congr_conj, MulEquiv.apply_symm_apply, hy]

section Plane

variable (h : UnitaryFieldData 2 f K)

theorem gramForm_one_eq :
    gramForm h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = stdHermForm h n := by
  rw [Units.val_one, stdHermForm_eq_gramForm]

@[expose] def isoPairVec (i j : Fin n) : Fin n → K :=
  Pi.single i 1 + Pi.single j 1

theorem stdHermForm_isoPairVec (i j : Fin n) (y : Fin n → K) :
    stdHermForm h n (isoPairVec i j) y = y i + y j := by
  rw [isoPairVec, map_add, LinearMap.add_apply, stdHermForm_single, stdHermForm_single]

theorem stdHermForm_isoPairVec_self {i j : Fin n} (hij : i ≠ j) :
    stdHermForm h n (isoPairVec i j) (isoPairVec i j) = 0 := by
  have : CharP K 2 := h.charP
  rw [stdHermForm_isoPairVec]
  simp only [isoPairVec, Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hij,
    Pi.single_eq_of_ne hij.symm, add_zero, zero_add, CharTwo.add_self_eq_zero]

theorem stdHermForm_isoPairVec_isoPairVec {i j k l : Fin n} (hki : k ≠ i) (hkj : k ≠ j) (hli : l ≠ i)
    (hlj : l ≠ j) : stdHermForm h n (isoPairVec i j) (isoPairVec k l) = 0 := by
  rw [stdHermForm_isoPairVec]
  simp only [isoPairVec, Pi.add_apply, Pi.single_eq_of_ne hki.symm, Pi.single_eq_of_ne hli.symm,
    Pi.single_eq_of_ne hkj.symm, Pi.single_eq_of_ne hlj.symm, add_zero]

@[expose] noncomputable def planeTwo (hn : 4 ≤ n) : Submodule K (Fin n → K) :=
  Submodule.span K {isoPairVec ⟨0, by omega⟩ ⟨1, by omega⟩, isoPairVec ⟨2, by omega⟩ ⟨3, by omega⟩}

theorem isTotIso_planeTwo (hn : 4 ≤ n) :
    ∀ x ∈ planeTwo (K := K) hn, ∀ y ∈ planeTwo (K := K) hn,
      gramForm h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) x y = 0 := by
  have h01 : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  have h23 : (⟨2, by omega⟩ : Fin n) ≠ ⟨3, by omega⟩ := by simp [Fin.ext_iff]
  have h20 : (⟨2, by omega⟩ : Fin n) ≠ ⟨0, by omega⟩ := by simp [Fin.ext_iff]
  have h21 : (⟨2, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  have h30 : (⟨3, by omega⟩ : Fin n) ≠ ⟨0, by omega⟩ := by simp [Fin.ext_iff]
  have h31 : (⟨3, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  have hvv := stdHermForm_isoPairVec_self h (K := K) h01
  have hww := stdHermForm_isoPairVec_self h (K := K) h23
  have hvw := stdHermForm_isoPairVec_isoPairVec h (K := K) h20 h21 h30 h31
  have hwv := stdHermForm_isoPairVec_isoPairVec h (K := K) h20.symm h30.symm h21.symm h31.symm
  intro x hx y hy
  rw [gramForm_one_eq]
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.1 hx
  obtain ⟨c, d, rfl⟩ := Submodule.mem_span_pair.1 hy
  simp only [map_add, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hvv,
    hww, hvw, hwv, mul_zero, add_zero]

theorem planeTwo_independent (hn : 4 ≤ n) (a b : K)
    (hab : a • isoPairVec (K := K) (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩ +
      b • isoPairVec (⟨2, by omega⟩ : Fin n) ⟨3, by omega⟩ = 0) : a = 0 ∧ b = 0 := by
  have h01 : (⟨1, by omega⟩ : Fin n) ≠ ⟨0, by omega⟩ := by simp [Fin.ext_iff]
  have h20 : (⟨2, by omega⟩ : Fin n) ≠ ⟨0, by omega⟩ := by simp [Fin.ext_iff]
  have h30 : (⟨3, by omega⟩ : Fin n) ≠ ⟨0, by omega⟩ := by simp [Fin.ext_iff]
  have h02 : (⟨0, by omega⟩ : Fin n) ≠ ⟨2, by omega⟩ := by simp [Fin.ext_iff]
  have h12 : (⟨1, by omega⟩ : Fin n) ≠ ⟨2, by omega⟩ := by simp [Fin.ext_iff]
  have h32 : (⟨3, by omega⟩ : Fin n) ≠ ⟨2, by omega⟩ := by simp [Fin.ext_iff]
  have e0 := congrFun hab ⟨0, by omega⟩
  have e2 := congrFun hab ⟨2, by omega⟩
  simp only [isoPairVec, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_eq_same,
    Pi.single_eq_of_ne h01.symm, Pi.single_eq_of_ne h20.symm, Pi.single_eq_of_ne h30.symm,
    Pi.single_eq_of_ne h02.symm, Pi.single_eq_of_ne h12.symm, Pi.single_eq_of_ne h32.symm,
    Pi.zero_apply, mul_one, mul_zero, add_zero, zero_add] at e0 e2
  exact ⟨e0, e2⟩

end Plane

section AutU

variable (h : UnitaryFieldData 2 f K)

theorem finite_primeFormP (C : Matrix (Fin n) (Fin n) K) : Finite (primeFormP h C) := by
  have := h.finite
  infer_instance

theorem finite_unitaryPSU (n : ℕ) : Finite (unitaryPSU h n) := by
  have := h.finite
  infer_instance

theorem mem_inner_of_fix_sylow_of_pow_primeFormOne (hn : 4 ≤ n)
    (U : Sylow 2 (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)))
    (β : MulAut (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) (k : ℕ)
    (hβk : β ^ 2 ^ k = 1)
    (hβ : ∀ u ∈ (U : Subgroup (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))),
      β u = u) :
    β ∈ inner (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := finite_primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
  obtain ⟨x, hx⟩ := exists_conj_mem_sylow_of_isPGroup
    (isPGroup_map_radical h (C := (1 : GL (Fin n) K)) (planeTwo hn)) U
  set β' := (MulAut.conj x)⁻¹ * β * (MulAut.conj x)⁻¹⁻¹ with hβ'
  have hβ'k : β' ^ 2 ^ k = 1 := by
    rw [hβ', conj_pow, hβk, mul_one, mul_inv_cancel]
  have hfix : ∀ g ∈ isotropicRadical h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
      (planeTwo hn), β' (g : primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) = g := by
    intro g hg
    have hxg := hβ _ (hx _ (mem_map_of_mem _ hg))
    rw [QuotientGroup.mk'_apply] at hxg
    rw [hβ', inv_inv, MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, hxg,
      MulAut.conj_inv_apply]
    group
  have hβ'i := mem_inner_of_fix_radical_of_pow h (isPrimeFormGram_one (K := K)) (by omega)
    (by omega) (isTotIso_planeTwo h hn) (Submodule.subset_span (by simp))
    (Submodule.subset_span (by simp)) (planeTwo_independent hn) hβ'k hfix
  have e : β = MulAut.conj x * β' * (MulAut.conj x)⁻¹ := by
    rw [hβ', inv_inv]
    group
  rw [e]
  exact mul_mem (mul_mem ⟨x, rfl⟩ hβ'i) (inv_mem ⟨x, rfl⟩)

theorem mem_range_conj_of_fix_sylow_of_pow (hn : 4 ≤ n) (U : Sylow 2 (unitaryPSU h n))
    (β : MulAut (unitaryPSU h n)) (k : ℕ) (hβk : β ^ 2 ^ k = 1)
    (hβ : ∀ u ∈ (U : Subgroup (unitaryPSU h n)), β u = u) :
    β ∈ (MulAut.conj : unitaryPSU h n →* MulAut (unitaryPSU h n)).range := by
  have := finite_unitaryPSU h n
  exact autU_pow_of_mulEquiv (OutcomeLocal.primeFormOneEquiv h n).symm
    (mem_inner_of_fix_sylow_of_pow_primeFormOne h hn) U β k hβk hβ

theorem mem_range_conj_of_fix_sylow_of_sq_of_mulEquiv {X : Type*} [Group X]
    (e : X ≃* unitaryPSU h n) (hn : 4 ≤ n) (U : Sylow 2 X) (β : MulAut X) (hβ2 : β ^ 2 = 1)
    (hβ : ∀ u ∈ (U : Subgroup X), β u = u) : β ∈ (MulAut.conj : X →* MulAut X).range := by
  have := finite_unitaryPSU h n
  have : Finite X := Finite.of_equiv _ e.symm.toEquiv
  exact autU_pow_of_mulEquiv e (fun U β k hβk hβ => mem_range_conj_of_fix_sylow_of_pow h hn U β k
    hβk hβ) U β 1 (by rw [pow_one]; exact hβ2) hβ

end AutU

end CFSG.SeitzReduction.UnitaryPilot
