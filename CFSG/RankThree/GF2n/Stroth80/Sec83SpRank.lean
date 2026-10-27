module

public import CFSG.Assembly.Defs
public import CFSG.ClassicalGroups.Symplectic.StandardForm

public section

namespace CFSG.ClassicalGroups.Symplectic

open CFSG.ClassicalGroups.Alternating CFSG.Open
open Matrix

theorem card_range_sub_one_of_mem_LspGL {m : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {u : Fin m ⊕ Fin m → K} (hu : u ≠ 0) {A : GL (Fin m ⊕ Fin m) K} (hA : A ∈ LspGL m K u)
    (hA1 : A ≠ 1) :
    (Nat.card (LinearMap.range
        (Matrix.toLin' ((A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) - 1))) = Nat.card K ∨
      Nat.card (LinearMap.range
        (Matrix.toLin' ((A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) - 1))) =
          Nat.card K ^ 2) ∧
    ((¬ ∃ y : Fin m ⊕ Fin m → K,
        spForm m K y ((A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ y) ≠ 0) →
      Nat.card (LinearMap.range
        (Matrix.toLin' ((A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) - 1))) =
          Nat.card K ^ 2) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hBn : (spForm m K).Nondegenerate := spForm_nondegenerate
  obtain ⟨-, w, c, -, hM⟩ := mem_LspGL_iff_siegel.mp hA
  obtain ⟨N, hNdef⟩ : ∃ N : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K,
      N = (A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) - 1 := ⟨_, rfl⟩
  rw [← hNdef]
  have hN : ∀ x : Fin m ⊕ Fin m → K,
      N *ᵥ x = spForm m K x u • w + (spForm m K x w + c * spForm m K x u) • u := by
    intro x
    rw [hNdef, Matrix.sub_mulVec, Matrix.one_mulVec, hM x]
    module
  have hN0 : N ≠ 0 := by
    intro h
    rw [hNdef] at h
    apply hA1
    apply Units.ext
    rw [Units.val_one]
    exact sub_eq_zero.mp h
  obtain ⟨R, hR⟩ : ∃ R : Submodule K (Fin m ⊕ Fin m → K),
      R = LinearMap.range (Matrix.toLin' N) := ⟨_, rfl⟩
  rw [← hR]
  have hmemR : ∀ y : Fin m ⊕ Fin m → K, y ∈ R ↔
      ∃ x : Fin m ⊕ Fin m → K, N *ᵥ x = y := by
    intro y
    rw [hR, LinearMap.mem_range]
    simp only [Matrix.toLin'_apply]
  have hR_ne : R ≠ ⊥ := by
    intro h
    rw [hR, LinearMap.range_eq_bot] at h
    exact hN0 (Matrix.toLin'.injective (by rw [h, map_zero]))
  have hR1 : 1 ≤ Module.finrank K R := Submodule.one_le_finrank_iff.mpr hR_ne
  obtain ⟨S, hS⟩ : ∃ S : Submodule K (Fin m ⊕ Fin m → K),
      S = Submodule.span K (Set.range ![u, w]) := ⟨_, rfl⟩
  have hRS : R ≤ S := by
    intro y hy
    obtain ⟨x, rfl⟩ := (hmemR y).mp hy
    rw [hS, hN x]
    refine Submodule.add_mem _ (Submodule.smul_mem _ _ ?_) (Submodule.smul_mem _ _ ?_)
    · exact Submodule.subset_span ⟨1, by simp⟩
    · exact Submodule.subset_span ⟨0, by simp⟩
  have hRfin : Module.finrank K R ≤ 2 := by
    have hS2 : Module.finrank K S ≤ 2 := by
      rw [hS]
      have h := finrank_range_le_card (R := K) ![u, w]
      rw [Fintype.card_fin] at h
      exact h
    exact (Submodule.finrank_mono hRS).trans hS2
  refine ⟨?_, ?_⟩
  · rw [Module.natCard_eq_pow_finrank (K := K)]
    have h12 : Module.finrank K R = 1 ∨ Module.finrank K R = 2 := by omega
    rcases h12 with h | h
    · left
      rw [h, pow_one]
    · right
      rw [h]
  · intro hno
    push Not at hno
    have hc : c = 0 := by
      obtain ⟨y, hy⟩ : ∃ y : Fin m ⊕ Fin m → K, spForm m K u y ≠ 0 := by
        by_contra hcon
        push Not at hcon
        exact hu (hBn.1 u hcon)
      have hyu : spForm m K y u ≠ 0 := by
        rw [← spForm_isAlt.neg_eq u y]
        exact neg_ne_zero.mpr hy
      have h1 := hno y
      rw [hM y] at h1
      simp only [map_add, map_smul, smul_eq_mul, spForm_self] at h1
      have h3 : c * spForm m K y u ^ 2 = 0 := by
        linear_combination h1 - (spForm m K y u * spForm m K y w) * h2
      exact (mul_eq_zero.mp h3).resolve_right (pow_ne_zero 2 hyu)
    have hN2 : ∀ x : Fin m ⊕ Fin m → K,
        N *ᵥ x = spForm m K x u • w + spForm m K x w • u := by
      intro x
      rw [hN x, hc, zero_mul, add_zero]
    have hwr : ∀ r : K, w ≠ r • u := by
      intro r hr
      apply hN0
      refine Matrix.toLin'.injective (LinearMap.ext fun x => ?_)
      simp only [Matrix.toLin'_apply, Matrix.zero_mulVec]
      rw [hN2 x, hr, map_smul, smul_eq_mul]
      have e : spForm m K x u • (r • u) + (r * spForm m K x u) • u =
          (2 * (r * spForm m K x u)) • u := by
        module
      rw [e, h2, zero_mul, zero_smul]
    have hli : ∀ s t : K, s • u + t • w = 0 → s = 0 ∧ t = 0 := by
      intro s t h
      by_cases ht : t = 0
      · rw [ht, zero_smul, add_zero] at h
        exact ⟨(smul_eq_zero.mp h).resolve_right hu, ht⟩
      · exfalso
        apply hwr (-(t⁻¹ * s))
        have h' : t • w = -(s • u) := by
          rw [← sub_eq_zero, sub_neg_eq_add, add_comm]
          exact h
        calc w = t⁻¹ • (t • w) := by rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
          _ = t⁻¹ • (-(s • u)) := by rw [h']
          _ = (-(t⁻¹ * s)) • u := by module
    have hsep : ∀ G : Module.Dual K (Fin m ⊕ Fin m → K), ∃ x : Fin m ⊕ Fin m → K,
        ∀ y : Fin m ⊕ Fin m → K, spForm m K x y = G y := by
      intro G
      refine ⟨((spForm m K).toDual hBn).symm G, fun y => ?_⟩
      rw [← LinearMap.BilinForm.toDual_def hBn, LinearEquiv.apply_symm_apply]
    obtain ⟨f, hf⟩ : ∃ f : (Fin 2 → K) →ₗ[K] (Fin m ⊕ Fin m → K),
        ∀ v : Fin 2 → K, f v = v 0 • u + v 1 • w :=
      ⟨(LinearMap.proj (0 : Fin 2) : (Fin 2 → K) →ₗ[K] K).smulRight u +
        (LinearMap.proj (1 : Fin 2) : (Fin 2 → K) →ₗ[K] K).smulRight w, fun v => rfl⟩
    obtain ⟨π₀, hπ₀⟩ : ∃ π : (Fin 2 → K) →ₗ[K] K,
        ∀ v : Fin 2 → K, π v = v 0 :=
      ⟨LinearMap.proj 0, fun v => rfl⟩
    obtain ⟨π₁, hπ₁⟩ : ∃ π : (Fin 2 → K) →ₗ[K] K,
        ∀ v : Fin 2 → K, π v = v 1 :=
      ⟨LinearMap.proj 1, fun v => rfl⟩
    have hker : LinearMap.ker f = ⊥ := by
      rw [LinearMap.ker_eq_bot']
      intro v hv
      rw [hf] at hv
      obtain ⟨h0, h1⟩ := hli (v 0) (v 1) hv
      funext i
      fin_cases i
      · simpa using h0
      · simpa using h1
    obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective f hker
    have e1 : f ![1, 0] = u := by
      rw [hf]
      simp
    have e2 : f ![0, 1] = w := by
      rw [hf]
      simp
    have hg1 : g u = ![1, 0] := by
      rw [← e1]
      exact LinearMap.congr_fun hg ![1, 0]
    have hg2 : g w = ![0, 1] := by
      rw [← e2]
      exact LinearMap.congr_fun hg ![0, 1]
    have hdual : ∀ p q : K,
        ∃ G : Module.Dual K (Fin m ⊕ Fin m → K), G u = p ∧ G w = q := by
      intro p q
      refine ⟨(p • π₀ + q • π₁).comp g, ?_, ?_⟩
      · simp [hg1, hπ₀, hπ₁]
      · simp [hg2, hπ₀, hπ₁]
    obtain ⟨G₁, hG₁u, hG₁w⟩ := hdual 1 0
    obtain ⟨x₁, hx₁⟩ := hsep G₁
    obtain ⟨G₂, hG₂u, hG₂w⟩ := hdual 0 1
    obtain ⟨x₂, hx₂⟩ := hsep G₂
    have hu_mem : u ∈ R := by
      refine (hmemR u).mpr ⟨x₂, ?_⟩
      rw [hN2 x₂, hx₂ u, hx₂ w, hG₂u, hG₂w, zero_smul, one_smul, zero_add]
    have hw_mem : w ∈ R := by
      refine (hmemR w).mpr ⟨x₁, ?_⟩
      rw [hN2 x₁, hx₁ u, hx₁ w, hG₁u, hG₁w, zero_smul, one_smul, add_zero]
    have hSR : S ≤ R := by
      rw [hS, Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      fin_cases i
      · simpa using hu_mem
      · simpa using hw_mem
    have hRS' : R = S := le_antisymm hRS hSR
    have hli2 : LinearIndependent K ![u, w] := LinearIndependent.pair_iff.mpr hli
    have hR2 : Module.finrank K R = 2 := by
      rw [hRS', hS, finrank_span_eq_card hli2, Fintype.card_fin]
    rw [Module.natCard_eq_pow_finrank (K := K), hR2]

end CFSG.ClassicalGroups.Symplectic
