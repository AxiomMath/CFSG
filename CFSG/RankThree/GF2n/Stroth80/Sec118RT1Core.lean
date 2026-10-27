module

public import CFSG.ClassicalGroups.Symplectic.TensorK2Count
public import CFSG.RankThree.GF2n.Stroth80.Sec83Card

public section

namespace CFSG.ClassicalGroups.Symplectic

open CFSG.Open Matrix

variable {K : Type} [Field K] [Finite K] [CharP K 2] {m n : ℕ} {E : Type*} [AddCommGroup E]
  [Module K E] [Finite E] {D : Type*} [Group D] [Finite D]

theorem rt1_core (hm : 2 ≤ m) (hq : 2 < Nat.card K) (hn : 2 * m ≤ n)
    (ι₁ ι₂ : (Fin m ⊕ Fin m → K) →ₗ[K] E) {u : Fin m ⊕ Fin m → K} (hu : u ≠ 0)
    {k₀ k₁ : Fin 2 → K} (hk : detFin2 k₀ k₁ = 1)
    (T : D →* (E ≃ₗ[K] E)) (S : D →* GL (Fin m ⊕ Fin m) K) (H : D →* GL (Fin 2) K)
    (hT : ∀ (d : D) (x : Fin m ⊕ Fin m → K) (k : Fin 2 → K), T d (tensorK2 ι₁ ι₂ x k) =
      tensorK2 ι₁ ι₂ ((S d : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ x)
        ((H d : Matrix (Fin 2) (Fin 2) K) *ᵥ k))
    (hSu : ∀ d : D, (S d : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ u = u)
    (hHk₀ : ∀ d : D, (H d : Matrix (Fin 2) (Fin 2) K) *ᵥ k₀ = k₀)
    (hHk₁ : ∀ d : D, ∃ t : K, (H d : Matrix (Fin 2) (Fin 2) K) *ᵥ k₁ = k₁ + t • k₀)
    (Dq : Subgroup D) (hDq : ∀ d : D, d ∈ Dq ↔ (S d = 1 ∧ H d = 1))
    (hLu : ∀ d : D, H d = 1 → S d ∈ LspGL m K u)
    (hdich : (∀ d : D, H d = 1 → ∃ c : K, ∀ v : Fin m ⊕ Fin m → K,
        (S d : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ v = v + (c * spForm m K v u) • u) ∨
      (∀ g ∈ LspGL m K u, ∃ d : D, H d = 1 ∧ S d = g))
    (Yp V : AddSubgroup E)
    (hdec : ∀ v : E, ∃ (x₀ x₁ : Fin m ⊕ Fin m → K) (z : E), z ∈ Yp ∧
      v = tensorK2 ι₁ ι₂ x₀ k₀ + tensorK2 ι₁ ι₂ x₁ k₁ + z)
    (hYp : ∀ (x₀ x₁ : Fin m ⊕ Fin m → K) (z : E), z ∈ Yp →
      tensorK2 ι₁ ι₂ x₀ k₀ + tensorK2 ι₁ ι₂ x₁ k₁ + z = 0 → x₀ = 0 ∧ x₁ = 0)
    (hTYp : ∀ d : D, ∀ z ∈ Yp, T d z = z)
    (hV1 : ∀ d : D, ∀ v ∈ V, ∃ s : K, T d v - v = s • tensorK2 ι₁ ι₂ u k₀)
    (hV2 : ∀ (d : D) (x : Fin m ⊕ Fin m → K) (k : Fin 2 → K), spForm m K x u = 0 →
      T d (tensorK2 ι₁ ι₂ x k) - tensorK2 ι₁ ι₂ x k ∈ V)
    (hV3 : ∀ v ∈ V, (∀ d : D, T d v = v) → ∃ s : K, v = s • tensorK2 ι₁ ι₂ u k₀)
    (hcnt : Nat.card D * (Nat.card K * Nat.card V) = Nat.card Dq * Nat.card K ^ (2 * n))
    (hge : Nat.card Dq * Nat.card K ^ (n - 1) ≤ Nat.card D) : False := by
  classical
  have hq2 : 2 ≤ Nat.card K := hq.le
  have hind0 : ∀ (x₀ x₁ : Fin m ⊕ Fin m → K),
      tensorK2 ι₁ ι₂ x₀ k₀ + tensorK2 ι₁ ι₂ x₁ k₁ = 0 → x₀ = 0 ∧ x₁ = 0 := fun x₀ x₁ h =>
    hYp x₀ x₁ 0 Yp.zero_mem (by rw [add_zero]; exact h)
  have hDqpos : 0 < Nat.card Dq := Nat.card_pos
  have hcount := card_eq_card_mul_card_map_mul_card_range S H Dq hDq
  have hrle : Nat.card H.range ≤ Nat.card K :=
    card_le_of_unipotent_subgroup hk H.range (by
      rintro _ ⟨d, rfl⟩
      exact ⟨hHk₀ d, hHk₁ d⟩)
  rcases hdich with h1 | h2
  · have ha : Nat.card (Subgroup.map S H.ker) ≤ Nat.card K := by
      refine card_le_of_transvection_subgroup u _ ?_
      rintro g ⟨d, hd, rfl⟩
      exact h1 d (MonoidHom.mem_ker.mp hd)
    rw [hcount] at hge
    exact rt1_arith_one hDqpos hq2 hm hn ha hrle hge
  · have hmap : Subgroup.map S H.ker = LspGL m K u := by
      apply le_antisymm
      · rintro _ ⟨d, hd, rfl⟩
        exact hLu d (MonoidHom.mem_ker.mp hd)
      · intro g hg
        obtain ⟨d, hHd, hSd⟩ := h2 g hg
        exact ⟨d, MonoidHom.mem_ker.mpr hHd, hSd⟩
    have ha : Nat.card (Subgroup.map S H.ker) = Nat.card K ^ (2 * m - 1) := by
      rw [hmap]
      exact card_LspGL hu
    have hVup := card_le_pow_of_decomp hm ι₁ ι₂ hu T S H hT h2 Yp V hdec hYp hTYp hV1 hV3
    by_cases hr1 : Nat.card H.range = 1
    · have hHtriv : ∀ d : D, H d = 1 := by
        intro d
        have hbot : H.range = ⊥ := Subgroup.card_eq_one.mp hr1
        have hd : H d ∈ H.range := ⟨d, rfl⟩
        rw [hbot] at hd
        exact Subgroup.mem_bot.mp hd
      exact false_of_H_trivial hm ι₁ ι₂ hu T S H hT h2 hSu hHtriv V hV2 hV3 hind0
    · have hrpos : 0 < Nat.card H.range := Nat.card_pos
      have hr2 : 2 ≤ Nat.card H.range := by omega
      obtain ⟨d₁, hd₁⟩ : ∃ d : D, H d ≠ 1 := by
        by_contra hcon
        push Not at hcon
        apply hr1
        rw [Subgroup.card_eq_one, eq_bot_iff]
        rintro _ ⟨d, rfl⟩
        exact Subgroup.mem_bot.mpr (hcon d)
      obtain ⟨t, ht⟩ := hHk₁ d₁
      have ht0 : t ≠ 0 := by
        rintro rfl
        apply hd₁
        have h3 : (H d₁ : Matrix (Fin 2) (Fin 2) K) = 1 :=
          eq_one_of_mulVec_basis_two hk _ (hHk₀ d₁) (by rw [ht, zero_smul, add_zero])
        exact Units.ext h3
      have hVlow := pow_le_card_of_translate hm ι₁ ι₂ hu T S H hT h2 V hV2 hind0 ht0 ht
      refine rt1_arith_two hDqpos hq2 (by omega) hn hr2 hrle hVup hVlow ?_
      rw [hcount, ha] at hcnt
      exact hcnt

end CFSG.ClassicalGroups.Symplectic
