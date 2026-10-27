module

public import CFSG.RankThree.PartOne.SEITZ12.ModuleIdent

public section

namespace CFSG.RankThree.PartOne.SEITZ12

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps
  CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution

set_option linter.unusedSectionVars false

variable {m : ℕ} {K : Type} [Field K] [Finite K] [CharP K F4.prime]

@[expose] def phi4ml_Lam (m : ℕ) (W : Subgroup (ModGL F4.tag K)) (e k l g i : K) : Prop :=
  phi4ml_vt m K e k l g i ∈ W

theorem phi4ml_vt_zero_mem (W : Subgroup (ModGL F4.tag K)) : phi4ml_Lam m W 0 0 0 0 0 := by
  rw [phi4ml_Lam, phi4ml_vt_zero]
  exact W.one_mem

theorem phi4ml_Lam_mul (hK : Nat.card K = 2 ^ (2 * m + 1)) {W : Subgroup (ModGL F4.tag K)}
    {e k l g i e' k' l' g' i' : K} (h : phi4ml_Lam m W e k l g i)
    (h' : phi4ml_Lam m W e' k' l' g' i') :
    phi4ml_Lam m W (e + e') (k + k') (l + l') (g + g') (i + i') := by
  rw [phi4ml_Lam, ← phi4ml_vt_mul hK]
  exact W.mul_mem h h'

theorem phi4ml_conj_B1_vt (hK : Nat.card K = 2 ^ (2 * m + 1)) (e k l g i : K) :
    sylowB m K 1 0 * phi4ml_vt m K e k l g i * (sylowB m K 1 0)⁻¹ =
      phi4ml_vt m K e (k + e) (l + k) (g + l + k + e)
        (i + largeReeSigma m e + largeReeSigma m k) := by
  rw [phi4ml_conj_B_vt hK 1 0 e k l g i]
  simp only [largeReeSigma_one, largeReeSigma_zero, one_mul, zero_mul, mul_zero, mul_one,
    one_pow, add_zero, zero_add]

variable {W : Subgroup (ModGL F4.tag K)}

theorem phi4ml_Lam_comm (hK : Nat.card K = 2 ^ (2 * m + 1))
    (hB : ∀ x ∈ W, sylowB m K 1 0 * x * (sylowB m K 1 0)⁻¹ ∈ W) {e k l g i : K}
    (h : phi4ml_Lam m W e k l g i) :
    phi4ml_Lam m W 0 e k (l + k + e) (largeReeSigma m e + largeReeSigma m k) := by
  have hchar : CharP K 2 := ‹CharP K F4.prime›
  have h1 := hB _ h
  rw [phi4ml_conj_B1_vt hK] at h1
  have h2 := phi4ml_Lam_mul hK h1 h
  have h2' : (2 : K) = 0 := CharTwo.two_eq_zero
  have c1 : e + e = 0 := CharTwo.add_self_eq_zero e
  have c2 : k + e + k = e := by linear_combination k * h2'
  have c3 : l + k + l = k := by linear_combination l * h2'
  have c4 : g + l + k + e + g = l + k + e := by linear_combination g * h2'
  have c5 : i + largeReeSigma m e + largeReeSigma m k + i = largeReeSigma m e + largeReeSigma m k :=
    by linear_combination i * h2'
  rw [c1, c2, c3, c4, c5] at h2
  exact h2

theorem phi4ml_Lam_Z (hH : ∀ i, sylowH m K 0 i ∈ W) (i : K) : phi4ml_Lam m W 0 0 0 0 i := by
  rw [phi4ml_Lam, phi4ml_vt_i]
  exact hH i

theorem phi4ml_Lam_descent (hK : Nat.card K = 2 ^ (2 * m + 1))
    (hB : ∀ x ∈ W, sylowB m K 1 0 * x * (sylowB m K 1 0)⁻¹ ∈ W) (hH : ∀ i, sylowH m K 0 i ∈ W)
    {e k l g i : K} (h : phi4ml_Lam m W e k l g i) (hne : e ≠ 0 ∨ k ≠ 0 ∨ l ≠ 0 ∨ g ≠ 0) :
    ∃ g₀ : K, g₀ ≠ 0 ∧ phi4ml_Lam m W 0 0 0 g₀ 0 := by
  have hchar : CharP K 2 := ‹CharP K F4.prime›
  by_cases he : e = 0
  · subst he
    by_cases hk : k = 0
    · subst hk
      by_cases hl : l = 0
      · subst hl
        have hg : g ≠ 0 := by
          rcases hne with h' | h' | h' | h'
          · exact absurd rfl h'
          · exact absurd rfl h'
          · exact absurd rfl h'
          · exact h'
        have h1 := phi4ml_Lam_mul hK h (phi4ml_Lam_Z hH i)
        rw [CharTwo.add_self_eq_zero i] at h1
        simp only [add_zero] at h1
        exact ⟨g, hg, h1⟩
      · have h1 := phi4ml_Lam_comm hK hB h
        simp only [add_zero, largeReeSigma_zero] at h1
        exact ⟨l, hl, by simpa using h1⟩
    · have h1 := phi4ml_Lam_comm hK hB h
      have h2 := phi4ml_Lam_comm hK hB h1
      simp only [add_zero, largeReeSigma_zero] at h2
      exact ⟨k, hk, by simpa using h2⟩
  · have h1 := phi4ml_Lam_comm hK hB h
    have h2 := phi4ml_Lam_comm hK hB h1
    have h3 := phi4ml_Lam_comm hK hB h2
    simp only [add_zero, largeReeSigma_zero] at h3
    exact ⟨e, he, by simpa using h3⟩

theorem phi4ml_exists_pow_two_pow (m : ℕ) (c : K) : ∃ u : K, u ^ 2 ^ m = c := by
  have hchar : CharP K 2 := ‹CharP K F4.prime›
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hinj : Function.Injective (fun u : K => u ^ 2 ^ m) := fun a b hab => by
    have := (iterateFrobenius K 2 m).injective
    exact this (by simpa [iterateFrobenius_def] using hab)
  exact Finite.surjective_of_injective hinj c

theorem phi4ml_Lam_gline
    (hTor : ∀ (u : Kˣ) (g : K), phi4ml_Lam m W 0 0 0 g 0 →
      phi4ml_Lam m W 0 0 0 ((u : K) ^ 2 ^ m * g) 0) {g₀ : K} (hg₀ : g₀ ≠ 0)
    (h : phi4ml_Lam m W 0 0 0 g₀ 0) (g : K) : phi4ml_Lam m W 0 0 0 g 0 := by
  by_cases hg : g = 0
  · subst hg
    exact phi4ml_vt_zero_mem W
  · obtain ⟨u, hu⟩ := phi4ml_exists_pow_two_pow (K := K) m (g / g₀)
    have hu0 : u ≠ 0 := by
      rintro rfl
      rw [zero_pow (by positivity)] at hu
      exact hg (by simpa [hg₀] using hu.symm)
    have := hTor (Units.mk0 u hu0) g₀ h
    simpa [hu, hg₀] using this

theorem phi4ml_Lam_kline (hK : Nat.card K = 2 ^ (2 * m + 1))
    (hB : ∀ x ∈ W, sylowB m K 1 0 * x * (sylowB m K 1 0)⁻¹ ∈ W) (hH : ∀ i, sylowH m K 0 i ∈ W)
    (hE : ∀ e : K, phi4ml_Lam m W e 0 0 0 0) (hG : ∀ g : K, phi4ml_Lam m W 0 0 0 g 0) (k : K) :
    phi4ml_Lam m W 0 k 0 0 0 := by
  have hchar : CharP K 2 := ‹CharP K F4.prime›
  have h1 := phi4ml_Lam_comm hK hB (hE k)
  have h2 := phi4ml_Lam_mul hK h1 (hG k)
  have h3 := phi4ml_Lam_mul hK h2 (phi4ml_Lam_Z hH (largeReeSigma m k + largeReeSigma m 0))
  rw [largeReeSigma_zero] at h3
  simp only [add_zero, zero_add, CharTwo.add_self_eq_zero] at h3
  exact h3

end CFSG.RankThree.PartOne.SEITZ12
