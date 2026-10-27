module

public import CFSG.LocalAnalysis.StandardType.GGResKnownGroup
public import CFSG.LocalAnalysis.StandardType.GGRCMonomial
public import CFSG.LocalAnalysis.StandardType.GGRCLinWeyl

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem l05nK8_zmod_three_pm1 : ∀ c : ZMod 3, c ≠ 0 → c = 1 ∨ c = -1 := by
  decide

private theorem l05nK8_prime_eq_three_or_five_le {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    p = 3 ∨ 5 ≤ p := by
  have hpge2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have h2or : p = 2 ∨ 3 ≤ p := by omega
  rcases h2or with h | h
  · exact absurd h hp2
  · by_cases h5 : 5 ≤ p
    · exact Or.inr h5
    · left
      have hp_le4 : p ≤ 4 := by omega
      interval_cases p
      · rfl
      · exact absurd (Fact.out : Nat.Prime 4) (by norm_num)

theorem ggRC_classify (hKG : GGReflClassLargeInput') {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] {n : ℕ}
    (hn : Module.finrank (ZMod p) V = n) (h9 : 9 ≤ n)
    (A : Subgroup (V ≃ₗ[ZMod p] V)) (hirr : ZS.AbsIrred p A)
    (hgen : A = Subgroup.closure {r | r ∈ A ∧ GGLinRefl r})
    (hsmall : 8 * Nat.card A < p ^ (n * (n - 1) / 2))
    (hpm1 : 5 ≤ p → ∀ f : Module.Basis (Fin n) (ZMod p) V,
      (∀ a ∈ A, ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p),
        (∀ i, c i ≠ 0) ∧ ∀ i, a (f i) = c i • f (σ i)) →
      ∃ b' : Module.Basis (Fin n) (ZMod p) V, ∀ a ∈ A,
        ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p),
          (∀ i, c i = 1 ∨ c i = -1) ∧ ∀ i, a (b' i) = c i • b' (σ i)) :
    ZS.LinWeyl p A ∨ ∃ (N : ℕ) (_ : 3 ≤ N) (e : A ≃* Equiv.Perm (Fin N)),
      ∀ r : A, GGLinRefl (r : V ≃ₗ[ZMod p] V) → ∃ i j, i ≠ j ∧ e r = Equiv.swap i j := by
  haveI : Module.Finite (ZMod p) V := Module.finite_of_finrank_pos (by omega)
  rcases hKG p hp2 V n hn h9 A hirr hgen with himp | hcard | hsym1 | hsym2
  · obtain ⟨b, hmon0⟩ := ggRC_monomial_of_imprimitive hn A hirr hgen himp
    rcases l05nK8_prime_eq_three_or_five_le hp2 with hp3 | hp5
    · subst hp3
      have hmon : ∀ a ∈ A, ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod 3),
          (∀ i, c i = 1 ∨ c i = -1) ∧ ∀ i, a (b i) = c i • b (σ i) := by
        intro a ha
        obtain ⟨σ, c, hcne, hbc⟩ := hmon0 a ha
        exact ⟨σ, c, fun i => l05nK8_zmod_three_pm1 (c i) (hcne i), hbc⟩
      exact Or.inl (ggRC_linWeyl_of_monomial_pm1 hp2 (by omega) b A hirr hgen hmon)
    · obtain ⟨b', hmon'⟩ := hpm1 hp5 b hmon0
      exact Or.inl (ggRC_linWeyl_of_monomial_pm1 hp2 (by omega) b' A hirr hgen hmon')
  · exact absurd hcard (not_le.mpr hsmall)
  · obtain ⟨_, ⟨e, he⟩⟩ := hsym1
    exact Or.inr ⟨n + 1, by omega, e, he⟩
  · obtain ⟨_, ⟨e, he⟩⟩ := hsym2
    exact Or.inr ⟨n + 2, by omega, e, he⟩

end CFSG.StandardType
