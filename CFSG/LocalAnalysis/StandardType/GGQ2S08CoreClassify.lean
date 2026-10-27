module

public import CFSG.LocalAnalysis.StandardType.GGRCClassify
public import CFSG.LocalAnalysis.StandardType.GGRCSignedClass
public import CFSG.LocalAnalysis.StandardType.GGQ2S08RoCloseDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def GGReflClassLargeThree : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 3) V] [Module.Finite (ZMod 3) V] (n : ℕ),
    Module.finrank (ZMod 3) V = n → 9 ≤ n →
    ∀ A : Subgroup (V ≃ₗ[ZMod 3] V), ZS.AbsIrred 3 A →
      A = Subgroup.closure {r | r ∈ A ∧ GGLinRefl r} →
      CFSG.Quasithin.SimsG4.IsImprimitiveOnV A ∨ 3 ^ (n * (n - 1) / 2) ≤ 8 * Nat.card A ∨
        (¬ 3 ∣ n + 1 ∧ ∃ e : A ≃* Equiv.Perm (Fin (n + 1)),
          ∀ r : A, GGLinRefl (r : V ≃ₗ[ZMod 3] V) → ∃ i j, i ≠ j ∧ e r = Equiv.swap i j) ∨
        (3 ∣ n + 2 ∧ ∃ e : A ≃* Equiv.Perm (Fin (n + 2)),
          ∀ r : A, GGLinRefl (r : V ≃ₗ[ZMod 3] V) → ∃ i j, i ≠ j ∧ e r = Equiv.swap i j)

theorem GGReflClassLargeThree_of_largeInput (h : GGReflClassLargeInput') :
    GGReflClassLargeThree := by
  intro V _ _ _ n hn h9 A habs hgen
  exact h 3 (by norm_num) V n hn h9 A habs hgen

theorem ggRC_classify_frame3 (hKG : GGReflClassLargeThree) {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] {n : ℕ} (hn : Module.finrank (ZMod 3) V = n) (h9 : 9 ≤ n)
    (A : Subgroup (V ≃ₗ[ZMod 3] V)) (hirr : ZS.AbsIrred 3 A)
    (hgen : A = Subgroup.closure {r | r ∈ A ∧ GGLinRefl r})
    (hsmall : 8 * Nat.card A < 3 ^ (n * (n - 1) / 2)) :
    (∃ b : Module.Basis (Fin n) (ZMod 3) V, (∀ a, a ∈ A ↔ GGQ2S08Mono b a) ∨
        (∀ a, a ∈ A ↔ GGQ2S08MonoEven b a)) ∨
      (∃ e : A ≃* Equiv.Perm (Fin (n + 1)),
        ∀ r : A, GGLinRefl (r : V ≃ₗ[ZMod 3] V) → ∃ i j, i ≠ j ∧ e r = Equiv.swap i j) ∨
      (∃ e : A ≃* Equiv.Perm (Fin (n + 2)),
        ∀ r : A, GGLinRefl (r : V ≃ₗ[ZMod 3] V) → ∃ i j, i ≠ j ∧ e r = Equiv.swap i j) := by
  haveI : Module.Finite (ZMod 3) V := Module.finite_of_finrank_pos (by omega)
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hpm1 : ∀ c : ZMod 3, c ≠ 0 ↔ (c = 1 ∨ c = -1) := by decide
  rcases hKG V n hn h9 A hirr hgen with himp | hcard | hsym1 | hsym2
  · obtain ⟨b, hmon0⟩ := ggRC_monomial_of_imprimitive hn A hirr hgen himp
    have hmon : ∀ a ∈ A, ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod 3),
        (∀ i, c i = 1 ∨ c i = -1) ∧ ∀ i, a (b i) = c i • b (σ i) := by
      intro a ha
      obtain ⟨σ, c, hcne, hbc⟩ := hmon0 a ha
      exact ⟨σ, c, fun i => (hpm1 (c i)).1 (hcne i), hbc⟩
    refine Or.inl ⟨b, ?_⟩
    rcases ggRC_signed_class hp2 (by omega) b A hirr hgen hmon with hB | hD
    · refine Or.inl fun a => ?_
      rw [hB a]
      constructor
      · rintro ⟨σ, c, hc, h⟩
        exact ⟨σ, c, fun i => (hpm1 (c i)).2 (hc i), h⟩
      · rintro ⟨σ, c, hc, h⟩
        exact ⟨σ, c, fun i => (hpm1 (c i)).1 (hc i), h⟩
    · refine Or.inr fun a => ?_
      rw [hD a]
      constructor
      · rintro ⟨σ, c, hc, hprod, h⟩
        exact ⟨σ, c, fun i => (hpm1 (c i)).2 (hc i), hprod, h⟩
      · rintro ⟨σ, c, hc, hprod, h⟩
        exact ⟨σ, c, fun i => (hpm1 (c i)).1 (hc i), hprod, h⟩
  · exact absurd hcard (not_le.mpr hsmall)
  · obtain ⟨_, ⟨e, he⟩⟩ := hsym1
    exact Or.inr (Or.inl ⟨e, he⟩)
  · obtain ⟨_, ⟨e, he⟩⟩ := hsym2
    exact Or.inr (Or.inr ⟨e, he⟩)

end CFSG.StandardType

end
