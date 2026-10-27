module

public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGTypeARowClass (p n f : ℕ) (X : LargeEvenLabel) : Prop :=
  (X = ⟨.A, n, f⟩ ∨ (n = 3 ∧ X = ⟨.D, 3, f⟩)) ∨
  (X = ⟨.A, n + 1, f⟩ ∧ p ∣ n + 2) ∨
  X = ⟨.C, n, f⟩ ∨ (X = ⟨.D, n, f⟩ ∧ 4 ≤ n) ∨ (n = 6 ∧ X = ⟨.E6, 0, f⟩) ∨
  (n = 7 ∧ X = ⟨.E7, 0, f⟩) ∨ (n = 8 ∧ p ≠ 3 ∧ X = ⟨.E8, 0, f⟩) ∨
  (n = 9 ∧ p = 3 ∧ X = ⟨.E8, 0, f⟩) ∨
  X = ⟨.twD, n + 1, f⟩ ∨
  (X.tag = .A ∧ (X.rank = 2 * n - 1 ∨ X.rank = 2 * n) ∧ 2 * X.n = f ∧ p ∣ 2 ^ X.n + 1) ∨
  (n = 3 ∧ X.tag = .twA ∧ X.rank = 5 ∧ 2 * X.n = f ∧ p ∣ 2 ^ X.n - 1) ∨
  (n = 3 ∧ f = 3 ∧ p = 7 ∧ X = ⟨.A, 8, 1⟩)

theorem not_dvd_two_pow_sub_add {p f : ℕ} (hp2 : p ≠ 2) (hp : p.Prime) (h1 : p ∣ 2 ^ f - 1)
    (h2 : p ∣ 2 ^ f + 1) : False := by
  have hpos : 1 ≤ 2 ^ f := Nat.one_le_two_pow
  have h3 : p ∣ (2 ^ f + 1) - (2 ^ f - 1) := Nat.dvd_sub h2 h1
  have h4 : (2 ^ f + 1) - (2 ^ f - 1) = 2 := by omega
  rw [h4] at h3
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h3)

theorem ggTablePRow_typeA_A {p n f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn : 3 ≤ n) (hf : 2 ≤ f)
    (hpf : p ∣ 2 ^ f - 1) {X : LargeEvenLabel} (h : GGTablePRow p ⟨.A, n - 1, f⟩ X) :
    GGTypeARowClass p n f X := by
  have e1 : n - 1 + 1 = n := by omega
  have e2 : n - 1 + 2 = n + 1 := by omega
  have e3 : n - 1 + 3 = n + 2 := by omega
  unfold GGTablePRow at h
  simp only [reduceCtorEq, false_and, or_false, LargeEvenLabel.mk.injEq, e1, e2, e3] at h
  unfold GGTypeARowClass
  rcases h with ⟨-, -, -, h⟩ | ⟨-, h2, -, -⟩ | ⟨⟨-, h1, h2⟩, h3, h4⟩ | ⟨⟨-, h1, h2⟩, h3, h4⟩ |
    ⟨⟨-, h1, h2⟩, -, -⟩ | ⟨⟨-, h1, h2⟩, -, -⟩
  · rcases h with h | ⟨h, h'⟩ | h | h | h | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h3, h2⟩ | ⟨h1, h3, h2⟩ |
      ⟨h1, h2, h3, h4, h5⟩ | h
    · exact Or.inl (Or.inl h)
    · right; left; exact ⟨h, h'⟩
    · iterate 2 right
      left; exact h
    · by_cases h3 : n = 3
      · subst h3
        exact Or.inl (Or.inr ⟨rfl, h⟩)
      · iterate 3 right
        left; exact ⟨h, by omega⟩
    · iterate 8 right
      left; exact h
    · iterate 4 right
      left; exact ⟨by omega, h2⟩
    · iterate 5 right
      left; exact ⟨by omega, h2⟩
    · iterate 6 right
      left; exact ⟨by omega, h3, h2⟩
    · iterate 7 right
      left; exact ⟨by omega, h3, h2⟩
    · iterate 10 right
      left; exact ⟨by omega, h2, h3, h4, h5⟩
    · iterate 9 right
      left
      refine ⟨h.1, ?_, h.2.2.1, h.2.2.2⟩
      omega
  · exact (not_dvd_two_pow_sub_add hp2 hp hpf h2).elim
  · iterate 11 right
    exact ⟨by omega, by omega, h3, h4⟩
  · iterate 9 right
    left
    subst h4
    refine ⟨rfl, Or.inl ?_, ?_, ?_⟩
    · show 5 = 2 * n - 1
      omega
    · show 2 * 2 = f
      omega
    · subst h3
      decide
  · omega
  · omega

theorem ggTablePRow_typeA_D3 {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 2 ≤ f)
    (hpf : p ∣ 2 ^ f - 1) {X : LargeEvenLabel} (h : GGTablePRow p ⟨.D, 3, f⟩ X) :
    GGTypeARowClass p 4 f X := by
  unfold GGTablePRow at h
  simp only [reduceCtorEq, false_and, and_false, or_false, false_or, LargeEvenLabel.mk.injEq,
    Nat.reduceAdd, Nat.reduceEqDiff, true_and] at h
  unfold GGTypeARowClass
  rcases h with ⟨-, h⟩ | ⟨h2, -⟩
  · iterate 3 right
    left; exact ⟨h, le_refl 4⟩
  · exact (not_dvd_two_pow_sub_add hp2 hp hpf h2).elim

theorem ggTablePRow_typeA {p n f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn : 3 ≤ n) (hf : 2 ≤ f)
    (hpf : p ∣ 2 ^ f - 1) {J X : LargeEvenLabel}
    (hJ : J = ⟨.A, n - 1, f⟩ ∨ (n = 4 ∧ J = ⟨.D, 3, f⟩)) (h : GGTablePRow p J X) :
    GGTypeARowClass p n f X := by
  rcases hJ with rfl | ⟨rfl, rfl⟩
  · exact ggTablePRow_typeA_A hp hp2 hn hf hpf h
  · exact ggTablePRow_typeA_D3 hp hp2 hf hpf h

end CFSG.StandardType

end
