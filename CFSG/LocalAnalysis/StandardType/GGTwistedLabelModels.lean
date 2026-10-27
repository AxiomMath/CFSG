module

public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.LocalAnalysis.StandardType.MarkingClassical

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank

theorem statedClassicalModel_of_hasLabel_typeTwA {X : Type} [Group X] {n f : ℕ}
    (hΛ : LargeEvenInLambda2 ⟨.twA, n, f⟩) (hX : GGHasLabel ⟨.twA, n, f⟩ X) :
    StatedClassicalModel X .PSU (n + 1) 2 f := by
  obtain ⟨K, hF, hfin, hK, ⟨e⟩⟩ := hX
  have hf : 1 ≤ f := hΛ.1
  have hn : 2 ≤ n := hΛ.2.1
  have hn2 : n = 2 → 2 ≤ f := hΛ.2.2
  have hadm : StatedLieAdmissible .PSU (n + 1) 2 f := by
    refine ⟨Nat.prime_two, hf, by omega, ?_⟩
    intro h
    have h1 : n + 1 = 3 := (Prod.mk.inj h).1
    have h2 : 2 ^ f = 2 := (Prod.mk.inj h).2
    have h3 : 2 ≤ f := hn2 (by omega)
    have h4 : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) h3
    omega
  exact ⟨hadm, K, hF, hfin, hK, ⟨e⟩⟩

theorem statedClassicalModel_of_hasLabel_typeD {X : Type} [Group X] {n f : ℕ} (hn : 4 ≤ n)
    (hX : GGHasLabel ⟨.D, n, f⟩ X) : CFSG.Open.StatedClassicalModel X .POmegaPlus n 2 f := by
  have h2 : ¬ n = 2 := by omega
  have h3 : ¬ n = 3 := by omega
  have hX' : LargeEvenRecipeOmegaPlus n (2 ^ f)
      (fun R' _ _ _ => Nonempty (X ≃* R')) := by
    simpa only [GGHasLabel, LargeEvenRawDatum, if_neg h2, if_neg h3] using hX
  obtain ⟨K, hF, hfin, hK, ⟨e⟩⟩ := hX'
  have hf : 1 ≤ f := by
    have hK' : Field K := hF
    have hfin' : Finite K := hfin
    have hcard : 1 < Nat.card K := Finite.one_lt_card
    rw [hK] at hcard
    have hf0 : f ≠ 0 := by
      intro hf0
      rw [hf0, pow_zero] at hcard
      exact lt_irrefl 1 hcard
    omega
  exact ⟨⟨Nat.prime_two, hf, hn⟩, K, hF, hfin, hK, ⟨e⟩⟩


theorem statedClassicalModel_of_hasLabel_typeTwD {X : Type} [Group X] {n f : ℕ} (hn : 4 ≤ n)
    (hX : GGHasLabel ⟨.twD, n, f⟩ X) : StatedClassicalModel X .POmegaMinus n 2 f := by
  have h2 : ¬ n = 2 := by omega
  have h3 : ¬ n = 3 := by omega
  have hX' : LargeEvenRecipeOmegaMinus (n - 1) (2 ^ f)
      (fun R' _ _ _ => Nonempty (X ≃* R')) := by
    simp only [GGHasLabel, LargeEvenRawDatum, if_neg h2, if_neg h3] at hX
    exact hX
  obtain ⟨K, hF, hfin, hK, b, c, hbc, ⟨e⟩⟩ := hX'
  have hf : 1 ≤ f := by
    have hF' : Field K := hF
    have hfin' : Finite K := hfin
    have hcard : 1 < Nat.card K := Finite.one_lt_card
    rw [hK] at hcard
    have hf0 : f ≠ 0 := by
      intro hf0
      rw [hf0, pow_zero] at hcard
      exact lt_irrefl 1 hcard
    omega
  exact ⟨⟨Nat.prime_two, hf, hn⟩, K, hF, hfin, hK, b, c, hbc,
    ⟨e.trans (omegaMinusProjEquiv n b c)⟩⟩

end CFSG.StandardType

end
