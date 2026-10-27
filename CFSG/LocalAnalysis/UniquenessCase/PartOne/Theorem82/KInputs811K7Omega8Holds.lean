module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811K7Omega8
import CFSG.ClassicalGroups.Orthogonal.OmegaMinus8ThreeLocalK7

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open Subgroup CFSG.Open CFSG.LieType.BorelTits
open CFSG.ClassicalGroups.Orthogonal.OmegaMinus8ThreeLocal

theorem k7bOmega8Model_holds {r f p : ℕ} (hr : r.Prime) (hr3 : r ≠ 3) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ∣ qPlusPi r f) : K7bOmega8Model r f p := by
  intro K _ _ b c hK hbc
  haveI : Fact r.Prime := ⟨hr⟩
  have h3 : (3 : K) ≠ 0 := three_ne_zero_of_card_eq hK hr3
  have hplus : plusPi (Nat.card K) = qPlusPi r f := by
    rw [hK]
    simp only [plusPi, qPlusPi]
  have hpd : p ∣ plusPi (Nat.card K) := by rw [hplus]; exact hpq
  refine ⟨(c₀ h3 hbc).range, ?_, ?_, ?_⟩
  ·
    have hpow : ∀ x : Multiplicative (Fin 3 → ZMod 3), x ^ 3 = 1 := by
      intro x
      refine Multiplicative.toAdd.injective (funext fun i => ?_)
      simp [toAdd_pow]
      decide +revert
    have hcomm : IsMulCommutative ((c₀ h3 hbc).range) := by
      have h := Subgroup.map_isMulCommutative
        (⊤ : Subgroup (Multiplicative (Fin 3 → ZMod 3))) (c₀ h3 hbc)
      rwa [Subgroup.map_top] at h
    refine ⟨hcomm, fun x hx => ?_⟩
    obtain ⟨u, hu⟩ := MonoidHom.mem_range.mp hx
    rw [← hu, ← map_pow, hpow u, map_one]
  ·
    rw [Nat.card_congr (MonoidHom.ofInjective (c₀_injective h3 hbc)).symm.toEquiv,
      Nat.card_congr Multiplicative.toAdd, Nat.card_eq_fintype_card]
    simp [Fintype.card_fun, ZMod.card]
  ·
    exact exists_k7b_centralizer h3 hbc hp hp2 hpd

theorem k7b_pomega8m
    {Y : Type} [Group Y] [Finite Y] {r f : ℕ} (hY : IsLie811 Y .pomega8m r f)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ qPlusPi r f)
    {A : Subgroup Y} (hA : CFSG.Open.IsElemAbelian 3 A) (h27 : Nat.card A = 27) :
    ∃ y ∈ centralizer (A : Set Y), orderOf y = p ∧ ∀ X : Subgroup Y, X ≤ A → Nat.card X = 3 →
      ∃ u ∈ centralizer (X : Set Y), orderOf u = p ∧ u * y = y * u ∧ u ∉ zpowers y :=
  k7b_pomega8m_of_model hY hp hp2
    (k7bOmega8Model_holds hY.2.2.1 hY.2.2.2.1 hp hp2 hpq) hA h27

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
