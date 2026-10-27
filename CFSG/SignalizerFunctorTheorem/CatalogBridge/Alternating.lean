module

public import CFSG.SignalizerFunctorTheorem.CatalogBridge.Basic
public import CFSG.RankThree.PartOne.KA.AlternatingPlaneInner

public section

open CFSG.Open
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

namespace CFSG.SignalizerFunctorTheorem.CatalogBridge

theorem six_dvd_card_alternating {n : ℕ} (hn : 5 ≤ n) :
    6 ∣ Nat.card (alternatingGroup (Fin n)) := by
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have hcard : Nat.card (alternatingGroup (Fin n)) = n.factorial / 2 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
  obtain ⟨m, hm⟩ := Nat.factorial_dvd_factorial (show 4 ≤ n by omega)
  rw [hcard, hm]
  exact ⟨2 * m, by rw [show (4 : ℕ).factorial = 24 from rfl]; omega⟩

theorem hypothesisA_alternating {p : ℕ} (hp : p.Prime) {X : Type} [Group X] [Finite X]
    (hsimple : IsSimpleGroup X) (hnonab : ∃ a b : X, a * b ≠ b * a) {n : ℕ} (hn : 5 ≤ n)
    (e : X ≃* alternatingGroup (Fin n)) (hcop : Nat.Coprime p (Nat.card X)) :
    signalizerMcBrideHypothesisA p X := by
  have hpX : ¬ p ∣ Nat.card X := (Nat.Prime.coprime_iff_not_dvd hp).mp hcop
  have h6 : 6 ∣ Nat.card X := by
    rw [Nat.card_congr e.toEquiv]
    exact six_dvd_card_alternating hn
  have hp2 : p ≠ 2 := fun h => hpX (h ▸ (by omega : 2 ∣ Nat.card X))
  have hp3 : p ≠ 3 := fun h => hpX (h ▸ (by omega : 3 ∣ Nat.card X))
  have hp5 : 5 ≤ p := by
    have := hp.two_le
    by_contra hlt
    interval_cases p <;> simp_all (config := {decide := true})
  have hout : Nat.card (Outer X) ≤ 4 :=
    (Nat.card_congr
      (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv).trans_le
      (CFSG.RankThree.PartOne.card_outer_alternating_le_four hn)
  have hpO : ¬ p ∣ Nat.card (Outer X) := fun h => by
    have := Nat.le_of_dvd Nat.card_pos h
    omega
  exact hypothesisA_of_not_dvd_card_mulAut hp hsimple hnonab hcop
    (not_dvd_card_mulAut_of_not_dvd_outer hp hpX hpO)

end CFSG.SignalizerFunctorTheorem.CatalogBridge
