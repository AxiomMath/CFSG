module

public import CFSG.RankThree.PartTwo.KFacts.KP4BasicCertificate18952Inputs
public import CFSG.RankThree.Asc83Table.M22

public section

namespace CFSG.RankThree.PartTwo.KFacts.KP4

open Equiv
open CFSG.RankThree.Asc83Table (permWord)
open CFSG.RankThree.Asc83Table.M22 (x y gens)

private theorem cert18952_vA_eq_word : ∀ i : Fin 4, vA i = permWord gens (vAWord i) := by
  decide +kernel

private theorem cert18952_vB_eq : ∀ i : Fin 4, vB i = (tw i)⁻¹ * vA i * tw i := by
  decide +kernel

private theorem cert18952_perm_facts : ∀ i : Fin 4,
    vA i * vA i = 1 ∧ vB i * vB i = 1 ∧ vA i * vB i = vB i * vA i ∧ vA i ≠ 1 ∧ vB i ≠ 1 ∧
      vA i ≠ vB i ∧ vA i * line i = line i * vA i ∧ vB i * line i = line i * vB i ∧
      line i ^ 3 = 1 ∧ line i ≠ 1 := by
  decide +kernel

private theorem cert18952_conj_facts : ∀ i : Fin 4, x * vA i * x⁻¹ = vElem i (conjIdx 0 i) ∧
    x * vB i * x⁻¹ = vElem i (conjIdx 1 i) ∧ y * vA i * y⁻¹ = vElem i (conjIdx 2 i) ∧
    y * vB i * y⁻¹ = vElem i (conjIdx 3 i) := by
  decide +kernel

private theorem cert18952_tw_facts : ∀ i : Fin 4, tw i * vA i * (tw i)⁻¹ = vA i * vB i ∧
    tw i * vB i * (tw i)⁻¹ = vA i ∧ (tw i = x ∨ tw i = y) := by
  decide +kernel

private theorem cert18952_ofTab_lineTab : ∀ i : Fin 4, ∀ p, ofTab (lineTab i) p = line i p := by
  decide +kernel

private theorem cert18952_line_eq : ∀ i : Fin 4, line i = x ^ lineA i * y ^ lineB i := by
  decide +kernel

private theorem cert18952_pow_mul_pow_cases : ∀ a b : Fin 3, (a, b) ≠ (0, 0) → ∃ i : Fin 4,
    x ^ (a : ℕ) * y ^ (b : ℕ) = line i ∨ x ^ (a : ℕ) * y ^ (b : ℕ) = line i ^ 2 := by
  decide +kernel

end CFSG.RankThree.PartTwo.KFacts.KP4

namespace Certificates

open Equiv CFSG.RankThree.PartTwo.KFacts.KP4 in
open CFSG.RankThree.Asc83Table (permWord) in
open CFSG.RankThree.Asc83Table.M22 (x y gens) in
theorem certificate18952 : (
    ∀ i : Fin 4, vA i = permWord gens (vAWord i)
  ) ∧ (
    ∀ i : Fin 4, vB i = (tw i)⁻¹ * vA i * tw i
  ) ∧ (
    ∀ i : Fin 4,
      vA i * vA i = 1 ∧ vB i * vB i = 1 ∧ vA i * vB i = vB i * vA i ∧ vA i ≠ 1 ∧ vB i ≠ 1 ∧
        vA i ≠ vB i ∧ vA i * line i = line i * vA i ∧ vB i * line i = line i * vB i ∧
        line i ^ 3 = 1 ∧ line i ≠ 1
  ) ∧ (
    ∀ i : Fin 4, x * vA i * x⁻¹ = vElem i (conjIdx 0 i) ∧
      x * vB i * x⁻¹ = vElem i (conjIdx 1 i) ∧ y * vA i * y⁻¹ = vElem i (conjIdx 2 i) ∧
      y * vB i * y⁻¹ = vElem i (conjIdx 3 i)
  ) ∧ (
    ∀ i : Fin 4, tw i * vA i * (tw i)⁻¹ = vA i * vB i ∧
      tw i * vB i * (tw i)⁻¹ = vA i ∧ (tw i = x ∨ tw i = y)
  ) ∧ (
    ∀ i : Fin 4, ∀ p, ofTab (lineTab i) p = line i p
  ) ∧ (
    ∀ i : Fin 4, line i = x ^ lineA i * y ^ lineB i
  ) ∧ (
    ∀ a b : Fin 3, (a, b) ≠ (0, 0) → ∃ i : Fin 4,
      x ^ (a : ℕ) * y ^ (b : ℕ) = line i ∨ x ^ (a : ℕ) * y ^ (b : ℕ) = line i ^ 2
  ) := by
  exact ⟨CFSG.RankThree.PartTwo.KFacts.KP4.cert18952_vA_eq_word,
    CFSG.RankThree.PartTwo.KFacts.KP4.cert18952_vB_eq,
    CFSG.RankThree.PartTwo.KFacts.KP4.cert18952_perm_facts,
    CFSG.RankThree.PartTwo.KFacts.KP4.cert18952_conj_facts,
    CFSG.RankThree.PartTwo.KFacts.KP4.cert18952_tw_facts,
    CFSG.RankThree.PartTwo.KFacts.KP4.cert18952_ofTab_lineTab,
    CFSG.RankThree.PartTwo.KFacts.KP4.cert18952_line_eq,
    CFSG.RankThree.PartTwo.KFacts.KP4.cert18952_pow_mul_pow_cases⟩

end Certificates
