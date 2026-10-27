module

public import CFSG.LocalAnalysis.UniquenessCase.UC6K332Bridge
import CFSG.RankThree.PartTwo.Sec4.RonanK432RowZ3FieldL3
import CFSG.RankThree.PartTwo.Sec4.RonanK432RowZ3FieldU3
import CFSG.RankThree.PartTwo.Sec4.RonanK432RowL33
public import CFSG.RankThree.PartTwo.Sec4.RonanK432RowL3Easy
import CFSG.RankThree.PartTwo.Sec4.RonanK432RowU3Char3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.K332Route

open CFSG.Blueprint CFSG.PGLModel
open CFSG.RankThree.PartTwo.Sec4.RonanK432
open CFSG.RankThree.PartTwo.Sec4 (PiField ModThree)
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (projectiveSL)
open CFSG.RankThree.PartTwo.KFacts.L34 (projSLEquivProjectiveSL)

private theorem pow_three_mod_three (x : ℕ) : x ^ 3 % 3 = x % 3 := by
  rcases (show x % 3 = 0 ∨ x % 3 = 1 ∨ x % 3 = 2 by omega) with h | h | h <;>
    simp [Nat.pow_mod, h]

private theorem pow_div_three_mod_three {p f : ℕ} (h3 : 3 ∣ f) : p ^ (f / 3) % 3 = p ^ f % 3 := by
  obtain ⟨k, rfl⟩ := h3
  rw [Nat.mul_div_cancel_left _ (by norm_num), pow_mul', pow_three_mod_three]

theorem outerRow_projSL_three_pow_of_mod_one {p f : ℕ} [Fact p.Prime] (hf : 1 ≤ f)
    (hq : p ^ f % 3 = 1) : OuterRow (projSL 3 (GaloisField p f)) := by
  have hp : p.Prime := Fact.out
  have hcard : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f (by omega)
  have hmod : Nat.card (GaloisField p f) % 3 = 1 := by rw [hcard]; exact hq
  by_cases h3 : 3 ∣ f
  · haveI : Finite (projectiveSL 3 (GaloisField p f)) :=
      Finite.of_equiv _ (projSLEquivProjectiveSL 3 (GaloisField p f)).toEquiv
    have hr : p ^ (f / 3) % 3 = 1 := (pow_div_three_mod_three h3).trans hq
    have h2 : 2 ≤ p ^ (f / 3) := hp.two_le.trans (Nat.le_self_pow (by omega) p)
    exact OuterRow.of_mulEquiv (projSLEquivProjectiveSL 3 (GaloisField p f)).symm
      (outerRow_projectiveSL_three_of_frobenius hmod hp hf hcard h3 (m := p ^ (f / 3) - 1)
        (by omega) (by omega) (by omega))
  · exact outerRow_projSL_three_of_mod_one hmod (no_field_aut_order_three h3 (by omega))

theorem outerRow_projSU_three_pow_of_mod_two {p f : ℕ} [Fact p.Prime] (hf : 1 ≤ f)
    (hq : p ^ f % 3 = 2) (h2 : p ^ f ≠ 2) : OuterRow (projSU 3 p f) := by
  have hp : p.Prime := Fact.out
  by_cases h3 : 3 ∣ f
  · have hPi : PiField false p f (GaloisField p (2 * f)) :=
      ⟨hp, hf, by
        rw [GaloisField.card p (2 * f) (by omega)]
        change p ^ (2 * f) = (p ^ f) ^ 2
        rw [← pow_mul, mul_comm]⟩
    have hmod : ModThree false (p ^ f) := hq
    have hr : p ^ (f / 3) % 3 = 2 := (pow_div_three_mod_three h3).trans hq
    obtain ⟨e⟩ := CFSG.RankThree.PartTwo.KFacts.nonempty_unitaryPSU_mulEquiv_projSU hPi.unitary
    exact OuterRow.of_mulEquiv e (outerRow_unitaryPSU_three_of_frobenius hPi.unitary hPi hmod
      (by omega) h3 (k := p ^ (f / 3) / 3) (by omega))
  · exact outerRow_projSU_three_of_mod_two (by omega) hq h2
      (no_field_aut_order_three (by omega) (by omega))

theorem goodRow_psl3_of_mod_one {S : Type} [Group S] [Finite S] {p f : ℕ}
    (h : LieModel S .PSL 3 p f) (hq : p ^ f % 3 = 1) : GoodRow S := by
  haveI : Fact p.Prime := ⟨h.admissible.1⟩
  have hf : 1 ≤ f := h.admissible.2.1
  obtain ⟨e⟩ := nonempty_projSL_of_lieModel h
  exact GoodRow.of_mulEquiv e.symm
    ⟨listRow_projSL_three_galoisField_of_mod_one (by omega) hq,
      outerRow_projSL_three_pow_of_mod_one hf hq⟩

theorem goodRow_psu3_of_mod_two {S : Type} [Group S] [Finite S] {p f : ℕ}
    (h : LieModel S .PSU 3 p f) (hq : p ^ f % 3 = 2) : GoodRow S := by
  haveI : Fact p.Prime := ⟨h.admissible.1⟩
  obtain ⟨-, hf, -, hne⟩ := h.admissible
  obtain ⟨e⟩ := nonempty_projSU_of_lieModel h
  exact GoodRow.of_mulEquiv e.symm
    ⟨listRow_projSU_three_of_mod_two (by omega) hq,
      outerRow_projSU_three_pow_of_mod_two hf hq (fun h2 => hne (by rw [h2]))⟩

theorem goodRow_psl3_three_one {S : Type} [Group S] [Finite S] (hs : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (h : LieModel S .PSL 3 3 1) : GoodRow S := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e⟩ := nonempty_projSL_of_lieModel h
  exact rowOf_nine_SL3_one S hs hna ⟨e⟩

theorem goodRow_psu3_three_one {S : Type} [Group S] [Finite S] (hs : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) (h : LieModel S .PSU 3 3 1) : GoodRow S := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e⟩ := nonempty_projSU_of_lieModel h
  exact rowOf_nine_SU3_one S hs hna ⟨e⟩

end CFSG.LocalAnalysis.UniquenessCase.UCK.K332Route
