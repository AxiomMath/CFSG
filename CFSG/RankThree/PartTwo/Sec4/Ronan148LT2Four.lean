module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148LE27Four
public import CFSG.RankThree.PartTwo.Sec4.Ronan148LT2Syl
public import CFSG.RankThree.PartTwo.Sec4.RonanK432RowSU4Two

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148L

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec4.Ronan148S
open CFSG.HardMathSupport.Solomon.Coordinator.LieComp (NoThreeCover)
open CFSG.Assembly.RankThreeEven (projSL projSU)

section SU


theorem kT2_four_SU_mod_two (p : ℕ) [Fact p.Prime] (hp3 : 3 < p) (hp : p % 3 = 2) :
    RowOf425 (projSU 4 p 1) := fun S _ _ _ _ ⟨e⟩ => by
  obtain ⟨E, hE⟩ := exists_e27_projSU4 hp
  exact row425_of_e27Move
    (HardMathSupport.Solomon.Coordinator.LieComp.NoThreeCover.of_mulEquiv e
      (noThreeCover_projSU4 hp3))
    (cubeInner_of_mulEquiv e (cubeInner_of_not_three_dvd_card_outer
      RonanK432.not_three_dvd_card_outer_projSU_four_prime))
    ⟨E.map e.symm.toMonoidHom, isElemAbelian_map _ hE.1, by
      rw [Subgroup.card_map_of_injective e.symm.injective, hE.2]⟩
    ((e27Move_projSU4 hp).of_mulEquiv e)

end SU

section SL


theorem kT2_four_SL_mod_one (p : ℕ) [Fact p.Prime] (hp3 : 3 < p) (hp : p % 3 = 1) :
    RowOf425 (projSL 4 (GaloisField p 1)) := fun S _ _ _ _ ⟨e⟩ => by
  obtain ⟨E, hE⟩ := exists_e27_projSL4 hp
  exact row425_of_e27Move
    (HardMathSupport.Solomon.Coordinator.LieComp.NoThreeCover.of_mulEquiv e
      (noThreeCover_projSL4 hp3))
    (cubeInner_of_mulEquiv e (cubeInner_of_not_three_dvd_card_outer
      not_three_dvd_card_outer_projSL4p))
    ⟨E.map e.symm.toMonoidHom, isElemAbelian_map _ hE.1, by
      rw [Subgroup.card_map_of_injective e.symm.injective, hE.2]⟩
    ((e27Move_projSL4 hp).of_mulEquiv e)


theorem kT2_four_SL (p : ℕ) [Fact p.Prime] (hp : 3 < p) :
    RowOf425 (projSL 4 (GaloisField p 1)) := by
  rcases (by omega : p % 3 = 0 ∨ p % 3 = 1 ∨ p % 3 = 2) with h | h | h
  · have h3 : 3 ∣ p := Nat.dvd_of_mod_eq_zero h
    rcases (Nat.dvd_prime (Fact.out : p.Prime)).mp h3 with h' | h' <;> omega
  · exact kT2_four_SL_mod_one p hp h
  · exact kT2_four_SL_mod_two p h

end SL

end CFSG.RankThree.PartTwo.Sec4.Ronan148L
