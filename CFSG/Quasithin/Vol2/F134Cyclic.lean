module

public import CFSG.Quasithin.Vol2.F134Basic
public import CFSG.LocalAnalysis.SectionRank.OddCover.CyclicSylow

public section

namespace CFSG.Quasithin.F134

open CFSG.Assembly.LowTwoRank

theorem noElemNine_of_statedPSL_three {X : Type} [Group X] {p : ℕ} (hp3 : p % 3 = 2)
    (h : StatedClassicalModel X .PSL 3 p 1) : NoElemNine X := by
  obtain ⟨⟨hp, -⟩, K, _, _, hK, ⟨e⟩⟩ := h
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hK' : Nat.card K = p := by rw [hK, pow_one]
  have hcyc := (CFSG.SectionRank.OddCover.prime_classical_three_cyclic_odd_sylows hp
    (ε := 1) (H := StatedSL 3 K) (Or.inl ⟨rfl, hK', rfl⟩)).1 3 (by norm_num) (by omega)
    (by omega)
  refine NoElemNine.of_mulEquiv e (noElemNine_of_isCyclic fun Q hQ => ?_)
  exact isCyclic_of_isPGroup_of_surjective (QuotientGroup.mk'_surjective _) hcyc Q hQ

theorem noElemNine_of_statedPSU_three {X : Type} [Group X] {p : ℕ} (hp3 : p % 3 = 1)
    (h : StatedClassicalModel X .PSU 3 p 1) : NoElemNine X := by
  obtain ⟨⟨hp, -⟩, K, _, _, hK, ⟨e⟩⟩ := h
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [pow_one] at hK
  have hcyc := (CFSG.SectionRank.OddCover.prime_classical_three_cyclic_odd_sylows hp
    (ε := -1) (H := StatedSU 3 (p ^ 1) K) (Or.inr ⟨rfl, hK, by rw [pow_one]⟩)).1 3
    (by norm_num) (by omega) (by omega)
  refine NoElemNine.of_mulEquiv e (noElemNine_of_isCyclic fun Q hQ => ?_)
  exact isCyclic_of_isPGroup_of_surjective (QuotientGroup.mk'_surjective _) hcyc Q hQ

end CFSG.Quasithin.F134
