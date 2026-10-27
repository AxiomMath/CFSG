module

public import CFSG.RankThree.Classical.UnitaryRankWitness
public import CFSG.RankThree.PartOne.SRC.RankOneAux

public section

namespace CFSG.RankThree.PartOne.SLB4B

open CFSG CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.Classical

theorem exists_elementaryAbelian_statedSU_four {p e : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (he : 1 ≤ e) {K : Type} [Field K] (hK : Nat.card K = p ^ (2 * e)) :
    ∃ E : Subgroup (StatedSU 4 (p ^ e) K), IsElementaryAbelian p E ∧
      Nat.card E = p ^ (4 * e) := by
  classical
  have h : UnitaryFieldData p e K := ⟨Fact.out, he, hK⟩
  have : CharP K p := h.charP
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero (by rw [ringChar.eq K p]; exact hp2)
  obtain ⟨P, hP⟩ := exists_evenFrame h h2 (n := 4) (r := 2) (by norm_num)
  have hP' : hadj h P * P = frameGram 2 (4 - 2 * 2) K := hP
  have hnm : 2 * 2 + (4 - 2 * 2) = 4 := by omega
  set φ := frameSUHom h hP' hnm with hφdef
  have hinj : Function.Injective φ :=
    Function.Injective.of_comp (f := unitaryProj h 4) (frameUnipotentHom_injective h hP' hnm)
  have hpow : ∀ a : Multiplicative (skewHermMatrices h 2), a ^ p = 1 := fun a =>
    Multiplicative.toAdd.injective (by rw [toAdd_pow, toAdd_one]; exact nsmul_char_eq_zero _ _)
  refine ⟨φ.range, CFSG.RankThree.PartOne.SRC.isElementaryAbelian_range φ hpow, ?_⟩
  rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective hinj, Subgroup.card_top,
    Nat.card_congr Multiplicative.toAdd, card_skewHermMatrices, ← pow_mul]
  congr 1
  omega

end CFSG.RankThree.PartOne.SLB4B
