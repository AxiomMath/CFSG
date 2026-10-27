module

public import CFSG.RankThree.PartOne.SLB4B.RankFourU
public import CFSG.RankThree.PartOne.SLB4B.RadicalU
public import CFSG.RankThree.PartOne.SLB4B.CommCover

set_option linter.unusedSectionVars false

public section

namespace CFSG.RankThree.PartOne.SLB4B

open Subgroup CFSG CFSG.RankThree.PartOne.SRC CFSG.Assembly.LowTwoRank

section Three

variable {K : Type} [Field K] [Finite K]

theorem cover_su4_three {p e : ℕ} [Fact p.Prime] [CharP K p] (hp3 : p = 3) (he : e = 1)
    (hK : Nat.card K = (p ^ e) ^ 2) (W : Type) [Group W] [Finite W]
    (ρ : W →* StatedSU 4 (p ^ e) K) (hρ : Function.Surjective ρ) (hker : IsPGroup p ρ.ker) :
    ∃ (E : Subgroup W) (k : ℕ), 4 ≤ k ∧ IsElementaryAbelian p E ∧ Nat.card E = p ^ k := by
  have hp2 : p ≠ 2 := by omega
  obtain ⟨hQ, hZ, h, hhc, hho⟩ := su4_block_data hK hp2
  have hK' : Nat.card K = p ^ (2 * e) := by rw [hK, ← pow_mul, mul_comm]
  obtain ⟨E₀, hE₀, hcard, hcomm⟩ := exists_su4_three_radical hp3 he hK'
  exact rank_four_of_cover_quasisimple_comm hp2 hQ hZ h hhc hho hE₀ (k := 4) le_rfl hcard hcomm
    ρ hρ hker

end Three

theorem rankFourCover_psu_three {p e : ℕ} [Fact p.Prime] (hp3 : p = 3) (he : e = 1) {n : ℕ}
    (hn : 5 ≤ n) :
    RankFourCover p (StatedProj (StatedSU n (p ^ e) (GaloisField p (2 * e)))) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = 4 + m := ⟨n - 4, by omega⟩
  have hm : 1 ≤ m := by omega
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := by omega
  set K := GaloisField p (2 * e) with hKdef
  have hK : Nat.card K = (p ^ e) ^ 2 := by
    rw [GaloisField.card p (2 * e) (by omega), ← pow_mul, mul_comm]
  have hodd : Odd (p ^ e) := (hp.eq_two_or_odd'.resolve_left hp2).pow
  have hneg : (-1 : K) ≠ 1 :=
    Ring.neg_one_ne_one_of_char_ne_two (by rw [ringChar.eq K p]; exact hp2)
  exact rankFourCover_of_cover_ker hp hp2
    (fun W _ _ ρ hρ hker => cover_su4_three hp3 he hK W ρ hρ hker)
    (psuEmb (m := m) hodd.pos)
    (fun A hA => by rw [psuEmb_injective hodd.pos hm (hA.trans (map_one _).symm), one_pow])
    (orderOf_psuSign hodd hm hneg) (psuEmb_comm hodd.pos hodd)

end CFSG.RankThree.PartOne.SLB4B
