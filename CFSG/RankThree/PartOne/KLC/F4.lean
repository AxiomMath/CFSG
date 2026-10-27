module

public import CFSG.RankThree.PartOne.KLC.EigF4
public import CFSG.RankThree.PartOne.KLC.Assembly
public import CFSG.RankThree.PartOne.KLC.G2
public import CFSG.RankThree.PartOne.KE.CTCasesF4
public import CFSG.RankThree.PartOne.KE.CTMain

public section

namespace CFSG.RankThree.PartOne.KLC

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.Sec66T
open CFSG.RankThree.Chevalley (exhaustionPhi exists_mem_row_of_dvd_pow_sub_one
  exhaustionMinusFactors)


section Regular


theorem no_commuting_F4_regular {K : Type} [Field K] [Finite K] (hK2 : Even (Nat.card K))
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) {e : ℕ} (he : e = 8 ∨ e = 12)
    (h : (p : ℤ) ∣ (exhaustionPhi e).eval (Nat.card K : ℤ)) {x y : adjointGroup Tag.F4 K}
    (hx : orderOf x = p) (hy2 : y ^ 2 = 1) (hy1 : y ≠ 1) (hxy : x * y = y * x) : False := by
  rcases he with rfl | rfl
  · obtain ⟨-, -, hc⟩ := F4_eight_cyclic_sylow cyclic_torus_prime_centralizers_F4 K hp hp3 h
    refine not_commute_involution_of_cyclicSylow hc ?_ hx hy2 hy1 hxy
    exact Even.add_one (Nat.even_pow.2 ⟨hK2, by norm_num⟩)
  · obtain ⟨-, -, hc⟩ := F4_twelve_cyclic_sylow cyclic_torus_prime_centralizers_F4 K hp hp3 h
    refine not_commute_involution_of_cyclicSylow hc ?_ hx hy2 hy1 hxy
    have h4 : Even (Nat.card K ^ 4) := Nat.even_pow.2 ⟨hK2, by norm_num⟩
    have h2 : Even (Nat.card K ^ 2) := Nat.even_pow.2 ⟨hK2, by norm_num⟩
    have hle : Nat.card K ^ 2 ≤ Nat.card K ^ 4 :=
      Nat.pow_le_pow_right Nat.card_pos (by norm_num)
    exact Even.add_one ((Nat.even_sub hle).2 ⟨fun _ => h2, fun _ => h4⟩)

end Regular

section Main

theorem lieGoodComponentFixT_F4 :
    LieGoodComponentFixT .F4 := by
  intro T _ _ p hp hp5 hLR hpr n f₀ hf₀ hM α hαp hαinn hLRA hX x hxp hx1 hαx y hy2 hy1 hxy
  exfalso
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨K, hKf, hKfin, hKcard, ⟨e⟩⟩ :=
    exists_adjoint_equiv (show untwistedTag .F4 = some Tag.F4 from rfl) hM
  have hpK : ¬ p ∣ Nat.card K := by
    rw [hKcard]
    exact not_dvd_two_pow hp hp5
  have hK2 : Even (Nat.card K) := by
    rw [hKcard]
    exact Nat.even_pow.2 ⟨even_two, Nat.pos_iff_ne_zero.1 (Nat.mul_pos hp.pos hf₀)⟩
  have hx' : orderOf (e x) = p := by
    rw [MulEquiv.orderOf_eq]
    exact orderOf_eq_prime hxp hx1
  have hy2' : (e y) ^ 2 = 1 := by rw [← map_pow, hy2, map_one]
  have hy1' : e y ≠ 1 := fun h => hy1 (e.injective (by rw [h, map_one]))
  have hxy' : e x * e y = e y * e x := by rw [← map_mul, ← map_mul, hxy]
  have hdvd : p ∣ Nat.card (adjointGroup Tag.F4 K) := hx' ▸ orderOf_dvd_natCard (e x)
  rw [exactF4FiniteOrder K] at hdvd
  have hq1 : 1 ≤ Nat.card K := Nat.card_pos
  have hD : ∃ d ∈ ([2, 6, 8, 12] : List ℕ), p ∣ Nat.card K ^ d - 1 := by
    rcases (Nat.Prime.dvd_mul hp).1 hdvd with h | h
    · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
      · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
        · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
          · exact absurd (hp.dvd_of_dvd_pow h) hpK
          · exact ⟨2, by simp, h⟩
        · exact ⟨6, by simp, h⟩
      · exact ⟨8, by simp, h⟩
    · exact ⟨12, by simp, h⟩
  obtain ⟨m, hm, hpm⟩ := exists_mem_row_of_dvd_pow_sub_one hp hq1
    (D := [2, 6, 8, 12]) (by decide) (row := ({1, 2, 3, 4, 6, 8, 12} : Finset ℕ)) (by decide) hD
  have hm' : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 6 ∨ m = 8 ∨ m = 12 := by
    simpa using hm
  rcases hm' with hm1 | hm2 | hm3 | hm4 | hm6 | hm8 | hm12
  · have := two_le_pRank_F4_of_sector hp hp5 hpK (e := m) (by omega) hpm
    rw [pRank_congr_mulEquiv e hp.one_lt] at hpr
    omega
  · have := two_le_pRank_F4_of_sector hp hp5 hpK (e := m) (by omega) hpm
    rw [pRank_congr_mulEquiv e hp.one_lt] at hpr
    omega
  · have := two_le_pRank_F4_of_sector hp hp5 hpK (e := m) (by omega) hpm
    rw [pRank_congr_mulEquiv e hp.one_lt] at hpr
    omega
  · have := two_le_pRank_F4_of_sector hp hp5 hpK (e := m) (by omega) hpm
    rw [pRank_congr_mulEquiv e hp.one_lt] at hpr
    omega
  · have := two_le_pRank_F4_of_sector hp hp5 hpK (e := m) (by omega) hpm
    rw [pRank_congr_mulEquiv e hp.one_lt] at hpr
    omega
  · exact no_commuting_F4_regular hK2 hp (by omega) (e := m) (by omega) hpm hx' hy2' hy1' hxy'
  · exact no_commuting_F4_regular hK2 hp (by omega) (e := m) (by omega) hpm hx' hy2' hy1' hxy'

end Main

end CFSG.RankThree.PartOne.KLC
