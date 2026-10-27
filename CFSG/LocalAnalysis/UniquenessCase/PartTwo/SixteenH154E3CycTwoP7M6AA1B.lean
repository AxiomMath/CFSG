module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC13BCOdd

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16h_e3_CycTwoP7M6A_lBar_le_pCoreOf
    (D : Data G) {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V)
    (hc : Conc4_136 D V₀ V hV L) {p : ℕ} (hp : p.Prime)
    (hLp : IsCyclicOrd ↥(lBar V₀ V hV L) p) :
    lBar V₀ V hV L ≤ pCoreOf p (Mbar D.M V₀ V hV) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite ↥(lBar V₀ V hV L) := Subtype.finite
  have hLpg : IsPGroup p ↥(lBar V₀ V hV L) :=
    IsPGroup.of_card (n := 1) (by rw [hLp.2, pow_one])
  have hL1 : lBar V₀ V hV L ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card ↥(lBar V₀ V hV L) = 1 := by rw [hbot, Subgroup.card_bot]
    rw [hLp.2] at h1
    exact hp.ne_one h1
  obtain ⟨n, hn⟩ := hLpg.exists_card_eq
  have hn0 : n ≠ 0 := by
    rintro rfl
    apply hL1
    rw [pow_zero] at hn
    exact Subgroup.card_eq_one.1 hn
  have hdvd : p ∣ Nat.card ↥(lBar V₀ V hV L) := by
    rw [hn]
    exact dvd_pow_self p hn0
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := ↥(lBar V₀ V hV L)) p hdvd
  have hao : orderOf (a : MulAut (Vtil V₀ V hV)) = p := by
    rw [Subgroup.orderOf_coe]
    exact ha
  obtain ⟨t, -, -, -, -, -, -, h⟩ := hc
  rcases h with h133 | ⟨K, hK, g, -, -, hLK, -⟩ | ⟨hcomp, -⟩ | ⟨-, -, hcomp, -⟩
  · obtain ⟨p', hp', hLp', -⟩ := h133
    have hpp' := s16c13bc_prime_eq_of_mem_pCoreOf hp hp' hao (hLp' a.2)
    subst hpp'
    exact hLp'
  · have hKL : K ≤ lBar V₀ V hV L := by
      rw [hLK]
      exact le_sup_left
    exact (s16c13bc_not_quasisimple_of_isPGroup hp hK.2.2 (hLpg.to_le hKL)).elim
  · exact (s16c13bc_not_quasisimple_of_isPGroup hp hcomp.2.2 hLpg).elim
  · exact (s16c13bc_not_quasisimple_of_isPGroup hp hcomp.2.2 hLpg).elim

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
