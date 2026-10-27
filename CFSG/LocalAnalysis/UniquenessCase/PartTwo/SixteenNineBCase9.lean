module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNineBCase9B

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16n9b_case9_invFix (D : Data G) (h1217 : R1217 D) {V₀ V L : Subgroup G}
    (hV : IsElemAbelian 2 V) (hc : Counterex16 D V₀ V L hV) (hV0 : V₀ ≠ ⊥)
    (h9 : Case168_9 D V₀ V hV L) : s16n9bInvFix (Mbar D.M V₀ V hV) 7 4 := by
  obtain ⟨g, h2⟩ := s16n9b_case9_two D h1217 hV hc hV0 h9
  refine s16n9b_case9_two_invFix (T := Vtil V₀ V hV) (s15_Infra_vtil_sq_eq_one V₀ V hV)
    h2 ?_ ?_ ?_ (s16n9b_case9_rank D h1217 hV hc hV0 h9)
  · have hrk : rk ↥(wTil V₀ V hV L) = 9 :=
      s16c167_rk_natSum3 (s16c167_natSum3_of_sumOfNat h9.2.2.2.1)
    show 4 < rk ↥(wTil V₀ V hV L)
    omega
  · norm_num
  · obtain ⟨-, hL3, -, -, -⟩ := h9
    have hPSL : IsPSL 3 2 1 ↥(lBar V₀ V hV L) := s16n9b_case9_isPSL_of_isL3 hL3
    have hcard : Nat.card ↥(lBar V₀ V hV L) = 168 := card_eq_168_of_isPSL_three_two hPSL
    obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card'
      (G := ↥(lBar V₀ V hV L)) 7 (by rw [hcard]; norm_num)
    refine ⟨(a : MulAut (Vtil V₀ V hV)), a.2, ?_⟩
    rwa [Subgroup.orderOf_coe]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
