module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNineBTwo
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNineBCase6
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKSchur2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16n9b_case6_invFix (D : Data G) (h1217 : R1217 D) {V₀ V L : Subgroup G}
    (hV : IsElemAbelian 2 V) (hc : Counterex16 D V₀ V L hV) (hV0 : V₀ ≠ ⊥)
    (h6 : Case168_6 D V₀ V hV L) : s16n9bInvFix (Mbar D.M V₀ V hV) 3 3 := by
  obtain ⟨g, hg⟩ := s16n9b_twoConj D h1217 hV hc hV0 h6.2.2.1
  obtain ⟨hN, hrank⟩ := s16n9b_case6_rank D hV h6
  have hord3 : ∃ a ∈ lBar V₀ V hV L, orderOf a = 3 := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hY : IsAlt ↥(lBar V₀ V hV L) 5 ∨ IsL3 ↥(lBar V₀ V hV L) 1 := by
      rcases h6.2.1 with ⟨hA, -⟩ | ⟨hL, -⟩
      · exact Or.inl hA
      · exact Or.inr hL
    have h3 : 3 ∣ Nat.card ↥(lBar V₀ V hV L) := by
      rcases s15k_schur2_card hY with h | h <;> rw [h] <;> norm_num
    obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' 3 h3
    exact ⟨(a : MulAut (Vtil V₀ V hV)), a.2, by rw [Subgroup.orderOf_coe]; exact ha⟩
  exact s16n9b_two_invFix hg (p := 3) (N := 3) (r := 2) hN (by norm_num) hord3 hrank

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
