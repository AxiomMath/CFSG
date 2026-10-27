module

public import CFSG.Quasithin.Background.A318PL3Inst
public import CFSG.Quasithin.Background.A318POutSpor
public import CFSG.Quasithin.Background.A318POutMore
public import CFSG.Quasithin.Background.A318POutHe
public import CFSG.Quasithin.Background.A318PSp4
public import CFSG.Quasithin.Background.A318PG2
public import CFSG.Quasithin.Background.A318PD4

public section

namespace CFSG.Quasithin

namespace A318P

open CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

theorem a318AutFact_of
    (qs : QSporOutTwo) (ql : QLiePRank) (ql3 : QLieThreeRank) :
    A318AutFact := by
  intro p hp hp2 X _ _ S _ hC hSimple hList hrS hX
  have := hSimple
  have hdvd : p ∣ Nat.card S := dvd_card_of_one_lt_pRank hp hrS
  have key : ¬ p ∣ Nat.card (Outer ↥S) → oPrimeResidualOf p (⊤ : Subgroup X) = S ∨
      (p = 3 ∧ A318Case2 S) :=
    fun h => Or.inl (oPrimeResidualOf_eq_of_not_dvd_outer hC hp hdvd h)
  have key2 : CFSG.Open.pRank p (⊤ : Subgroup ↥S) ≤ 1 → False := fun h => by
    rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := p) S] at h
    omega
  have lieHard : (p = 3 → ∀ x : X, (∃ k : ℕ, orderOf x = 3 ^ k) → x ∈ S) →
      (5 ≤ p → LieTwoFamily ↥S) →
      oPrimeResidualOf p (⊤ : Subgroup X) = S ∨ (p = 3 ∧ A318Case2 S) := by
    intro h3 h5
    left
    refine oPrimeResidualOf_eq_of_forall hp hdvd fun x k hk => ?_
    by_cases hp3 : p = 3
    · subst hp3
      exact h3 rfl x ⟨k, hk⟩
    · exact ql p hp (five_le_of_prime hp hp2 hp3) X S hC hSimple (h5 (five_le_of_prime hp hp2 hp3))
        hrS hX x ⟨k, hk⟩
  rcases hList with ⟨n, hn5, hn8, ⟨e⟩⟩ | ⟨p₀, hp₀, hp₀2, hL⟩ | ⟨⟨f, hcases⟩ | htits⟩ |
    ⟨n, hn, hm⟩ | ⟨s, hs, ⟨e⟩⟩
  ·
    by_cases h6 : n = 6
    · subst h6
      exact key (not_dvd_outer_alternating_six e hp hp2)
    · exact key (not_dvd_outer_alternating (by omega) e hp hp2)
  ·
    rcases hL with ⟨f, hf, hm⟩ | hm | hm
    · exact key (not_dvd_outer_psl_two_odd hf hm hp hp2)
    · exact aut_L3_linear ql hp hp2 hC (Or.inr rfl) hm hrS hX
    · exact aut_L3_unitary ql hp hp2 hC (Or.inr rfl) hm hrS hX
  ·
    rcases hcases with ⟨hf, hm⟩ | ⟨hf, hm⟩ | ⟨hf, hm⟩ | ⟨hf, hm⟩ | ⟨hf, hm⟩ | ⟨hf, hm⟩ |
      ⟨hodd, hf, hm⟩ | ⟨hodd, hf, hm⟩
    · exact (key2 (pRank_le_one_psl_two_even hf hm hp hp2)).elim
    · exact aut_L3_linear ql hp hp2 hC (Or.inl rfl) hm hrS hX
    · exact aut_L3_unitary ql hp hp2 hC (Or.inl rfl) hm hrS hX
    · exact lieHard (fun h => by subst h; exact aut_Sp4 hC hm hX)
        (fun _ => Or.inr (Or.inr (Or.inl ⟨f, hf, hm⟩)))
    · exact lieHard (fun h => by subst h; exact g2_threeElements hC hf hm hX)
        (fun _ => Or.inr (Or.inr (Or.inr (Or.inl ⟨f, hf, hm⟩))))
    · exact lieHard (fun h => by subst h; exact d4_threeElements hC hf hm hX)
        (fun _ => Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨f, hf, hm⟩)))))
    · exact lieHard (fun h => by subst h; exact ql3 X S hC hSimple ⟨f, hodd, hf, hm⟩ hrS hX)
        (fun _ => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨f, hodd, hf, hm⟩)))))
    · exact (key2 (pRank_le_one_suzuki' hm hp hp2)).elim
  ·
    exact key (not_dvd_outer_tits htits hp hp2)
  ·
    exact key (not_dvd_outer_psl_binary (by omega) hm hp hp2)
  ·
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact key (not_dvd_outer_M11 e hp hp2)
    · exact key (not_dvd_outer_M12 e hp hp2)
    · exact key (not_dvd_outer_M22 e hp hp2)
    · exact key (not_dvd_outer_M23 e hp hp2)
    · exact key (not_dvd_outer_M24 e hp hp2)
    · exact key (not_dvd_outer_J1 e hp hp2)
    · exact key (not_dvd_outer_J2 e hp hp2)
    · exact key (not_dvd_outer_J4 e qs hp hp2)
    · exact key (not_dvd_outer_HS e hp hp2)
    · exact key (not_dvd_outer_He e hp hp2)
    · exact key (not_dvd_outer_Ru e hp hp2)

end A318P

end CFSG.Quasithin
