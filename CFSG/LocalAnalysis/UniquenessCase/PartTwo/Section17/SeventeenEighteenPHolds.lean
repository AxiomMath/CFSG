module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenEighteenNoncentral
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SporadicNoncentral17
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.HeJ2Local17
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenEighteenResidual

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {G : Type} [Group G] [Finite G]

section Certificates

theorem sporadic_cases_of_pRank_le_two
    (D : Data G) {V₀ V L : Subgroup G}
    (c : Ctx17_17 D V₀ V L) (h2 : CFSG.Open.pRank 3 L ≤ 2) :
    ∃ s : TauCeti.SporadicName, IsSpor (BarInf L) s ∧
      ((s = .M11 ∨ s = .M23 ∨ s = .M24 ∨ s = .J2 ∨ s = .He ∨ s = .J4) ∨
        (s = .J1 ∨ s = .M12 ∨ s = .M22 ∨ s = .HS ∨ s = .Ru)) := by
  obtain ⟨s, hs⟩ := c.sporadic
  refine ⟨s, hs, ?_⟩
  have hq : CFSG.Open.IsQuasisimple (Bar2 L) := c.mem_calC.2.2
  have hodd : Odd (Nat.card (Subgroup.center (Bar2 L))) :=
    UC22.uc22p20p_odd_center_bar2 ↥L
  obtain ⟨eBI⟩ := UC22.uc22p21k_barInf_equiv_of_calC c.mem_calC
  have hspq : IsSpor (Bar2 L ⧸ Subgroup.center (Bar2 L)) s := by
    obtain ⟨eS⟩ := hs
    exact ⟨eBI.symm.trans eS⟩
  have hleBar : CFSG.Open.pRank 3 (⊤ : Subgroup (Bar2 L)) ≤ 2 := by
    rw [pRank_bar2_eq_of_odd Nat.prime_three (by norm_num)]
    exact h2
  have hCov := Inputs1719.k_SporadicCoverThreeRank_holds (Bar2 L) s hq hodd hspq hleBar
  have hpos : 1 ≤ CFSG.Open.pRank 3
      (⊤ : Subgroup (Bar2 L ⧸ Subgroup.center (Bar2 L))) := by
    have : Nontrivial (BarInf L) := by
      have := hq.2.toNontrivial
      exact eBI.toEquiv.nontrivial
    rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) eBI]
    exact Inputs1719.k_SporadicThreeRankPos_holds (BarInf L) s hs
  have hK1 := PartOne.Section8.kSporadicThreeRank_holds
    (Bar2 L ⧸ Subgroup.center (Bar2 L)) s hspq
  rcases (by omega : CFSG.Open.pRank 3
      (⊤ : Subgroup (Bar2 L ⧸ Subgroup.center (Bar2 L))) = 1 ∨
      CFSG.Open.pRank 3 (⊤ : Subgroup (Bar2 L ⧸ Subgroup.center (Bar2 L))) = 2) with h1 | h2'
  · have h1C : CFSG.pRank 3 (⊤ : Subgroup (Bar2 L ⧸ Subgroup.center (Bar2 L))) = 1 := by
      rw [CFSG.Foundations.SteinbergCA.pRank_coe_eq_open_pRank Nat.prime_three]
      exact h1
    exact Or.inr (Or.inl (hK1.1.mpr h1C))
  · have h2C : CFSG.pRank 3 (⊤ : Subgroup (Bar2 L ⧸ Subgroup.center (Bar2 L))) = 2 := by
      rw [CFSG.Foundations.SteinbergCA.pRank_coe_eq_open_pRank Nat.prime_three]
      exact h2'
    rcases hK1.2.mpr h2C with h | h | h | h | h | h | h | h | h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inl (Or.inr (Or.inl h))
    · exact Or.inl (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
    · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))

theorem gap17_18P_holds (D : Data G) (V₀ V : Subgroup G)
    (hKS9 : Inputs1719.K_SporadicNine) (hN1 : Inputs1719.K_SporadicNoncentralThree) :
    Gap17_18P D V₀ V := by
  intro L c h3 hstr
  have hNC : ∀ s : TauCeti.SporadicName, IsSpor (BarInf L) s →
      (s = .J1 ∨ s = .M12 ∨ s = .M22 ∨ s = .HS ∨ s = .Ru ∨ s = .ONan) →
      NoncentralThreeFact L := by
    intro s hs hsl Y _ _ K S hKY hKe
    obtain ⟨e⟩ := hKe
    exact hN1 Y K S s hKY (isSpor_quot_center_of_bar2 c.mem_calC hs e) hsl
  refine ⟨fun h2 => ?_, fun hON hN => ?_⟩
  · have hN : ¬ (L.subgroupOf D.M).Normal := by
      intro hn
      rw [Inputs1719.conjClosure_eq_self_of_normal c.mem_calC.1.le hn] at h3
      omega
    obtain ⟨s, hs, hsix | hfive⟩ := sporadic_cases_of_pRank_le_two D c h2
    · obtain ⟨X, hXM, -, hXp, hXexp, hXnc, hXperm⟩ :=
        exists_permutes_three_of_calC (D := D) c.mem_calC
          (fun Y _ _ K hKn hKq hKodd he hcent hidx S hS => by
            obtain ⟨e⟩ := he
            exact hKS9 Y K S ⟨hKn, hKq, hKodd, hcent, hidx, hS⟩
              ⟨s, hsix, isSpor_quot_center_of_bar2 c.mem_calC hs e⟩)
      exact ⟨X, inP11_of_strongly Nat.prime_three (by norm_num) hstr hXM hXp hXexp hXnc hXperm⟩
    · refine exists_inP11_of_not_normal_of_noncentral D c.mem_calC hstr hN (hNC s hs ?_)
      rcases hfive with h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact exists_inP11_of_not_normal_of_noncentral D c.mem_calC hstr hN
      (hNC .ONan hON (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))

end Certificates

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
