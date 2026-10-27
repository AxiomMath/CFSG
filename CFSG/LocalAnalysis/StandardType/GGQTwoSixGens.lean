module

public import CFSG.LocalAnalysis.StandardType.GGQTwoSixGensRelsData
public import CFSG.LocalAnalysis.StandardType.GGQTwoSixGensGen

public section

namespace CFSG.StandardType.QTwo.SixPoint

open CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary

variable {K : Type} [Field K] [Finite K] [CharP K 2]
  {G : Type} [Group G] {H : Subgroup G}

theorem qTwoSix_gens (hK : Nat.card K = 4) (B : QTwoCanonBlocks K 5 6 H)
    {φ₀ φ₁ φ₂ : Su K 2 1 4 →* G}
    (h₀ : QTwoFourChart B 0 (by norm_num) φ₀) (h₁ : QTwoFourChart B 1 (by norm_num) φ₁)
    (h₂ : QTwoFourChart B 2 (by norm_num) φ₂)
    (a₀₁ : ∀ u : Su K 2 1 3, φ₀ (blockEmb K 2 1 4 3 1 (by norm_num) u) =
      φ₁ (blockEmb K 2 1 4 3 0 (by norm_num) u))
    (a₁₂ : ∀ u : Su K 2 1 3, φ₁ (blockEmb K 2 1 4 3 1 (by norm_num) u) =
      φ₂ (blockEmb K 2 1 4 3 0 (by norm_num) u)) :
    ∃ g : Fin 18 → G, (∀ w ∈ relsP, evalG g w = 1) ∧ (∀ i, g i ∈ H) ∧
      (∀ x ∈ B.blk {0, 1, 2}, x ∈ Subgroup.closure {g 10, g 11}) ∧
      (∀ x ∈ B.blk {3, 4, 5}, x ∈ Subgroup.closure {g 16, g 17}) ∧
      (∀ x ∈ B.blk {0, 1, 2, 3}, x ∈ Subgroup.closure (Set.range g)) ∧
      (∀ x ∈ B.blk {1, 2, 3, 4}, x ∈ Subgroup.closure (Set.range g)) ∧
      (∀ x ∈ B.blk {2, 3, 4, 5}, x ∈ Subgroup.closure (Set.range g)) := by
  classical
  let φ : Fin 3 → Su K 2 1 4 →* G := ![φ₀, φ₁, φ₂]
  have a01 : ∀ u : Su K 2 1 3,
      φ 0 (qTwoSixWin_left u) = φ 1 (qTwoSixWin_right u) := by
    intro u
    exact a₀₁ u
  have a12 : ∀ u : Su K 2 1 3,
      φ 1 (qTwoSixWin_left u) = φ 2 (qTwoSixWin_right u) := by
    intro u
    exact a₁₂ u
  have hφ : ∀ s : Fin 3, QTwoFourChart B s.val (qTwoSixWin_hs s) (φ s) := by
    intro s
    fin_cases s
    · exact h₀
    · exact h₁
    · exact h₂
  let g := qTwoSixWin_g hK φ
  have hmem : ∀ i, g i ∈ B.blk (qTwoSixData_support i) := by
    intro i
    exact qTwoSixWin_g_mem_blk hK a01 a12 hφ i
  have hcomm : ∀ a b : Fin 18,
      Disjoint (qTwoSixData_support a) (qTwoSixData_support b) →
      (qTwoSixData_support a ∪ qTwoSixData_support b).card ≤ 5 → Commute (g a) (g b) := by
    intro a b hd hc
    exact B.commute_of_disjoint (by norm_num) hd hc
      (qTwoSixData_support_card a).1 (by have := (qTwoSixData_support_card a).2; omega)
      (qTwoSixData_support_card b).1 (by have := (qTwoSixData_support_card b).2; omega)
      (g a) (hmem a) (g b) (hmem b)
  have hrel : ∀ w ∈ relsP, evalG g w = 1 :=
    qTwoSixRels_evalG_eq_one_data
      (fun s => blockEmb K 2 1 6 4 s.val (qTwoSixWin_hs s))
      qTwoSixWin_emb_injective (nativeSu hK) (nativeSu_rels hK)
      (qTwoSixWin_lift hK)
      (fun s i hin => qTwoSixWin_lift_eq hK s i (qTwoSixWin_hs s) hin)
      g φ (qTwoSixWin_g_eq hK a01 a12) hcomm
  refine ⟨g, hrel, ?_, ?_⟩
  · intro i
    exact B.blk_le _ (qTwoSixData_support_card i).1
      (by have := (qTwoSixData_support_card i).2; omega) (hmem i)
  · obtain ⟨hend0, hend3⟩ := qTwoSixGensGen_ends hK B hφ g (qTwoSixWin_g_eq hK a01 a12)
    obtain ⟨hfour0, hfour1, hfour2⟩ :=
      qTwoSixGensGen_four_blocks hK B hφ g (qTwoSixWin_g_eq hK a01 a12)
    exact ⟨hend0, hend3, hfour0, hfour1, hfour2⟩

end CFSG.StandardType.QTwo.SixPoint

end
