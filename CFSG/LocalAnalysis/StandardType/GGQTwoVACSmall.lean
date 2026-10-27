module

public import CFSG.LocalAnalysis.StandardType.GGQTwoVACSplit
public import CFSG.LocalAnalysis.StandardType.GGRootGenSmallRankQFour

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem ggQ2VACLabSmall_not_largeEvenMarking
    {X : Type} [Group X] :
    ¬ LargeEvenMarking X (fun lab R _ I _ _ => GGQ2VACLabSmall 3 lab ∧
      ∃ E : Subgroup (MulAut R), (E : Set (MulAut R)) ⊆ I ∧ IsElemAbelian 3 E ∧
        3 ^ 3 ≤ Nat.card E) := by
  intro h
  obtain ⟨hX, lab, hlab, hraw⟩ := h
  have hS : GGQ2VACLabSmall 3 lab := by
    obtain ⟨R, _, I, F, hQ⟩ := largeEvenRawDatum_exists hraw
    obtain ⟨-, -, _, hP⟩ := hQ
    exact hP.1
  have mk : ∀ Q : LargeEvenLabel → Prop, Q lab →
      LargeEvenMarking X (fun lab' R _ I _ _ => Q lab' ∧
        ∃ E : Subgroup (MulAut R), (E : Set (MulAut R)) ⊆ I ∧ IsElemAbelian 3 E ∧
          3 ^ 3 ≤ Nat.card E) := by
    intro Q hQlab
    refine ⟨hX, lab, hlab, largeEvenRawDatum_mono ?_ hraw⟩
    rintro R _ I F hQ
    obtain ⟨hs, hna, θ, hP⟩ := hQ
    exact ⟨hs, hna, θ, hQlab, hP.2⟩
  rcases hS.2 with h | h | h | h | h | h | h
  · exact (ggInndiag_pRank_le_two_B2der (X := X) Nat.prime_three (by norm_num))
      (mk (fun lab' => lab'.tag = .B2der) h)
  · exact (ggInndiag_pRank_le_two_G2der (X := X) Nat.prime_three (by norm_num))
      (mk (fun lab' => lab'.tag = .G2der) h)
  · exact (ggInndiag_pRank_le_two_twF4der (X := X) Nat.prime_three (by norm_num))
      (mk (fun lab' => lab'.tag = .twF4der) h)
  · have hn : lab.n = 1 := by
      have h1 : 1 ≤ lab.n := hlab.1
      have h2 : lab.n < 2 := hS.1
      omega
    exact (ggInndiag_pRank_le_two_triD4 (X := X) Nat.prime_three)
      (mk (fun lab' => lab'.tag = .triD4 ∧
        (3 ∣ 2 ^ lab'.n - 1 ∨ 3 ∣ 2 ^ lab'.n + 1)) ⟨h, Or.inr (by rw [hn]; norm_num)⟩)
  · exact (ggInndiag_pRank_le_two_G2 (X := X) Nat.prime_three (by norm_num))
      (mk (fun lab' => lab'.tag = .G2) h)
  · exact (ggInndiag_pRank_le_two_twB2 (X := X) Nat.prime_three (by norm_num))
      (mk (fun lab' => lab'.tag = .twB2) h)
  · have h2 : lab.n < 2 := hS.1
    have h3 := hlab
    simp only [LargeEvenInLambda2, h] at h3
    obtain ⟨-, -, -, h4⟩ := h3
    omega

theorem ggQTwoGuardFailsOn_small :
    GGQTwoGuardFailsOn GGQ2VACLabSmall := by
  intro G _ _ p B Bs x L D J hS hp3 hL
  cases hp3
  exact absurd (ggInnerDiagOnLabel_L_pRank_ge_three (S := GGQ2VACLabSmall) hS.1.1 hL)
    (ggQ2VACLabSmall_not_largeEvenMarking (X := ↥L))

end CFSG.StandardType

end
