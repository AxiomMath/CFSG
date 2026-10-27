module

public import CFSG.LocalAnalysis.StandardType.GGCSRLabels
public import CFSG.LocalAnalysis.StandardType.GGTableBF4Two
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallRanksTri
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallRest
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRefl
public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP8dAct

public section

namespace CFSG.StandardType.FrameRoute

open CFSG.Assembly CFSG.Open CFSG.StandardType

theorem p8d_small_label_exclusion
    {G : Type} [Group G] [Finite G] {Bs K : Subgroup G} {z : G}
    {n : ℕ} (hBs : IsElemAbelian 3 Bs) (hcard : Nat.card Bs = 3 ^ n) (hn : 7 ≤ n) (hz : z ∈ Bs)
    (hz1 : z ≠ 1) (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hker : Bs ⊓ Subgroup.centralizer (K : Set G) = Subgroup.zpowers z)
    (hBstar : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (hK : GGInnerDiagOnLabel (fun _ lab => lab.n = 1 ∧ (lab.tag = .F4 ∨ lab.tag = .twF4der ∨
      lab.tag = .triD4 ∨ lab.tag = .B2der ∨ lab.tag = .G2der)) 3 Bs K) : False := by
  have hK' : GGInnerDiagOnLabel (fun _ lab => (lab.n = 1 ∧ lab.tag = .F4) ∨ (lab.n = 1 ∧
      (lab.tag = .twF4der ∨ lab.tag = .triD4 ∨ lab.tag = .B2der ∨ lab.tag = .G2der))) 3 Bs K := by
    refine largeEvenMarking_mono (fun lab R _ I F θ hP => ?_) hK
    obtain ⟨⟨hn1, ht⟩, hrest⟩ := hP
    refine ⟨?_, hrest⟩
    rcases ht with ht | ht
    · exact Or.inl ⟨hn1, ht⟩
    · exact Or.inr ⟨hn1, ht⟩
  rcases GGInnerDiagOnLabel.elim_or hK' with hF | hO
  · obtain ⟨hperf, lab, _, hraw⟩ := hF
    obtain ⟨R, _, I, Fd, hQ⟩ := CFSG.StandardType.largeEvenRawDatum_exists hraw
    obtain ⟨-, -, -, ⟨⟨hn1, htag⟩, -, -⟩⟩ := hQ
    obtain ⟨tag, rank, m⟩ := lab
    subst htag
    subst hn1
    simp only at hraw
    obtain ⟨F, fieldF, finiteF, hcardF, hQ2⟩ := hraw
    obtain ⟨-, -, θ, -⟩ := hQ2
    have hF2 : Nat.card F = 2 := by simpa using hcardF
    have hchar : CharP F 2 := charP_two_of_card (m := 1) (by rw [hF2, pow_one])
    have h1 := p8dAct_card_range_ggBeta θ hperf hBs hz hz1 hN hker
    have hEA := p8dAct_isElemAbelian_range_ggBeta θ hBs hN
    have h4 := TableBF4Two.card_le_mulAut (K := F) hF2 hEA
    have h7 : (3 : ℕ) ^ 7 ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have h8 : Nat.card (ggBeta K θ hN).range * 3 ≤ 3 ^ 4 * 3 := Nat.mul_le_mul_right 3 h4
    have h9 : (3 : ℕ) ^ 7 ≤ 3 ^ 4 * 3 := by
      calc (3 : ℕ) ^ 7 ≤ 3 ^ n := h7
        _ = Nat.card (ggBeta K θ hN).range * 3 := by rw [← hcard, h1]
        _ ≤ 3 ^ 4 * 3 := h8
    norm_num at h9
  · have hM := largeEvenMarking_and_labelAll (X := ↥K)
      (S := fun lab => lab.n = 1 ∧
        (lab.tag = .twF4der ∨ lab.tag = .triD4 ∨ lab.tag = .B2der ∨ lab.tag = .G2der))
      (P' := fun R _ I _ => ∀ X : Subgroup (MulAut R), (X : Set (MulAut R)) ⊆ I →
        IsElemAbelian 3 X → Nat.card X < 3 ^ 3)
      (fun lab hlab ⟨hn1, ht⟩ => by
        rcases ht with ht | ht | ht | ht
        · exact ggCSR_twF4der hlab ht
        · exact TableBExcSmallRest.largeEvenLabelAll_card_lt_triD4
            (fun _ => TableBExcSmallRanks.ggTriD4ThreeRankInput_holds) Nat.prime_three hlab ht
            (Or.inr (Or.inr (Or.inr ⟨hn1, rfl⟩)))
        · exact ggCSR_B2der hlab ht
        · exact ggCSR_G2der hlab ht)
      (fun lab R _ I F θ hP => hP.1) hO
    obtain ⟨hperf, lab, _, hraw⟩ := hM
    obtain ⟨R, _, I, Fd, hQ⟩ := CFSG.StandardType.largeEvenRawDatum_exists hraw
    obtain ⟨-, -, θ, ⟨⟨-, hBsN, hbs⟩, hbound⟩⟩ := hQ
    have hEA := p8dAct_isElemAbelian_range_ggBeta θ hBs hN
    have hI : ((ggBeta K θ hN).range : Set (MulAut R)) ⊆ I := by
      rintro _ ⟨b, rfl⟩
      exact ggBeta_mem K θ hN hbs b
    have hlt := hbound _ hI hEA
    have h1 := p8dAct_card_range_ggBeta θ hperf hBs hz hz1 hN hker
    have h7 : (3 : ℕ) ^ 7 ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have h27 : Nat.card (ggBeta K θ hN).range < 27 := by simpa using hlt
    have h2187 : 2187 ≤ Nat.card (ggBeta K θ hN).range * 3 := by
      rw [h1, hcard]
      simpa using h7
    omega

end CFSG.StandardType.FrameRoute

end
