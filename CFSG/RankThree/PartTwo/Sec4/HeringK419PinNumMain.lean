module

public import CFSG.RankThree.PartTwo.Sec4.HeringK419PinFam2
public import CFSG.RankThree.PartTwo.Sec4.HeringK419PinExplicit

public section

namespace CFSG.RankThree.PartTwo.Sec4.HeringPin

open Finset CFSG.Open

@[expose] def NumList46 (M : ℕ) : Prop :=
  (∃ x d : ℕ, 2 ≤ x ∧ ((Odd x ∧ d = 2) ∨ (Even x ∧ d = 1)) ∧ M * d = x * (x ^ 2 - 1)) ∨
  (∃ s g d : ℕ, s.Prime ∧ 1 ≤ g ∧ (s = 2 ∨ (5 ≤ s ∧ g ≤ 2)) ∧ d ∣ 3 ∧
    ((d ∣ s ^ g - 1 ∧ M * d = (s ^ g) ^ 3 * (((s ^ g) ^ 2 - 1) * ((s ^ g) ^ 3 - 1))) ∨
     (d ∣ s ^ g + 1 ∧ M * d = (s ^ g) ^ 3 * (((s ^ g) ^ 2 - 1) * ((s ^ g) ^ 3 + 1))))) ∨
  (∃ s g d : ℕ, s.Prime ∧ 1 ≤ g ∧ (s = 2 ∨ (5 ≤ s ∧ g = 1)) ∧
    ((Even (s ^ g) ∧ d = 1) ∨ (Odd (s ^ g) ∧ d = 2)) ∧
    M * d = (s ^ g) ^ 4 * (((s ^ g) ^ 2 - 1) * ((s ^ g) ^ 4 - 1))) ∨
  (∃ s g d : ℕ, s.Prime ∧ 1 ≤ g ∧ (s = 2 ∨ (5 ≤ s ∧ g = 1)) ∧ d ∣ 4 ∧ d ∣ s ^ g + 1 ∧
    M * d = (s ^ g) ^ 6 * (((s ^ g) ^ 2 - 1) * ((s ^ g) ^ 3 + 1) * ((s ^ g) ^ 4 - 1))) ∨
  (∃ s d : ℕ, s.Prime ∧ 5 ≤ s ∧ d ∣ 4 ∧ d ∣ s - 1 ∧
    M * d = s ^ 6 * ((s ^ 2 - 1) * (s ^ 3 - 1) * (s ^ 4 - 1))) ∨
  (∃ s g : ℕ, s.Prime ∧ 1 ≤ g ∧ (s = 2 ∨ (5 ≤ s ∧ g = 1)) ∧ M = ordG2 (s ^ g)) ∨
  (∃ f : ℕ, 1 ≤ f ∧ M = ordTrialityD4 (2 ^ f)) ∨
  (∃ f : ℕ, 1 ≤ f ∧ M = ordSuzuki (2 ^ f)) ∨
  (∃ f : ℕ, 1 ≤ f ∧ M = ordTwistedF4 (2 ^ f)) ∨
  (∃ D ∈ ExplicitD, M ∣ D)

theorem not_numList46 {M p e : ℕ} (hp : p.Prime) (he : 2 ≤ e) (hX : XOrd M p e) :
    ¬ NumList46 M := by
  have hI := xinfo_of_xord hp he hX
  rintro (⟨x, d, hx, hd, h⟩ | ⟨s, g, d, hs, hg, hc, hd3, hf⟩ | ⟨s, g, d, hs, hg, hc, hd, h⟩ |
    ⟨s, g, d, hs, hg, hc, hd4, hdq, h⟩ | ⟨s, d, hs, h5, hd4, hdq, h⟩ | ⟨s, g, hs, hg, hc, h⟩ |
    ⟨f, hf, h⟩ | ⟨f, hf, h⟩ | ⟨f, hf, h⟩ | ⟨D, hD, hMD⟩)
  · exact not_psl2 hI hx hd h
  · exact not_sl3 hI hs hg hc hd3 hf
  · exact not_sp4 hI hs hg hc hd h
  · exact not_u4 hI hs hg hc hd4 hdq h
  · exact not_l4 hI hs h5 hd4 hdq h
  · exact not_g2 hI hs hg hc h
  · exact not_d4 hI hf h
  · exact not_sz hI hf h
  · exact not_f4t hI hf h
  · exact explicit_false hX hp he hD hMD

end CFSG.RankThree.PartTwo.Sec4.HeringPin
