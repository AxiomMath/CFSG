module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6ThreeTwo
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRefl
public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP8dAct

public section

namespace CFSG.StandardType.FrameRoute

open CFSG.Assembly CFSG.Open CFSG.StandardType CFSG.Blueprint.Chevalley

theorem p10g_E6_ambient
    {G : Type} [Group G] [Finite G] {Bs K : Subgroup G} {z : G} {n : ℕ}
    (hBs : IsElemAbelian 3 Bs) (hcard : Nat.card Bs = 3 ^ n) (hn : 7 ≤ n) (hz : z ∈ Bs)
    (hz1 : z ≠ 1) (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hker : Bs ⊓ Subgroup.centralizer (K : Set G) = Subgroup.zpowers z)
    (hBstar : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (hK : GGInnerDiagOnLabel (fun _ lab => lab.tag = .E6 ∧ lab.n = 1) 3 Bs K) : False := by
  obtain ⟨hperf, lab, _, hraw⟩ := hK
  obtain ⟨R, _, I, Fd, hQ⟩ := CFSG.StandardType.largeEvenRawDatum_exists hraw
  obtain ⟨-, -, -, ⟨⟨htag, hn1⟩, -, -⟩⟩ := hQ
  obtain ⟨tag, rank, m⟩ := lab
  subst htag
  subst hn1
  simp only at hraw
  obtain ⟨F, fieldF, finiteF, hcardF, hQ2⟩ := hraw
  obtain ⟨-, -, θ, -⟩ := hQ2
  have hF2 : Nat.card F = 2 := by simpa using hcardF
  have h1 := p8dAct_card_range_ggBeta θ hperf hBs hz hz1 hN hker
  have hEA := p8dAct_isElemAbelian_range_ggBeta θ hBs hN
  have h5 := TableBExc.E6Three.card_le_of_isElemAbelian_aut_E6_two hF2 hEA
  have h7 : (3 : ℕ) ^ 7 ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have h8 : Nat.card (ggBeta K θ hN).range * 3 ≤ 3 ^ 5 * 3 := Nat.mul_le_mul_right 3 h5
  have h9 : (3 : ℕ) ^ 7 ≤ 3 ^ 5 * 3 := by
    calc (3 : ℕ) ^ 7 ≤ 3 ^ n := h7
      _ = Nat.card (ggBeta K θ hN).range * 3 := by rw [← hcard, h1]
      _ ≤ 3 ^ 5 * 3 := h8
  norm_num at h9

end CFSG.StandardType.FrameRoute

end
