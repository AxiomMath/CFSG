module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddQ7U3Dick
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndex.U3OddPSL

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.Q7U3

open Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.LieType.Steinberg
  CFSG.BenderSuzuki.MatrixGroups CFSG.AGLEmbeddingD2.McLaughlin.OddIndex

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]

theorem range_embSU_le_of_not_bad (hF : Nat.card F = (p ^ f) ^ 2)
    (hp2 : p ≠ 2) (hq3 : p ^ f % 3 = 1) (hq13 : 13 ≤ p ^ f) {ω : Fˣ} (hω : orderOf ω = 3)
    {W : Subgroup (SU (unitaryInvolution F p f) 3)} (hNW : normA0 hF ω ≤ W)
    {x : SU (unitaryInvolution F p f) 3} (hxW : x ∈ W) (hxz : x * zSU hF = zSU hF * x)
    (hxN : x ∉ normA0 hF ω) : (embSU (unitaryInvolution F p f)).range ≤ W := by
  obtain ⟨ζ, hζ0, hζ⟩ := exists_unitaryInvolution_eq_neg hF
  have hTN := range_tSU_le_normA0 hF hω hq3
  have hTW : (tSU hF).range ≤ W := hTN.trans hNW
  obtain ⟨l, hl, t, ht, rfl⟩ := (mem_centralizer_zSU_iff hF hp2 x).1 hxz
  have hlW : l ∈ W := by
    have : l = (l * t) * t⁻¹ := by group
    rw [this]
    exact W.mul_mem hxW (W.inv_mem (hTW ht))
  have hlN : l ∉ normA0 hF ω := fun h => hxN ((normA0 hF ω).mul_mem h (hTN ht))
  rw [← range_levi hζ0 hζ] at hl
  obtain ⟨w, rfl⟩ := hl
  have hA := card_zpowers_pslMk_diagSL hζ0 hζ hF hω hq3
  have hAH := (normalizer_psl_le_map_comap hζ0 hζ hF hω hq3).trans
    (Subgroup.map_mono (Subgroup.comap_mono hNW))
  have hF0 : Nat.card (fixedSubfield F p f) = p ^ f := card_fixedSubfield hF
  rcases psl2_normalizer_three_eq_or_top hF0 hp2 (by rw [hF0]; exact hq3)
    (by rw [hF0]; exact hq13) hA hAH with hEq | htop
  · exfalso
    apply hlN
    have hmem : pslMk (fixedSubfield F p f) w ∈
        (W.comap (levi hζ0 hζ)).map (pslMk (fixedSubfield F p f)) :=
      ⟨w, Subgroup.mem_comap.2 hlW, rfl⟩
    rw [hEq] at hmem
    exact levi_mem_normA0_of_psl_normalizer hζ0 hζ hF hω hq3 hmem
  · have hcount := card_inf_range_embSU_eq hζ0 hζ hF hp2 W hTW
    rw [htop, Subgroup.card_top, CFSG.Glauberman.Dickson.MaxUp.card_psl2_odd hF0 hp2] at hcount
    have h2 : 2 ∣ p ^ f * ((p ^ f) ^ 2 - 1) := by
      obtain ⟨a, ha⟩ := odd_prime_pow (p := p) (f := f) hp2
      refine Dvd.dvd.mul_left ?_ _
      have h : (p ^ f) ^ 2 = 4 * a * (a + 1) + 1 := by rw [ha]; ring
      have : (p ^ f) ^ 2 - 1 = 4 * a * (a + 1) := by omega
      rw [this]
      exact ⟨2 * a * (a + 1), by ring⟩
    have hge : Nat.card (embSU (unitaryInvolution F p f)).range ≤
        Nat.card (W ⊓ (embSU (unitaryInvolution F p f)).range : Subgroup _) := by
      rw [hcount, card_range_embSU hF, Nat.mul_div_cancel' h2]
    have heq := Subgroup.eq_of_le_of_card_ge (inf_le_right :
      W ⊓ (embSU (unitaryInvolution F p f)).range ≤ (embSU (unitaryInvolution F p f)).range) hge
    rw [← heq]
    exact inf_le_left

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.Q7U3
