module

public import CFSG.LocalAnalysis.StandardType.GGTwE6DeltaThreeDefs
import CFSG.LocalAnalysis.StandardType.GGTwE6DeltaThreeReduce
import CFSG.LocalAnalysis.StandardType.GGTwE6DD2Cover

public section

namespace CFSG.StandardType.TwE6D3

section Center


variable {K : Type} [Field K] [Finite K] {n : ℕ} {L' : Type} [Group L'] [Finite L']
  {ψ : L' →* TwE6Delta.RecipeR K n} {A As : Subgroup (MulAut L')}

theorem Cfg.card_center_dvd (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) (h : Cfg ψ A As) :
    Nat.card (Subgroup.center L') = 1 ∨ Nat.card (Subgroup.center L') = 3 := by
  obtain ⟨hexp, hcyc⟩ := TwE6DD2.center_facts hn hK h.surj h.ker_le h.perfect
  have hodd := h.odd_center
  have hcop : (Nat.card (Subgroup.center L')).Coprime (4 ^ Nat.card L') := by
    have h2 : (Nat.card (Subgroup.center L')).Coprime 2 := Nat.coprime_two_right.mpr hodd
    have h4 : (Nat.card (Subgroup.center L')).Coprime 4 := by
      simpa using Nat.Coprime.pow_right 2 h2
    exact Nat.Coprime.pow_right _ h4
  have hcube : ∀ z ∈ Subgroup.center L', z ^ 3 = 1 := by
    intro z hz
    obtain ⟨z', hz'⟩ := (Nat.Coprime.pow_left_bijective hcop).2 ⟨z, hz⟩
    have h1 := hexp z' z'.2
    have h2 : (z' : L') ^ 4 ^ Nat.card L' = z := congrArg Subtype.val hz'
    rwa [h2] at h1
  rcases Subgroup.bot_or_exists_ne_one (Subgroup.center L') with hbot | ⟨z₀, hz₀, hz₀1⟩
  · left
    rw [hbot]
    exact Subgroup.card_bot
  · right
    have ho : orderOf z₀ = 3 := by
      have hd : orderOf z₀ ∣ 3 := orderOf_dvd_of_pow_eq_one (hcube z₀ hz₀)
      rcases (Nat.dvd_prime Nat.prime_three).1 hd with h1 | h3
      · exact absurd (orderOf_eq_one_iff.1 h1) hz₀1
      · exact h3
    have hle : Subgroup.center L' ≤ Subgroup.zpowers z₀ := fun z hz =>
      hcyc z₀ hz₀ z hz ho (hcube z hz)
    have h1 : Nat.card (Subgroup.center L') ≤ Nat.card (Subgroup.zpowers z₀) :=
      Subgroup.card_le_of_le hle
    rw [Nat.card_zpowers, ho] at h1
    have h2 : 3 ∣ Nat.card (Subgroup.center L') := ho ▸ Subgroup.orderOf_dvd_natCard _ hz₀
    have h3 : 0 < Nat.card (Subgroup.center L') := Nat.card_pos
    omega

end Center

end CFSG.StandardType.TwE6D3
