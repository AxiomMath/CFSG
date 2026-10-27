module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Fi22Three

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row

open CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic
  CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit

theorem two_pow_fifty_four_le_card_of_cover
    {U : Type} [CommGroup U] [Finite U] [Nontrivial U]
    (hU : ∀ w : U, w * w = 1) {L : Type} [Group L] [Finite L] (ρ : L →* MulAut U)
    (hρ : Function.Injective ρ) (e : (L ⧸ Subgroup.center L) ≃* CFSG.Blueprint.NativeSporadic.Fi22)
    (hZ : Nat.card (Subgroup.center L) = 3) {ζ : L} (hζ : ζ ∈ Subgroup.center L) (hζ1 : ζ ≠ 1)
    (hfix : ∀ w : U, ρ ζ w = w → w = 1) : 2 ^ 54 ≤ Nat.card U := by
  let π : L →* CFSG.Blueprint.NativeSporadic.Fi22 :=
    (e : (L ⧸ Subgroup.center L) →* CFSG.Blueprint.NativeSporadic.Fi22).comp
      (QuotientGroup.mk' (Subgroup.center L))
  have hπs : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : π.ker = Subgroup.center L := by
    ext k
    rw [MonoidHom.mem_ker]
    show e (QuotientGroup.mk k) = 1 ↔ k ∈ Subgroup.center L
    rw [← map_one e, e.injective.eq_iff, QuotientGroup.eq_one_iff]
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hD⟩ := fi22_coverData
  obtain ⟨P₀, P₁, P₂, Q₀, Q₁, Q₂, c, ω, N, r, hωK, hω1, hs⟩ :=
    fi22_cover_struct π hπs hker.le (by rw [hker]; exact hZ) hD
  have hs' := hs.map ρ hρ
  have hωc : ω ∈ Subgroup.center L := by rw [← hker]; exact hωK
  have hζ3 : ζ ^ 3 = 1 := by
    have h1 : (⟨ζ, hζ⟩ : Subgroup.center L) ^ Nat.card (Subgroup.center L) = 1 :=
      pow_card_eq_one'
    rw [hZ] at h1
    exact congrArg Subtype.val h1
  have hord : orderOf ζ = 3 := orderOf_eq_prime hζ3 hζ1
  have hcen : Subgroup.center L = Subgroup.zpowers ζ := by
    symm
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hζ) ?_
    rw [Nat.card_zpowers, hord, hZ]
  have hfix' : ∀ w : U, ρ ω w = w → w = 1 := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hcen ▸ hωc)
    have hk3 : ζ ^ (k % 3) = ω := by
      rw [← hk, ← zpow_mod_orderOf ζ k, hord]
      rfl
    have hmod : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
    rcases hmod with h0 | h1 | h2
    · exact absurd (by rw [← hk3, h0, zpow_zero]) hω1
    · intro w hw
      apply hfix w
      rw [h1, zpow_one] at hk3
      rw [hk3]
      exact hw
    · intro w hw
      apply hfix w
      rw [h2] at hk3
      have hρω : ρ ω = (ρ ζ) ^ (2 : ℕ) := by
        rw [← hk3, show ((2 : ℤ)) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, map_pow]
      have h3 : (ρ ζ) ^ (3 : ℕ) = 1 := by rw [← map_pow, hζ3, map_one]
      have h4 : ((ρ ζ) ^ (2 : ℕ)) w = w := by rw [← hρω]; exact hw
      calc ρ ζ w = ρ ζ (((ρ ζ) ^ (2 : ℕ)) w) := by rw [h4]
        _ = ((ρ ζ) ^ (3 : ℕ)) w := by
            rw [pow_succ' (ρ ζ) 2, MulAut.mul_apply]
        _ = w := by rw [h3]; rfl
  exact card_ge_of_cover hU inferInstance hs' hfix'

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row
