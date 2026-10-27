module

public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanPrimDefs
import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1OfPrim

public section

namespace CFSG.StandardType

open scoped MatrixGroups

theorem ggSecFivePhanRankOne_of_card_six
    (hRk1 : GGSecFiveRk1PhanInput) {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hns : ¬ GGSplitLie p L) {ι : Type}
    {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e)
    (hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3) {X : Subgroup G} (hX : X = L ∨ X ∈ 𝒦)
    {r : MulAut ↥Bs} (hrA : r ∈ ggAutomizer X Bs) (hrC : r ∈ ggCoxRefl M e)
    (h6 : Nat.card (ggRankOneIn X Bs r) = 6) :
    p = 3 ∧ ∃ (F : Type) (_ : Field F) (_ : Finite F) (θ : SL(2, F) →* G),
      CharP F 2 ∧ Nat.card F = 2 ∧ Function.Injective θ ∧ θ.range = ggRankOneIn X Bs r := by
  obtain ⟨F, hF, hFfin, θ, hchar, hθinj, hθrange, -, hsplit, hnsplit, -⟩ :=
    hRk1 G p B Bs x L D J 𝒦 hcfg hns ι M e hpres hle3 X hX r hrA hrC
  have hcardSL : Nat.card (ggRankOneIn X Bs r) = Nat.card SL(2, F) := by
    rw [← hθrange]
    exact Nat.card_congr (MonoidHom.ofInjective hθinj).toEquiv.symm
  have hF2 : Nat.card F = 2 := by
    have hq2 : 2 ≤ Nat.card F := Finite.one_lt_card
    rw [hcardSL, ggSL2_card F] at h6
    by_contra hne
    have h3 : 3 ≤ Nat.card F := by omega
    have h9 : 9 ≤ Nat.card F ^ 2 := by
      simpa using Nat.pow_le_pow_left h3 2
    have h8 : 8 ≤ Nat.card F ^ 2 - 1 := by omega
    have h24 : 24 ≤ Nat.card F * (Nat.card F ^ 2 - 1) := by
      calc (24 : ℕ) = 3 * 8 := by norm_num
        _ ≤ Nat.card F * (Nat.card F ^ 2 - 1) := Nat.mul_le_mul h3 h8
    omega
  have hp : p.Prime := (ggRouteCfg_prime hcfg).1
  have hp3 : p = 3 := by
    by_cases hsp : GGSplitLie p X
    · have h1 : p ∣ Nat.card F - 1 := hsplit hsp
      rw [hF2] at h1
      norm_num at h1
      exact absurd h1 hp.ne_one
    · have h1 : p ∣ Nat.card F + 1 := hnsplit hsp
      rw [hF2] at h1
      norm_num at h1
      exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h1
  exact ⟨hp3, F, hF, hFfin, θ, hchar, hF2, hθinj, hθrange⟩

end CFSG.StandardType

end
