module

public import CFSG.LocalAnalysis.StandardType.GGSixTCResidualSplit
public import CFSG.LocalAnalysis.StandardType.GGSixTCResidualSkeleton
public import CFSG.LocalAnalysis.StandardType.GGSixCtxKnownSupply

public section

namespace CFSG.StandardType.TCResidual

open CFSG.Assembly CFSG.Blueprint CFSG.Assembly.LowTwoRank

section KnownLie

theorem ggSixTCResidualExcluded_of_facts
    (hfacts : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), commutator ↥L = ⊤ →
      Odd (Nat.card (Subgroup.center ↥L)) →
      LieModel (↥L ⧸ Subgroup.center ↥L) .PSU 6 2 1 →
      (∃ E ≤ L, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 4 ∧
        E ⊓ Subgroup.centralizer (L : Set G) = ⊥) ∧
      (∃ y ∈ L, y ^ 3 = 1 ∧ y ∉ Subgroup.centralizer (L : Set G) ∧
        ∃ s ∈ L, s ≠ 1 ∧ s ^ 2 = 1 ∧ y * s = s * y))
    (hout : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), commutator ↥L = ⊤ →
      LieModel (↥L ⧸ Subgroup.center ↥L) .PSU 6 2 1 →
      ∀ T' : Subgroup G, IsPGroup 2 T' → T' ≤ Subgroup.normalizer (L : Set G) →
        (∀ t ∈ T', ∀ l ∈ L, (∀ g ∈ L, t * g * t⁻¹ = l * g * l⁻¹) →
          t ∈ Subgroup.centralizer (L : Set G)) →
        Nat.card T' ≤ 2 * Nat.card (T' ⊓ Subgroup.centralizer (L : Set G) : Subgroup G)) :
    GGSixTCResidualExcluded := by
  intro G _ _ p B Bs x L D J n f ψ hc hD hodd hcomp hz hA3 hE6 hF hres hB4 hR2
  unfold GGSixTCResidual at hres
  obtain ⟨hp3, -, hmodL, -⟩ := hres
  subst hp3
  have hxB : x ∈ B := hc.sstar.2.1
  have hx1 : x ≠ 1 := hc.sstar.2.2.1
  have hLcomp : IsComponentOf L (Subgroup.centralizer {x}) := hc.sstar.2.2.2.1
  have hBel : IsElemAbelian 3 B := hc.sstar.1.1
  have hx3 : x ^ 3 = 1 := hBel.2 x hxB
  have hrank : LargeEvenTwoLocalRank 3 G ≤ 4 := by
    have heq : LargeEvenTwoLocalRank 3 G = 4 :=
      Nat.pow_right_injective (by norm_num : 2 ≤ 3) (by
        change 3 ^ LargeEvenTwoLocalRank 3 G = 3 ^ 4
        rw [← hc.sstar.1.2.1, hB4])
    omega
  have hBL : B ≤ Subgroup.normalizer (L : Set G) :=
    (ggSixCtx_normalizer_and_innerDiag_on_L hc).1
  have hB0 : ∀ S : Subgroup G, S ≤ L → IsPGroup 2 S →
      B ≤ Subgroup.normalizer (S : Set G) → S = ⊥ := by
    intro S hSL hS2 hSB
    exact hR2 S hS2 (hSL.trans (le_ggG0_left 3 B x L D J)) hSB
  have hxD : x ∈ D := hc.stdSub.1.2.2.2.1
  have hJcomp : IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set G)) :=
    hc.stdSub.1.2.2.2.2.2.1
  have hJL : J ≤ L := hc.j_le_inf.trans inf_le_left
  have hLK : L = ggKd 3 B x L D J x := by
    have hKx : IsComponentOf (ggKd 3 B x L D J x) (Subgroup.centralizer {x}) :=
      hcomp x hxD hx1
    rcases CFSG.LocalAnalysis.ComponentInitial.isComponentOf_eq_or_commute hLcomp hKx with h | h
    · exact h
    · exfalso
      have hJJ : ⁅J, J⁆ ≤ ⁅L, ggKd 3 B x L D J x⁆ :=
        Subgroup.commutator_mono hJL (le_ggKd 3 B x L D J x)
      rw [h] at hJJ
      have hbot : ⁅J, J⁆ = ⊥ := le_bot_iff.mp hJJ
      rw [ggComponent_perfect hJcomp] at hbot
      exact ggComponent_ne_bot hJcomp hbot
  have hodZ : Odd (Nat.card ↥(Subgroup.center ↥L)) := by
    have h := hz x hxD hx1
    rw [← hLK] at h
    exact h
  have hperf : commutator ↥L = ⊤ := hLcomp.2.2.1
  obtain ⟨⟨E, hEL, hEab, hEcard, hEC⟩, hF2⟩ := hfacts G L hperf hodZ hmodL
  have hF1 : ∃ E ≤ L, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 4 := ⟨E, hEL, hEab, hEcard⟩
  have hF1' : ∃ E ≤ L ⊔ Subgroup.zpowers x, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 5 := by
    have hcomm : ∀ e ∈ E, e * x = x * e := fun e he =>
      Subgroup.mem_centralizer_singleton_iff.mp (hLcomp.1 (hEL he))
    have hxE : x ∉ E := by
      intro hxE
      have hxCL : x ∈ Subgroup.centralizer (L : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro l hl
        exact Subgroup.mem_centralizer_singleton_iff.mp (hLcomp.1 hl)
      have hxbot : x ∈ E ⊓ Subgroup.centralizer (L : Set G) := ⟨hxE, hxCL⟩
      rw [hEC] at hxbot
      exact hx1 (Subgroup.mem_bot.mp hxbot)
    obtain ⟨hab, hcard⟩ :=
      isElemAbelian_sup_zpowers_of_card Nat.prime_three hEab hEcard hx3 hxE hcomm
    refine ⟨E ⊔ Subgroup.zpowers x, sup_le_sup_right hEL (Subgroup.zpowers x), hab, ?_⟩
    simpa using hcard
  obtain ⟨T, hTx, hT2, hBT, hne⟩ := hc.stdType.2.1
  exact hne (ggResidual_commutator_eq_bot (x := x) (L := L) (B := B) (T := T)
    hrank hLcomp hBL hB0 hT2 hTx hBT hF1 hF1' hF2 (hout G L hperf hmodL))

end KnownLie

end CFSG.StandardType.TCResidual

end
