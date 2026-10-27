module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Good
import CFSG.LocalAnalysis.GLTheoremB.ComponentTools
import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
import CFSG.GroupTheory.PCore.PrimeSetCore

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7

open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

@[expose] def InvolutionCentralizerHasPElementOutside (p : ℕ) {X : Type*} [Group X]
    (N : Subgroup X) : Prop :=
  ∀ A : Subgroup X, A ≤ N → CFSG.Open.IsElemAbelian p A → Nat.card A = p ^ 2 →
    ∀ t : X, t ∈ N → orderOf t = 2 → (∀ a ∈ A, a * t = t * a) →
      ∃ c ∈ CFSG.generalizedFitting X, c * t = t * c ∧ IsPGroup p (Subgroup.zpowers c) ∧ c ∉ N

@[expose] def AbelianPSubgroupLeFStar (p : ℕ) {X : Type*} [Group X] (N : Subgroup X) : Prop :=
  ∀ B : Subgroup X, B ≤ N → IsPGroup p B → (∀ a ∈ B, ∀ b ∈ B, a * b = b * a) →
    p ^ 3 ≤ Nat.card B → B ≤ CFSG.generalizedFitting X

@[expose] def StronglyEmbeddedFiveZ : Prop :=
  ∀ p : ℕ, p.Prime → 5 ≤ p →
    ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X → CFSG.pPrimeCore p X = ⊥ →
      2 ≤ CFSG.Open.pRank p (⊤ : Subgroup X) → ∀ N : Subgroup X, IsStronglyPEmbedded p N →
        (InvolutionCentralizerHasPElementOutside p N ∧ AbelianPSubgroupLeFStar p N) ∨
          CoverHasLargeTwoLocal ↥(CFSG.generalizedFitting X)

theorem involutionCentralizerHasPElementOutside_of_single {p : ℕ} (hp : p.Prime) {X : Type*}
    [Group X] {N : Subgroup X}
    (h : ∀ x t : X, x ∈ N → t ∈ N → x ≠ 1 → IsPGroup p (Subgroup.zpowers x) → orderOf t = 2 →
      x * t = t * x →
      ∃ c ∈ CFSG.generalizedFitting X, c * t = t * c ∧ IsPGroup p (Subgroup.zpowers c) ∧ c ∉ N) :
    InvolutionCentralizerHasPElementOutside p N := by
  intro A hAN hA hAc t htN ht2 htA
  have h1 : 1 < Nat.card A := by
    rw [hAc]
    exact Nat.one_lt_pow (by norm_num) hp.one_lt
  haveI : Finite A := Nat.finite_of_card_ne_zero (by omega)
  haveI : Nontrivial A := Finite.one_lt_card_iff_nontrivial.mp h1
  obtain ⟨⟨x, hxA⟩, hx1⟩ := exists_ne (1 : A)
  have hx1' : x ≠ 1 := fun h => hx1 (Subtype.ext h)
  have hxp : x ^ p = 1 := hA.2 x hxA
  have hxo : orderOf x = p := by
    rcases (Nat.dvd_prime hp).mp (orderOf_dvd_of_pow_eq_one hxp) with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hx1'
    · exact h
  have hxP : IsPGroup p (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hxo, pow_one])
  exact h x t (hAN hxA) htN hx1' hxP ht2 (htA x hxA)

variable {G : Type} [Group G] [Finite G]

namespace Sec7Core4

theorem goodZ_of_kIDExcluded (k : Sec7Core4 G) (h5 : 5 ≤ k.p) (hno : KIDExcluded k)
    {H : Subgroup G} (hH : Config k H) (hSEZ : StronglyEmbeddedFiveZ) (h75 : Step75 k) :
    InvolutionCentralizerHasPElementOutside k.p
        (((H ⊓ k.M).subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore k.p ↥H))) ∧
      AbelianPSubgroupLeFStar k.p
        (((H ⊓ k.M).subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore k.p ↥H))) := by
  have hp : k.p.Prime := k.prime
  haveI : Fact k.p.Prime := ⟨hp⟩
  let K₀ : Subgroup ↥H := CFSG.pPrimeCore k.p ↥H
  let Nbar : Subgroup (↥H ⧸ K₀) := ((H ⊓ k.M).subgroupOf H).map (QuotientGroup.mk' K₀)
  have hKH : CFSG.Open.IsKGroup ↥H :=
    CFSG.LocalAnalysis.GLTheoremB.isKGroup_of_isKProper k.standing.kProper hH.ne_top
  have hKQ : CFSG.Open.IsKGroup (↥H ⧸ K₀) :=
    CFSG.LocalAnalysis.GLTheoremB.isKGroup_quotient' hKH K₀
  have hO : CFSG.pPrimeCore k.p (↥H ⧸ K₀) = ⊥ := CFSG.pPrimeCore_quotient_eq_bot hp
  have hrank : 2 ≤ CFSG.Open.pRank k.p (⊤ : Subgroup (↥H ⧸ K₀)) :=
    k.two_le_pRank_quotient_pPrimeCore hH
  have hN : IsStronglyPEmbedded k.p Nbar := k.isStronglyPEmbedded_map_quotient_pPrimeCore hH
  rcases hSEZ k.p hp h5 (↥H ⧸ K₀) hKQ hO hrank Nbar hN with hgood | hbad
  · exact hgood
  · exact absurd hbad (hno H hH h75)

end Sec7Core4

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
