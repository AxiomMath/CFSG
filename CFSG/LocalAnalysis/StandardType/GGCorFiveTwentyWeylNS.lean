module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyQSplit

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGCorFiveTwentyWeylDomNS {G : Type} [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G)
    (x : G) (L D J : Subgroup G) : Prop :=
  GGReflGenerated p (ggAutomizer L Bs) ∧ GGInnerDiagOnLabel GGLabPhiOneTwo p Bs L ∧
    ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
      GGReflGenerated p (ggAutomizer K Bs) ∧ GGInnerDiagOnLabel GGLabPhiOneTwo p Bs K

section Dom

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}

theorem ggCorFiveTwentyWeylDom_iff_ns :
    GGCorFiveTwentyWeylDom p B Bs x L D J ↔
      GGScalarsPmOne Bs ∧ GGCorFiveTwentyWeylDomNS p B Bs x L D J := Iff.rfl

theorem GGCorFiveTwentyWeylDom.toNS (h : GGCorFiveTwentyWeylDom p B Bs x L D J) :
    GGCorFiveTwentyWeylDomNS p B Bs x L D J := h.2

end Dom

@[expose] def GGCorFiveTwentyQFourWeylNSInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGCorFiveTwentyHyp p B Bs x L D J → GGInnerDiagOnLabel GGLabQFour p Bs L →
      GGNbrLabelsOk p B Bs x D J → GGCorFiveTwentyWeylDomNS p B Bs x L D J →
        Subgroup.normalizer (Bs : Set G) ≤ Subgroup.normalizer (ggG0 p B x L D J : Set G)

@[expose] def GGCorFiveTwentyQFourNonWeylNSInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGCorFiveTwentyHyp p B Bs x L D J → GGInnerDiagOnLabel GGLabQFour p Bs L →
      GGNbrLabelsOk p B Bs x D J → ¬ GGCorFiveTwentyWeylDomNS p B Bs x L D J →
        Subgroup.normalizer (Bs : Set G) ≤ Subgroup.normalizer (ggG0 p B x L D J : Set G)

theorem ggScalarsPmOne_of_exp_three {G : Type} [Group G] {Bs : Subgroup G}
    (h : ∀ b ∈ Bs, b ^ 3 = 1) : GGScalarsPmOne Bs := by
  intro φ _ ⟨k, hk⟩
  refine MulEquiv.ext fun b => ?_
  have hb3 : b ^ 3 = 1 := Subtype.ext (by simpa using h b b.2)
  have hkb : φ b = b ^ (k % 3) := by rw [hk, pow_eq_pow_mod k hb3]
  have hcases : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rw [pow_two, MulAut.mul_apply, MulAut.one_apply]
  rcases hcases with h0 | h1 | h2
  · have h1' : φ b = 1 := by rw [hkb, h0, pow_zero]
    have hb : b = 1 := φ.injective (by rw [h1', map_one])
    rw [hb, map_one, map_one]
  · have h1' : φ b = b := by rw [hkb, h1, pow_one]
    rw [h1', h1']
  · rw [hkb, h2, map_pow, hkb, h2, ← pow_mul]
    have h4 : (2 * 2 : ℕ) = 3 + 1 := rfl
    rw [h4, pow_succ, hb3, one_mul]

theorem ggScalarsPmOne_of_prime_three {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J)
    (hp3 : p = 3) : GGScalarsPmOne Bs := by
  obtain ⟨hp, hBs, -, -, -⟩ := hcfg.tableB_facts
  subst hp3
  exact ggScalarsPmOne_of_exp_three fun b hb => hBs.2 b hb

theorem five_le_of_not_scalarsPmOne {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J)
    (hs : ¬ GGScalarsPmOne Bs) : 5 ≤ p := by
  obtain ⟨hp, -, -, -, -⟩ := hcfg.tableB_facts
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  have hp3 : p ≠ 3 := fun h => hs (ggScalarsPmOne_of_prime_three hcfg h)
  have hp4 : p ≠ 4 := by
    rintro rfl
    norm_num at hp
  have := hp.two_le
  omega

@[expose] def GGCorFiveTwentyQFourScalarFailInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGCorFiveTwentyHyp p B Bs x L D J → GGInnerDiagOnLabel GGLabQFour p Bs L →
      GGNbrLabelsOk p B Bs x D J → GGCorFiveTwentyWeylDomNS p B Bs x L D J →
        ¬ GGScalarsPmOne Bs → 5 ≤ p →
          Subgroup.normalizer (Bs : Set G) ≤ Subgroup.normalizer (ggG0 p B x L D J : Set G)

theorem ggCorFiveTwentyQFourInput_of_weylNS (hN : GGCorFiveTwentyQFourNonWeylNSInput)
    (hW : GGCorFiveTwentyQFourWeylNSInput) : GGCorFiveTwentyQFourInput := by
  intro G _ _ p B Bs x L D J hH hq hN'
  by_cases hD : GGCorFiveTwentyWeylDomNS p B Bs x L D J
  · exact hW G p B Bs x L D J hH hq hN' hD
  · exact hN G p B Bs x L D J hH hq hN' hD

theorem ggCorFiveTwentyQFourNonWeylNSInput_of_nonWeyl (h : GGCorFiveTwentyQFourNonWeylInput) :
    GGCorFiveTwentyQFourNonWeylNSInput :=
  fun G _ _ p B Bs x L D J hH hq hN hD =>
    h G p B Bs x L D J hH hq hN (fun hW => hD hW.2)

theorem ggCorFiveTwentyQFourNonWeylNSInput_of_aggregate (h : GGCorFiveTwentyInput) :
    GGCorFiveTwentyQFourNonWeylNSInput :=
  fun G _ _ p B Bs x L D J hH _ _ _ =>
    h G p B Bs x L D J hH.1 hH.2.1 hH.2.2.1 hH.2.2.2.1 hH.2.2.2.2

theorem ggCorFiveTwentyQFourNonWeylInput_iff :
    GGCorFiveTwentyQFourNonWeylInput ↔
      GGCorFiveTwentyQFourNonWeylNSInput ∧ GGCorFiveTwentyQFourScalarFailInput := by
  constructor
  · intro h
    exact ⟨ggCorFiveTwentyQFourNonWeylNSInput_of_nonWeyl h,
      fun G _ _ p B Bs x L D J hH hq hN hD hs _ =>
        h G p B Bs x L D J hH hq hN (fun hW => hs hW.1)⟩
  · rintro ⟨hNS, hS⟩ G _ _ p B Bs x L D J hH hq hN hD
    by_cases hDNS : GGCorFiveTwentyWeylDomNS p B Bs x L D J
    · have hs : ¬ GGScalarsPmOne Bs := fun hs => hD ⟨hs, hDNS⟩
      exact hS G p B Bs x L D J hH hq hN hDNS hs (five_le_of_not_scalarsPmOne hH.1 hs)
    · exact hNS G p B Bs x L D J hH hq hN hDNS

theorem ggCorFiveTwentyQFourWeylNSInput_of_weyl (hW : GGCorFiveTwentyQFourWeylInput)
    (hS : GGCorFiveTwentyQFourScalarFailInput) : GGCorFiveTwentyQFourWeylNSInput := by
  intro G _ _ p B Bs x L D J hH hq hN hD
  by_cases hs : GGScalarsPmOne Bs
  · exact hW G p B Bs x L D J hH hq hN ⟨hs, hD⟩
  · exact hS G p B Bs x L D J hH hq hN hD hs (five_le_of_not_scalarsPmOne hH.1 hs)

theorem ggCorFiveTwentyQFourScalarFailInput_of_nonWeyl (h : GGCorFiveTwentyQFourNonWeylInput) :
    GGCorFiveTwentyQFourScalarFailInput :=
  (ggCorFiveTwentyQFourNonWeylInput_iff.mp h).2

end CFSG.StandardType

end
