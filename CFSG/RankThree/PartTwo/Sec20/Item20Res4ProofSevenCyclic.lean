module

public import CFSG.RankThree.PartTwo.Sec20.Item20Res4ProofSeven
import CFSG.RankThree.PartTwo.Sec20.Item20Res4ProofSevenStruct
import CFSG.RankThree.PartTwo.Sec18.Components

public section

namespace CFSG.RankThree.PartTwo.Sec20

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late
open CFSG.Assembly.RankThreeEven (projSL)

@[expose] def Step207YCyclic : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M L N : Subgroup G) (c : G) (T : Subgroup G),
    Ctx20One G A M L N c T → T ≤ N →
    ¬ kTwenty M c ⊓ Subgroup.centralizer (zTwenty T : Set G) ≤ N →
    eTwenty M N c T ≠ ⊥ → L ≤ Subgroup.centralizer (eTwenty M N c T : Set G) →
    ∀ x ∈ kTwenty M c, x ∈ Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G) →
      x * c * x⁻¹ ∈ Subgroup.centralizer (fTwenty M N c T : Set G) →
        CFSG.Open.pRank 3
          (normalClosureIn (Subgroup.centralizer (fTwenty M N c T : Set G)) (x * c * x⁻¹)) ≤ 1

@[expose] def KF207Theta : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Y L : Subgroup G), CFSG.IsKGroup ↥Y →
    L ≤ Subgroup.normalizer (Y : Set G) → ⁅L, L⁆ = L →
    Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* projSL 3 (GaloisField 2 2)) →
    CFSG.Open.pRank 3 Y ≤ 1 → ⁅L, Y⁆ ≤ inSubgroup (CFSG.pPrimeCore 3) Y

theorem step207YTheta_core (hK : KF207Theta) {G : Type} [Group G] [Finite G]
    {A M L N : Subgroup G} {c : G} {T : Subgroup G} (hT : Ctx20 G A M L N c T)
    (hLq : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* projSL 3 (GaloisField 2 2))) (hLL : ⁅L, L⁆ = L)
    (hLE : L ≤ Subgroup.centralizer (eTwenty M N c T : Set G)) {x : G}
    (h3 : CFSG.Open.pRank 3
      (normalClosureIn (Subgroup.centralizer (fTwenty M N c T : Set G)) (x * c * x⁻¹)) ≤ 1) :
    ⁅L, normalClosureIn (Subgroup.centralizer (fTwenty M N c T : Set G)) (x * c * x⁻¹)⁆ ≤
      inSubgroup (CFSG.pPrimeCore 3)
        (normalClosureIn (Subgroup.centralizer (fTwenty M N c T : Set G)) (x * c * x⁻¹)) := by
  set F := fTwenty M N c T with hFdef
  set Y := normalClosureIn (Subgroup.centralizer (F : Set G)) (x * c * x⁻¹) with hYdef
  have hYtop : Y ≠ ⊤ := by
    intro htop
    have hA : IsE27 A := isE27_of_mem_partTwoE hT.mem_partTwoE
    have hle := CFSG.RankThreeEvenClassification.Helpers.pRank_mono 3 Nat.prime_three
      (le_top : A ≤ ⊤)
    rw [← htop, hA.pRank_eq] at hle
    omega
  have hKY : CFSG.IsKGroup ↥Y := (hT.toTheoremFourHyp.sectionFourHyp hYtop).kGroup
  have hLY : L ≤ Subgroup.normalizer (Y : Set G) :=
    (hLE.trans (Subgroup.centralizer_le fun z hz => hz.2)).trans
      (le_normalizer_normalClosureIn _ _)
  exact hK G Y L hKY hLY hLL hLq h3

theorem step207YTheta_of_cyclic (h184 : Sec18.Item184_1) (hC : Step207YCyclic)
    (hK : KF207Theta) : Step207YTheta := by
  intro G _ _ A M L N c T hT hTN hCK hE hLE x hxK hxB hcx
  have hLL : ⁅L, L⁆ = L := by
    obtain ⟨H, -, -, hL, -⟩ := hT.one
    rw [hL]
    exact Sec18.commutator_inSubgroup_perfectResidual H
  exact step207YTheta_core hK hT.toCtx20 (nonempty_quotient_of_hyp201One h184 hT.hyp201One) hLL
    hLE (hC G A M L N c T hT hTN hCK hE hLE x hxK hxB hcx)

section Certificates


theorem step207K0Sub_of_YTheta (h1812 : Sec18.Item181_2) (h184 : Sec18.Item184_1)
    (h2031 : Item203One1) (h204 : Item204One) (h2051 : Step2051) (h2053 : Step2053)
    (h189 : Sec18.Item189) (h321 : Sec3.Item321Split) (hY : Step207YTheta) : Step207K0Sub :=
  step207K0Sub_of_theta h1812 h184 h204 h2051 h2053
    (step207Struct_of h2031 h204 h2051 h2053 h189 h321) hY

theorem step207K0Sub_of_cyclic (h1812 : Sec18.Item181_2) (h184 : Sec18.Item184_1)
    (h2031 : Item203One1) (h204 : Item204One) (h2051 : Step2051) (h2053 : Step2053)
    (h189 : Sec18.Item189) (h321 : Sec3.Item321Split) (hC : Step207YCyclic)
    (hK : KF207Theta) : Step207K0Sub :=
  step207K0Sub_of_YTheta h1812 h184 h2031 h204 h2051 h2053 h189 h321
    (step207YTheta_of_cyclic h184 hC hK)

theorem step207K0_of_cyclic (h186 : Sec18.Item186H) (h1812 : Sec18.Item181_2)
    (h184 : Sec18.Item184_1) (h2031 : Item203One1) (h204 : Item204One) (h2051 : Step2051)
    (h2053 : Step2053) (h189 : Sec18.Item189) (h321 : Sec3.Item321Split)
    (hC : Step207YCyclic) (hK : KF207Theta) : Step207K0 :=
  step207K0_of_sub h186
    (step207K0Sub_of_cyclic h1812 h184 h2031 h204 h2051 h2053 h189 h321 hC hK)

end Certificates

end CFSG.RankThree.PartTwo.Sec20
