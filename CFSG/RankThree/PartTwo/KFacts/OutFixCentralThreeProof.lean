module

public import CFSG.RankThree.PartTwo.KFacts.OutFixCentralThreeTools
import CFSG.RankThree.PartTwo.KFacts.OutFixCentralThreeU43Rank
import CFSG.RankThree.PartTwo.Sec4.Census.WiringInputs
import CFSG.RankThree.Classical2.TwoLocalRankCoprimeQuotient
import CFSG.RankThree.PartTwo.Sec4.Item47CoreOut
import CFSG.RankThree.PartTwo.Sec4.Item47Bridges
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Blueprint.Catalog
public import CFSG.RankThree.PartTwo.Setup

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.ComponentClassification.OuterAutomorphisms (Outer equivalence)
open CFSG.Assembly.RankThreeEven (projSU localRank)
open CFSG.ComponentClassification.CatalogueSchreierAlternating
  (DegreeSix.outer_card_le_four_of_equiv outer_card_dvd_two_of_equiv_outside_six)
open OutFixCentralThree

namespace OutFixCentralThree

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley in
open CFSG.LieType.Ree (ReeTag) in
theorem card_outer_G2_three
    (Y : Type) [Group Y] (hY : Blueprint.ChevalleyExceptionalModel Y .G2 3 1) :
    Nat.card (Outer Y) = 2 := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := Sec4.exists_mulEquiv_adjointGroup_G2 hY
  have : CharP K ReeTag.G2.prime :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_three
      le_rfl hK
  obtain ⟨-, -, ⟨Θ, -, hs, hker⟩, -⟩ := G2_three_exact_automorphism_normal_form le_rfl K hK
  have hC : Nat.card (Outer (adjointGroup Tag.G2 K)) =
      Nat.card (Multiplicative (ZMod (2 * 1))) :=
    Sec4.Item47CoreOut.card_outer_eq_of_ker_eq_inner Θ hs hker
  rw [Nat.card_congr (equivalence e).toEquiv, hC, Nat.card_congr Multiplicative.toAdd,
    Nat.card_zmod]

theorem card_center_quotient_centerThreePrime_of_U43
    {X : Type} [Group X]
    [Finite X] (hS4 : SectionFourHyp X) (hq : IsQuasisimple X) {z : X}
    (hz : z ∈ Subgroup.center X) (hz3 : orderOf z = 3) (f : X ⧸ Subgroup.center X ≃* projSU 4 3 1) :
    Nat.card (Subgroup.center (X ⧸ centerThreePrime X)) = 3 := by
  obtain ⟨hq', ⟨ε⟩, hz'⟩ := quotient_centerThreePrime_facts hq hz
  have hZ3 := isPGroup_center_quotient_centerThreePrime hq
  have hdvd : Nat.card (Subgroup.center (X ⧸ centerThreePrime X)) ∣ 3 ^ 2 :=
    Sec4.Census.coverU43Center _ hq' hZ3 ⟨ε.trans f⟩
  have hne9 : Nat.card (Subgroup.center (X ⧸ centerThreePrime X)) ≠ 9 := by
    intro h9
    have h4 := Sec4.Census.nineCoverU43RankFour _ hq' h9 ⟨ε.trans f⟩
    have hle : localRank 3 (X ⧸ centerThreePrime X) ≤ localRank 3 X :=
      CFSG.RankThree.Classical2.localRank_quotient_le Nat.prime_three (by norm_num) _
        not_three_dvd_card_centerThreePrime
    have h3 := Sec4.Census.SectionFourHyp.localRank_three_le hS4
    omega
  have hne1 : Nat.card (Subgroup.center (X ⧸ centerThreePrime X)) ≠ 1 := by
    intro h1
    have hbot := Subgroup.card_eq_one.mp h1
    have hz1 : (z : X ⧸ centerThreePrime X) = 1 := by
      have := hz'
      rwa [hbot, Subgroup.mem_bot] at this
    have := orderOf_mk_centerThreePrime hz3
    rw [hz1, orderOf_one] at this
    norm_num at this
  obtain ⟨i, hi, hci⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  interval_cases i
  · exact absurd (by rw [hci]; norm_num) hne1
  · rw [hci]; norm_num
  · exact absurd (by rw [hci]; norm_num) hne9

theorem false_of_U43_of_pRank_le
    {X : Type} [Group X] [Finite X] (hS4 : SectionFourHyp X)
    (hq : IsQuasisimple X) (hrk : CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 3) {z : X}
    (hz : z ∈ Subgroup.center X) (hz3 : orderOf z = 3) (f : X ⧸ Subgroup.center X ≃* projSU 4 3 1) :
    False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, ⟨ε⟩, -⟩ := quotient_centerThreePrime_facts hq hz
  have h4 := four_le_pRank_of_threeCoverU43
    (card_center_quotient_centerThreePrime_of_U43 hS4 hq hz hz3 f) (ε.trans f)
  have heq := CFSG.SectionRank.pRank_quotient_eq (p := 3) (centerThreePrime X)
    not_three_dvd_card_centerThreePrime
  omega

end OutFixCentralThree

end CFSG.RankThree.PartTwo.KFacts
